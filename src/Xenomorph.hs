{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImportQualifiedPost #-}

module Xenomorph
  ( Parser,
    runParser,
    pElement,
    pElementMaybe,
    pElements,
    pName,
    pAttr,
    pAttrRead,
    pAttrReadInt,
    pAttrReadMaybeInt,
    pAttrBool,
    pAttrs,
    pChildren,
    parseChildren,
    pText,
    pWithText,
    pTextInt,
    fromRawXml,
    parseXML,
  )
where

import Prelude

import Control.Applicative (Alternative(..))
import Data.Maybe (mapMaybe)
import Control.Monad (MonadFail(..), join)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as BC
import Data.ByteString.Unsafe qualified as BU
import Data.HashMap.Strict qualified as Map
import Data.List qualified as List
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder as TBuilder
import Data.Vector.Unboxed ((!))
import HTMLEntities.Decoder (htmlEncodedText)
import Text.Read
import Xeno.DOM qualified as Xeno
import Xeno.DOM.Internal qualified as Xeno

data ParseState
  = ParseDocument ![Xeno.Node]
  | ParseElement
      {-# UNPACK #-} !Xeno.Node
      ![Xeno.Node]

-- | A fast XML parser built on top of Xeno
newtype Parser a = Parser {unParser :: ParseState -> Either String (ParseState, a)}

-- | Run a parser over a document containing some nodes.
runParser :: Parser a -> [Xeno.Node] -> Either String a
runParser (Parser f) elems =
  snd <$> f (ParseDocument elems)

-- | Run a parser directly against some raw XML
parseXML :: BS.ByteString -> Parser a -> Either String a
parseXML rawXML parser = fromRawXml rawXML >>= runParser parser . pure
{-# INLINE parseXML #-}

evalParser :: Parser a -> ParseState -> Either String a
evalParser (Parser f) !st = snd <$> f st
{-# INLINE evalParser #-}

instance Functor Parser where
  fmap f (Parser g) = Parser $ \node -> do
    (n, a) <- g node
    pure (n, f a)

instance Applicative Parser where
  pure a = Parser $ \n -> Right (n, a)
  (Parser f) <*> (Parser g) = Parser $ \node -> do
    (node', f') <- f node
    (node'', a) <- g node'
    pure (node'', f' a)

instance Monad Parser where
  return = pure
  (Parser f) >>= g = Parser $ \node -> do
    (node', a) <- f node
    unParser (g a) node'

instance MonadFail Parser where
  fail err = Parser $ \_ -> Left err

instance Alternative Parser where
  empty = fail "empty"
  (Parser f) <|> (Parser g) = Parser $ \node ->
    case f node of
      Left _ -> g node
      Right val -> Right val

-- | Parser an element with the name @elementName@ using the subParser
-- @subParser@. This consumes the current node from the parse state.
pElement :: BS.ByteString -> Parser a -> Parser a
pElement elementName subParser = Parser $ \parseState -> do
  case parseState of
    ParseElement thisNode (child : children)
      | Xeno.name child == elementName ->
          case unParser subParser (ParseElement child (Xeno.children child)) of
            Left err -> Left err
            Right (_, val) -> Right (ParseElement thisNode children, val)
      | otherwise ->
          Left $
            "pElement: no element "
              <> BC.unpack elementName
              <> " at this node "
              <> (BC.unpack $ Xeno.name thisNode)
              <> " next node is "
              <> (BC.unpack $ Xeno.name child)
    ParseElement thisNode [] ->
      Left $
        "pElement: No remaining children in "
          <> BC.unpack (Xeno.name thisNode)
          <> " when looking for "
          <> BC.unpack elementName
          <> "\nnode:\n"
          <> show thisNode
    ParseDocument (thisNode : rest)
      | Xeno.name thisNode == elementName ->
          case unParser subParser (ParseElement thisNode (Xeno.children thisNode)) of
            Left err -> Left err
            Right (_, val) -> Right (ParseDocument rest, val)
      | otherwise ->
          Left $
            "pElement: Element named "
              <> BC.unpack elementName
              <> " is not the next node, it is "
              <> BC.unpack (Xeno.name thisNode)
    ParseDocument [] ->
      Left $ "pElement: Cannot get an element out of an empty document, when searching for " <> BC.unpack elementName

-- | Parse all of the elements named @elementName@ using @subParser@
-- and return a list of the results. This parser fails if the
-- sub-parser fails for any of the elements in the list. This consumes
-- all of the elements from the parse state. Note that this only works
-- for contiguous elements, so for example calling @pElements "foo"
-- pAttrReadInt@ on some XML:
--
-- @
--   <foo id="1"/>
--   <foo id="2"/>
--   <bar id="1"/>
--   <foo id="3"/>
-- @
--
-- Would return @[1,2]@ and the parse state would be pointing at the
-- @bar@ node. Similarly if we have:
--
-- @
--   <bar id="1" />
--   <foo id="2" />
--   <foo id="3" />
-- @
--
-- Then we would return @[]@ and the parse state would still be
-- pointing at @bar@.
--
-- Also note that this function will return an empty list
-- if the node node has no children, or no children with the given
-- name (but see
-- 'Mercury.OFAC.SanctionsList.Parser.ParseHelpers.atLeastOne' for a
-- utility function to ensure you get at least one result.
pElements :: BS.ByteString -> Parser a -> Parser [a]
pElements elementName subParser =
  let getParser p [] = Right (p, [])
      getParser parsers allNodes@(node : nodes)
        | Xeno.name node == elementName =
            case evalParser subParser $ ParseElement node (Xeno.children node) of
              Left err -> Left err
              Right parsed -> do
                (parsers', rest) <- getParser parsers nodes
                pure (parsed : parsers', rest)
        | otherwise = Right (parsers, allNodes)
   in Parser $
        \case
          ParseDocument children ->
            case getParser [] children of
              Left err -> Left err
              Right (val, rest) -> Right (ParseDocument rest, val)
          ParseElement n children ->
            case getParser [] children of
              Left err -> Left err
              Right (val, rest) -> Right (ParseElement n rest, val)

-- | Parse an element if it exists, but otherwise return Nothing. This
-- will still fail if the element does exist and the sub-parser fails.
pElementMaybe :: BS.ByteString -> Parser a -> Parser (Maybe a)
pElementMaybe elementName subParser = Parser $ \parseState -> do
  case parseState of
    ParseElement thisNode (child : children)
      | Xeno.name child == elementName ->
          case unParser subParser (ParseElement child (Xeno.children child)) of
            Left err -> Left err
            Right (_, val) -> Right (ParseElement thisNode children, Just val)
      | otherwise -> Right (parseState, Nothing)
    ParseDocument (thisNode : rest)
      | Xeno.name thisNode == elementName ->
          case unParser subParser (ParseElement thisNode (Xeno.children thisNode)) of
            Left err -> Left err
            Right (_, val) -> Right (ParseDocument rest, Just val)
    _otherwise ->
      Right (parseState, Nothing)

-- | Get the name of the current element. Fails if we are at the top
-- of the document and have not yet selected a node.
pName :: Parser T.Text
pName = Parser $ \parseState ->
  case parseState of
    ParseDocument _ ->
      Left "Cannot parse a document without a selected node"
    ParseElement node _ ->
      Right (parseState, TE.decodeUtf8 $ Xeno.name node)

-- | Get an attribute as a text value. Fails if we are at the top of
-- the document or if no attribute exists.
pAttr :: BS.ByteString -> Parser T.Text
pAttr attrName =
  Parser $ \parseState ->
    case parseState of
      ParseDocument _ ->
        Left "Cannot get an attribute without a selected node"
      ParseElement node _nodes ->
        let attrs = Xeno.attributes node
         in case List.find (\(k, _v) -> k == attrName) attrs of
              Nothing ->
                Left $ "No attribute " <> BC.unpack attrName <> " in " <> BC.unpack (Xeno.name node)
              Just (_k, v) ->
                Right (parseState, TE.decodeUtf8 v)

{-# INLINE pAttrRaw' #-}
pAttrRaw' :: BS.ByteString -> ParseState -> Either String BS.ByteString
pAttrRaw' keyName parseState =
  case unsafeWithAttribute id keyName parseState of
    Nothing -> Left $ "No attribute found: " <> BC.unpack keyName
    Just val -> Right val

{-# INLINE bytestringToUnquotedStrictText #-}
bytestringToUnquotedStrictText :: BS.ByteString -> T.Text
bytestringToUnquotedStrictText = TL.toStrict . TBuilder.toLazyText . htmlEncodedText . TE.decodeUtf8

{-# INLINE bytestringToUnquotedString #-}
bytestringToUnquotedString :: BS.ByteString -> String
bytestringToUnquotedString = TL.unpack . TBuilder.toLazyText . htmlEncodedText . TE.decodeUtf8

-- | Try to get an attribute from the current node and parse it's
-- value using 'readMaybe'. Fails if the read fails. Note that this
-- function is far less efficient than 'pAttrReadInt' or 'pAttrBool'
-- for the common case of numeric and boolean keys, so prefer those if
-- possible.
pAttrRead :: Read a => BS.ByteString -> Parser a
pAttrRead attrName = Parser $ \parseState -> do
  attrVal <- pAttrRaw' attrName parseState
  case readMaybe (bytestringToUnquotedString attrVal) of
    Nothing -> Left $ "cannot read attribute: " <> BC.unpack attrName
    Just parsed -> Right (parseState, parsed)
{-# INLINE pAttrRead #-}

-- | Efficiently read a numeric attribute value from the selected
-- element.
pAttrReadInt :: BS.ByteString -> Parser Int
pAttrReadInt attrName = Parser $ \parseState ->
  case unsafeIntAttribute attrName parseState of
    Nothing -> Left $ "cannot convert attribute to Int: " <> BC.unpack attrName
    Just parsedInt -> Right (parseState, parsedInt)
{-# INLINE pAttrReadInt #-}

-- | Try to read an optional integer attribute. Note that this will
-- return Nothing if the attribute is missing _or_ if the value is
-- unparsable.
pAttrReadMaybeInt :: BS.ByteString -> Parser (Maybe Int)
pAttrReadMaybeInt attrName = Parser $ \parseState ->
  let val = unsafeIntAttribute attrName parseState
   in Right (parseState, val)
{-# INLINE pAttrReadMaybeInt #-}

-- | Try to read an attribute whose value should be the literal string
-- @true@ or @false@. Case sensitive and only works with lower-case
-- values.
pAttrBool :: BS.ByteString -> Parser Bool
pAttrBool attrName = Parser $ \parseState -> do
  case join (unsafeWithAttribute p attrName parseState) of
    Nothing -> Left $ "cannot convert attribute to Bool: " <> BC.unpack attrName
    Just t -> Right (parseState, t)
  where
    p "true" = Just True
    p "false" = Just False
    p _ = Nothing
{-# INLINE pAttrBool #-}

-- | Return the set of attributes for the current element as a hash
-- map.
pAttrs :: Parser (Map.HashMap BS.ByteString T.Text)
pAttrs = Parser $ \parseState ->
  case parseState of
    ParseDocument _ ->
      Left "Cannot get an attribute without a selected node"
    ParseElement node _nodes ->
      let attrMap = Map.fromList [(k, TE.decodeUtf8 v) | (k, v) <- Xeno.attributes node]
       in Right (parseState, attrMap)

-- | Get all of the children of the current node. This omits text nodes.
pChildren :: Parser [Xeno.Node]
pChildren = Parser $
  \case
    ParseDocument nodes ->
      Right (ParseDocument [], nodes)
    ParseElement node nodes ->
      Right (ParseElement node [], nodes)

-- | Run a parser over the children of the current node. This is
-- functionally similar to 'pElements' but does not check the name of
-- the element. You should use this function if you want to parse a
-- heterogeneous set of nodes. It may also be slightly more efficient
-- if the only children of the current node all are the same element
-- type.
parseChildren :: Parser a -> Parser [a]
parseChildren childParser = Parser $ \parseState ->
  let (newState, nodes) =
        case parseState of
          ParseDocument nodes' -> (ParseDocument [], nodes')
          ParseElement node nodes' -> (ParseElement node [], nodes')
   in do
        results <- traverse (\n -> evalParser childParser $ ParseDocument [n]) nodes
        pure (newState, results)

-- | Extract the value of a text element as an unquoted text
-- string. This evaluates HTML codes like @&amp;@ and turns them into
-- normal values, like @&@. This is generally the behavior that you
-- want, but the conversion can be very expensive, so if you are going
-- to parse the value yourself, use 'pWithText' or 'pTextInt' instead
-- to avoid this conversion.
pText :: Parser T.Text
pText = Parser $ \parseState ->
  case parseState of
    ParseDocument _ ->
      Left "Cannot get text at the top level of the document"
    ParseElement node _nodes ->
      let nodeText n =
            case n of
              Xeno.Element _ -> Nothing
              Xeno.Text t -> Just $ bytestringToUnquotedStrictText t
              Xeno.CData t -> Just $ bytestringToUnquotedStrictText t
          contents = mapMaybe nodeText (Xeno.contents node)
       in Right (parseState, T.unwords contents)

-- | Run a parse function on the raw unquoted value inside of a text
-- element. This is much more efficient than calling 'pText' if you
-- don't need the actual rendered text value.
pWithText :: (BS.ByteString -> Either String a) -> Parser a
pWithText f = Parser $ \parseState ->
  case unsafeWithText f parseState of
    Nothing ->
      Left "Cannot get a numeric text value out of the node"
    Just result -> (parseState,) <$> result

-- | An even more efficient version of 'pText' specialized for parsing
-- integer fields.
pTextInt :: Parser Int
pTextInt = Parser $ \parseState ->
  case join (unsafeWithText BC.readInt parseState) of
    Nothing ->
      Left "Cannot get a numeric text value out of the node"
    Just (parsedInt, _) ->
      Right (parseState, parsedInt)

-- | Parse a bytestring and turn it into a Xeno node.
fromRawXml :: BS.ByteString -> Either String Xeno.Node
fromRawXml !rawXml =
  case Xeno.parse rawXml of
    Left err -> Left (show err)
    Right node -> Right node

-- The 'unsafe*' family of functions are all manually specialized
-- implementations of internal 'Xeno' functions. These particular
-- specialized implementations allowed us to realize some major
-- performance gains in both artificial benchmarking and in real world
-- testing.

-- A note about the copied/derived functions, and licensing:
--
-- The Xeno code is under the BSD3 license, which is not a permissive
-- license and is not copyleft. The terms of the BSD3 license allow us
-- to use modify and use this code in precisely this way. We may
-- redistribute the code or binraries, with or without modifications,
-- so long as we retain the original copyright notice. It does not
-- require that we re-license any of our own code, or place any
-- further obligations on us. Furthermore, using code internally is
-- not redistributing, so as long as we're not giving someone the
-- mercury codebase or a compiled binary, we have no particular
-- obligation under the BSD3 license.
--
-- Should we, for some unexpected reason, choose to distribute the
-- source code or binaries, we should include the notice below:
--
-- Copyright (c) 2021, Mercury Technologies
-- Copyright (c) 2016-2017, Chris Done
--
-- Redistributions in binary form must reproduce the above copyright
-- notice, this list of conditions and the following disclaimer in the
-- documentation and/or other materials provided with the
-- distribution.
--
-- Neither the name of Xeno nor the names of its contributors may be
-- used to endorse or promote products derived from this software
-- without specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
-- "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
-- LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
-- FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL CHRIS
-- DONE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
-- EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
-- PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
-- PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
-- OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
-- (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
-- USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH
-- DAMAGE.

-- | This is a specialized implementation of 'Xeno.contents' that only
-- considers the first text node. In practice it provides us with a
-- noticeable performance benefit over calling 'Xeno.contents' and
-- then pattern matching on the returned values.
unsafeWithText :: (BS.ByteString -> a) -> ParseState -> Maybe a
unsafeWithText f (ParseElement (Xeno.Node str start offsets) _) = collect firstChild
  where
    collect i
      | i < endBoundary =
          case offsets ! i of
            0x00 -> collect (offsets ! (i + 4))
            0x01 -> Just . f $ substring str (offsets ! (i + 1)) (offsets ! (i + 2))
            0x03 -> collect (i + 3)
            _ -> Nothing
      | otherwise = Nothing
    firstChild = go (start + 5)
      where
        go i
          | i < endBoundary =
              case offsets ! i of
                0x02 -> go (i + 5)
                _ -> i
          | otherwise = i
    endBoundary = offsets ! (start + 4)
unsafeWithText _ _ = Nothing

-- | Extract a value out of a node, given a key. This allows us to
-- skip any intermediate constructions and avoid traversing the entire
-- set of attributes.
unsafeWithAttribute :: (BS.ByteString -> a) -> BS.ByteString -> ParseState -> Maybe a
unsafeWithAttribute f !target (ParseElement (Xeno.Node str start offsets) _) = collect (start + 5)
  where
    collect i
      | i < endBoundary =
          let attr = substring str (offsets ! (i + 1)) (offsets ! (i + 2))
           in case offsets ! i of
                0x02
                  | target == attr ->
                      Just . f $ substring str (offsets ! (i + 3)) (offsets ! (i + 4))
                  | otherwise ->
                      collect (i + 5)
                _ -> Nothing
      | otherwise = Nothing
    endBoundary = offsets ! (start + 4)
unsafeWithAttribute _f _target _ = Nothing

-- | Highly efficient specialization for getting an integer key
-- attribute out of a given node. Nearly every single node that we
-- parse in the sanctions list has an integer 'ID' attribute, and this
-- saves us a lot of time over the course of parsing the entire
-- document.
unsafeIntAttribute :: BS.ByteString -> ParseState -> Maybe Int
unsafeIntAttribute !target (ParseElement (Xeno.Node str start offsets) _) = collect (start + 5)
  where
    collect i
      | i < endBoundary =
          let attr = substring str (offsets ! (i + 1)) (offsets ! (i + 2))
           in case offsets ! i of
                0x02
                  | target == attr ->
                      (fmap fst . BC.readInt) $ substring str (offsets ! (i + 3)) (offsets ! (i + 4))
                  | otherwise ->
                      collect (i + 5)
                _ -> Nothing
      | otherwise = Nothing
    endBoundary = offsets ! (start + 4)
unsafeIntAttribute _target _ = Nothing

substring :: BS.ByteString -> Int -> Int -> BS.ByteString
substring str start len = BU.unsafeTake len (BU.unsafeDrop start str)
{-# INLINE substring #-}


