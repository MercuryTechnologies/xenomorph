build: xenomorph.cabal
	cabal build

xenomorph.cabal: package.yaml
	hpack

test: xenomorph.cabal
	cabal test
