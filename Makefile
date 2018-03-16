default: hpack
	cabal new-build all

hpack:
	(cd zsyntax-core ; hpack)
	(cd zsyntax-client ; hpack)
