.PHONY: all
all:
	cabal install --constraint="indentation -trifecta"

repl:
	cd test && ghci -i../src runTests.hs
