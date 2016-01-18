.PHONY: all
all:
	cabal install --constraint="indentation -trifecta"

repl:
	cd test && ghci -i../src runTests.hs

coverage:
	./run-test-suite.sh --coverage

profile:
	./run-test-suite.sh --profile
