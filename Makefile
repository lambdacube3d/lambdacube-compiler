.PHONY: all
all:
	cabal install --constraint="indentation -trifecta"

repl:
	cd test && ghci -Wall -fno-warn-name-shadowing -fno-warn-unused-matches -fno-warn-missing-signatures -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns -fno-warn-type-defaults -i../src runTests.hs

coverage:
	./run-test-suite.sh --coverage

profile:
	./run-test-suite.sh --profile

hlint:
	hlint -h tool/HLint.hs src test tool
