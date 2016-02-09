.PHONY: all
all:
	cabal install --constraint="indentation -trifecta"

LCDIR=~/.cabal/share/x86_64-linux-ghc-7.10.2/lambdacube-compiler-0.5.0.0/lc

repl:
	cp lc/*.lc $(LCDIR)
	cd test && ghci -Wall -fno-warn-name-shadowing -fno-warn-unused-matches -fno-warn-missing-signatures -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns -fno-warn-type-defaults -i../src -i../dist/build/autogen runTests.hs

coverage:
	./run-test-suite.sh --coverage

profile:
	./run-test-suite.sh --profile

docker-profile:
	docker run --rm -it -v `pwd`:/root/source/lambdacube-compiler lambdacube3d/lambdacube3d /bin/sh -c "/root/source/lambdacube-compiler/travis/profile.sh"

hlint:
	hlint -h tool/HLint.hs src test tool
