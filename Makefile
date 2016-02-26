.PHONY: all
all:
	cabal install

LCDIR=~/.cabal/share/x86_64-linux-ghc-7.10.3/lambdacube-compiler-0.5.0.0/lc

repl:
	cd test && ghci -Wall -fno-warn-name-shadowing -fno-warn-unused-matches -fno-warn-missing-signatures -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns -fno-warn-type-defaults -i../src -i../dist/build/autogen runTests.hs

copylc:
	cp lc/*.lc $(LCDIR)

coverage:
	./run-test-suite.sh --coverage

profile:
	./run-test-suite.sh --profile

docker-profile:
	docker run --rm -it -v `pwd`:/root/source/lambdacube-compiler lambdacube3d/lambdacube3d /bin/sh -c "/root/source/lambdacube-compiler/travis/profile.sh"

hlint:
	hlint -h tool/HLint.hs src test tool
