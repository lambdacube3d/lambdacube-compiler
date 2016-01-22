#!/bin/bash -e

ghc-pkg list

cd /root/source/lambdacube-compiler
cabal check
./run-test-suite.sh --coverage
cabal sdist
SRC_TGZ=$(cabal info . | awk '{print $2;exit}').tar.gz && (cd dist && cabal install --force-reinstalls "$SRC_TGZ")
