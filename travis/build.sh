#!/bin/bash -e

#cd /root/source/lambdacube-compiler
#cabal check
./run-test-suite.sh --coverage
# TODO
#cabal sdist
#SRC_TGZ=$(cabal info . | awk '{print $2;exit}').tar.gz && (cd dist && cabal install --force-reinstalls "$SRC_TGZ")
