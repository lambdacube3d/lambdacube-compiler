#!/bin/bash -e

if [ "$1" == "--profile" ] ; then
  shift
  cabal clean
  cabal sandbox delete
  cabal sandbox init
  cabal install --only-dependencies --enable-library-profiling --enable-executable-profiling --constraint="indentation -trifecta"
  cabal configure --flags "profiling" --enable-library-profiling --enable-executable-profiling
  cabal build
  cabal run lambdacube-compiler-test-suite -- $@ +RTS -p
  ./create-test-report.sh
  rm lambdacube-compiler-test-suite.tix
  cabal sandbox delete
  cabal clean
else
  cabal run lambdacube-compiler-test-suite -- $@
  ./create-test-report.sh
  rm lambdacube-compiler-test-suite.tix
fi
