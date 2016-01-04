#!/bin/bash -e

if [ "$1" == "--profile" ] ; then
  shift
  cabal clean
  cabal sandbox delete
  cabal sandbox init
  cabal install --only-dependencies --enable-library-profiling --enable-executable-profiling --constraint="indentation -trifecta"
  cabal configure --flags "profiling" --enable-library-profiling --enable-executable-profiling
  cabal build
  set +e
  cabal run lambdacube-compiler-test-suite -- -r $@ +RTS -p
  RESULT=`echo $?`
  ./create-test-report.sh
  rm lambdacube-compiler-test-suite.tix
  cabal sandbox delete
  cabal clean
  exit $RESULT
else
  set +e
  cabal install --only-dependencies -j1
  cabal run lambdacube-compiler-test-suite -- -r $@
  RESULT=`echo $?`
  ./create-test-report.sh
  rm lambdacube-compiler-test-suite.tix
  exit $RESULT
fi
