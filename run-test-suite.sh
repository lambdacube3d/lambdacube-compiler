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
  cabal test --show-details=streaming
  RESULT_UNITTESTS=`echo $?`
  cabal run lambdacube-compiler-test-suite -- -r $@ +RTS -p
  RESULT_TESTS=`echo $?`
  ./create-test-report.sh
  rm lambdacube-compiler-test-suite.tix
  cabal sandbox delete
  cabal clean
  exit $((RESULT_TESTS + RESULT_UNITTESTS))
else
  set +e
  cabal install --only-dependencies -j1
  cabal test --show-details=streaming
  RESULT_UNITTESTS=`echo $?`
  cabal run lambdacube-compiler-test-suite -- -r $@
  RESULT_TESTS=`echo $?`
  ./create-test-report.sh
  rm lambdacube-compiler-test-suite.tix
  exit $((RESULT_TESTS + RESULT_UNITTESTS))
fi
