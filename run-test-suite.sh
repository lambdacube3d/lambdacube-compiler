#!/bin/bash -e

if [ "$1" == "--profile" ] ; then
  shift
  cabal clean
  cabal sandbox delete
  cabal sandbox init
  git clone https://github.com/lambdacube3d/lambdacube-ir /tmp/ir
  cabal sandbox add-source /tmp/ir/lambdacube-ir.haskell
  cabal install --only-dependencies --enable-library-profiling --enable-executable-profiling --constraint="indentation -trifecta"
  cabal configure --flags "profiling onlytestsuite" --enable-library-profiling --enable-executable-profiling
  cabal build
  set +e
  RESULT_UNITTESTS=0
  cabal run lambdacube-compiler-test-suite -- -r $@ +RTS -p
  RESULT_TESTS=`echo $?`
  cabal sandbox delete
  cabal clean
  rm -rf /tmp/ir
elif [ "$1" == "--coverage" ] ; then
  shift
  set +e
  cabal install --only-dependencies -j1
  cabal configure --flags "coverage"
  cabal run lambdacube-compiler-unit-tests
  RESULT_UNITTESTS=`echo $?`
  cabal run lambdacube-compiler-coverage-test-suite -- -r $@
  RESULT_TESTS=`echo $?`
  ./create-test-report.sh
  rm lambdacube-compiler-coverage-test-suite.tix
else
  set +e
  cabal install --only-dependencies -j1
  cabal run lambdacube-compiler-unit-tests
  RESULT_UNITTESTS=`echo $?`
  cabal run lambdacube-compiler-test-suite -- -r $@
  RESULT_TESTS=`echo $?`
fi

if [[ $RESULT_UNITTESTS -ne 0 ]]; then
  echo "***************************"
  echo "* Unit tests are failing. *"
  echo "***************************"
fi

if [[ $RESULT_TESTS -ne 0 ]]; then
  echo "*******************************"
  echo "* Compiler tests are failing. *"
  echo "*******************************"
fi

exit $((RESULT_TESTS + RESULT_UNITTESTS))
