#!/bin/bash -e

UNIT_TEST_PARAMS="--quickcheck-max-size 30 --quickcheck-tests 100"

if [ "$1" == "--profile" ] ; then
  shift
  stack build --profile --flag lambdacube-compiler:testsuite --flag lambdacube-compiler:profiling --flag lambdacube-compiler:-cli -j3
  set +e
  RESULT_UNITTESTS=0
  stack exec lambdacube-compiler-test-suite -- -r -iperformance -i.ignore $@ +RTS -p
  RESULT_TESTS=`echo $?`
elif [ "$1" == "--coverage" ] ; then
  shift
  set +e
  stack build --flag lambdacube-compiler:coverage --flag lambdacube-compiler:alltest -j3
  stack exec lambdacube-compiler-unit-tests -- $UNIT_TEST_PARAMS
  RESULT_UNITTESTS=`echo $?`
  stack exec lambdacube-compiler-coverage-test-suite -- -iperformance -i.ignore -r $@
  RESULT_TESTS=`echo $?`
  ./create-test-report.sh
  rm lambdacube-compiler-coverage-test-suite.tix
else
  set +e
  stack build --flag lambdacube-compiler:alltest -j3
  stack exec lambdacube-compiler-unit-tests -- $UNIT_TEST_PARAMS
  RESULT_UNITTESTS=`echo $?`
  stack exec lambdacube-compiler-test-suite -- -iperformance -i.ignore -r $@
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
