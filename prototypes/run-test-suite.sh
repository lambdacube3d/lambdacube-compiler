#! /bin/sh

cabal run lambdacube-compiler-test-suite $@
./create-test-report.sh
rm lambdacube-compiler-test-suite.tix
