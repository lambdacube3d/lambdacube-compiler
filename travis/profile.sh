#!/bin/bash -e

cd /root/source/lambdacube-compiler
./run-test-suite.sh --profile
cat lambdacube-compiler-coverage-test-suite.prof
