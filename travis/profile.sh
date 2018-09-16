#!/bin/bash -ex

#cd /root/source/lambdacube-compiler
./run-test-suite.sh --profile
head -n 50 lambdacube-compiler-test-suite.prof
