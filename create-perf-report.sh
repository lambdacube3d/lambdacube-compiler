#! /bin/sh

lambdacube-compiler-test-suite --overall-time performance +RTS -tcurrent.log --machine-readable
echo ""
lambdacube-compiler-performance-report $@
echo ""
