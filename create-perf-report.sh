#! /bin/sh

lambdacube-compiler-test-suite --overall-time performance +RTS -tcurrent.log --machine-readable
lambdacube-compiler-performance-report $@