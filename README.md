# lambdacube-compiler

[![Build Status](https://travis-ci.org/lambdacube3d/lambdacube-compiler.svg)](https://travis-ci.org/lambdacube3d/lambdacube-compiler)

## Installation

Use `cabal install --constraint="indentation -trifecta"` to avoid to install unnecessary trifecta dependency.

## Hacking notes

If you are hacking on the compiler it is faster to run the tests without recompiling the library. Use the following commands:

    cd test
    ghci -i../src runTests.hs

