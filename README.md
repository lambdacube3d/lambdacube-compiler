# lambdacube-compiler

[![Build Status](https://travis-ci.org/lambdacube3d/lambdacube-compiler.svg)](https://travis-ci.org/lambdacube3d/lambdacube-compiler)

## Installation

Use `cabal install --constraint="indentation -trifecta"` to avoid to install unnecessary trifecta dependency.

## Hacking notes

If you are hacking on the compiler, you may be have a faster repl with ghci. Use the following commands:

    make repl

or:

    cd test
    ghci -i../src runTests.hs
