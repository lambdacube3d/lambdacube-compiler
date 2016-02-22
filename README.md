# lambdacube-compiler

[![Build Status](https://travis-ci.org/lambdacube3d/lambdacube-compiler.svg)](https://travis-ci.org/lambdacube3d/lambdacube-compiler)

Compiler for LambdaCube 3D, a Haskell-like purely functional domain specific language for programming the GPU (graphics processing unit).

See: [Language Specification](http://lambdacube3d.com/lang-specification)

## Installation

Use `make` or use `cabal install`.

## Hacking notes

If you are hacking on the compiler, you may be have a faster repl with ghci. Use the following commands:

    make repl

or:

    cd test
    ghci -i../src runTests.hs
