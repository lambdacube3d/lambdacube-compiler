# lambdacube-compiler

[![Build Status](https://travis-ci.org/lambdacube3d/lambdacube-compiler.svg?branch=master)](https://travis-ci.org/lambdacube3d/lambdacube-compiler)
[![Gitter chat](https://badges.gitter.im/lambdacube3d/lambdacube3d.png)](https://gitter.im/LambdaCube-3D/Lobby)

Compiler for LambdaCube 3D, a Haskell-like purely functional domain specific language for programming the GPU (graphics processing unit).

See: [Language Specification](http://lambdacube3d.com/lang-specification)

## Installation

1. Install Haskell [Stack](http://www.haskellstack.org) by following it's simple [install manual](https://docs.haskellstack.org/en/stable/README/#how-to-install).
2. Checkout the this repository then run the following commands.
```
stack setup
stack build
```
3. Run the lambdacube-compiler cli.
```
stack exec lc -- -h
```

## Tutorials and Examples

- [Getting started](http://lambdacube3d.com/getting-started)
- [Workshop material](https://github.com/csabahruska/lambdacube-workshop)

## Hacking notes

If you are hacking on the compiler, run the test suite to check the changes:

```
stack exec lambdacube-compiler-test-suite
```
