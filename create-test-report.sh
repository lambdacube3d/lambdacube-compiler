#! /bin/sh

CABAL_NAME=lambdacube-compiler

HPC_DIR=dist/hpc/${CABAL_NAME}
HPC_REPO_DIR=$HPC_DIR

TEST_DIR=src/UnitTest
TIX=lambdacube-compiler-test-suite.tix

hpc markup ${TIX} --hpcdir=${HPC_DIR} --destdir=${HPC_REPO_DIR}
hpc report ${TIX} --hpcdir=${HPC_DIR} --per-module
