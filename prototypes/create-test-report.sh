#! /bin/sh

CABAL_NAME=lambdacube-compiler

HPC_DIR=dist/hpc/${CABAL_NAME}
HPC_REPO_DIR=$HPC_DIR

TEST_DIR=src/UnitTest
TIX=runtests.tix

hpc report ${TIX} --hpcdir=${HPC_DIR} --xml-output > ${HPC_REPO_DIR}/result.xml
hpc markup ${TIX} --hpcdir=${HPC_DIR} --destdir=${HPC_REPO_DIR}
