#! /bin/sh

cabal test --show-details=streaming
./create-test-report.sh
rm runtests.tix
