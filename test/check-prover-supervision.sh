#!/bin/sh
set -eu

repository=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository"
stack test --no-run-tests >/dev/null
temporary_directory=$(mktemp -d "${TMPDIR:-/tmp}/felix-prover-supervision.XXXXXX")
trap 'rm -rf "$temporary_directory"' EXIT HUP INT TERM

# The normal test suite covers the non-threaded RTS. Link the same prover
# fixtures with the threaded RTS to exercise the production waiting path too.
stack exec -- ghc -v0 -O2 -threaded -rtsopts -Wall -i -itest -itest-support \
    -odir "$temporary_directory" -hidir "$temporary_directory" \
    -XImportQualifiedPost -XBlockArguments -XDeriveFunctor -XDeriveGeneric \
    -XFlexibleContexts -XFlexibleInstances -XGADTs -XGeneralizedNewtypeDeriving \
    -XInstanceSigs -XLambdaCase -XNoImplicitPrelude -XOverloadedStrings \
    -XPatternSynonyms -XScopedTypeVariables -XTypeFamilies -XTypeOperators \
    -package felix -package stm -package tasty -package tasty-hunit \
    "$repository/source/Felix/Provers/Timer.hs" \
    "$repository/test/prover-supervision/TimerTests.hs" \
    "$repository/test/prover-supervision/Main.hs" \
    -o "$temporary_directory/prover-supervision"
"$temporary_directory/prover-supervision" -j1 "$@" +RTS -N4 -RTS
