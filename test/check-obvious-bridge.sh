#!/bin/sh
set -eu

repository=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repository"
temporary_directory=$(mktemp -d "${TMPDIR:-/tmp}/felix-obvious-bridge.XXXXXX")
trap 'rm -rf "$temporary_directory"' EXIT HUP INT TERM

# Compile the private service and its narrow boundary fixture as home modules.
# This exercises real source without exporting scope or certificate constructors
# from the installed library. Core, proof construction and replay use the library.
stack exec -- ghc -v0 -Wall -i -i"$temporary_directory" \
    -odir "$temporary_directory" -hidir "$temporary_directory" \
    -XImportQualifiedPost -XBlockArguments -XDeriveFunctor -XDeriveGeneric \
    -XFlexibleContexts -XFlexibleInstances -XGADTs -XGeneralizedNewtypeDeriving \
    -XInstanceSigs -XLambdaCase -XNoImplicitPrelude -XOverloadedStrings \
    -XPatternSynonyms -XScopedTypeVariables -XTypeFamilies -XTypeOperators \
    -package felix -package tasty -package tasty-hunit \
    "$repository/source/Felix/Checking/Elimination.hs" \
    "$repository/source/Felix/Checking/Kernel/Conversion/Policy.hs" \
    "$repository/source/Felix/Checking/Obvious/Conversion.hs" \
    "$repository/source/Felix/Checking/Obvious/Template.hs" \
    "$repository/source/Felix/Checking/Obvious/LogicalView.hs" \
    "$repository/source/Felix/Checking/Obvious/Search.hs" \
    "$repository/source/Felix/Checking/Obvious/Equality.hs" \
    "$repository/source/Felix/Checking/Obvious/Match.hs" \
    "$repository/source/Felix/Checking/Obvious/Refutation.hs" \
    "$repository/source/Felix/Checking/Obvious/Choice.hs" \
    "$repository/source/Felix/Checking/Obvious/Driver.hs" \
    "$repository/test/obvious-bridge/ChoiceChecks.hs" \
    "$repository/test/Felix/Test/Support/GlobalTyping.hs" \
    "$repository/test/obvious-bridge/CatalogueChecks.hs" \
    "$repository/test/obvious-bridge/MatcherChecks.hs" \
    "$repository/test/obvious-bridge/ExtensionalityChecks.hs" \
    "$repository/test/obvious-bridge/SharedSyntaxChecks.hs" \
    "$repository/test/obvious-bridge/EqualityChecks.hs" \
    "$repository/test/obvious-bridge/EndpointChecks.hs" \
    "$repository/test/obvious-bridge/Main.hs" \
    -o "$temporary_directory/obvious-bridge"
"$temporary_directory/obvious-bridge" -j1 "$@"
