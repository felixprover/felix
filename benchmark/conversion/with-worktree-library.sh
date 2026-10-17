#!/bin/sh
set -eu

repository=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd -P)
library_root=$(CDPATH= cd -- "$repository/library" && pwd -P)

export NAPROCHE_LIB=$library_root
exec "$@"
