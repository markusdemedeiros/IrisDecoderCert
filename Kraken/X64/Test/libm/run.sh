#!/bin/bash
# Builds and runs bands_test.c (see README.md). Exit status: that of the test.
set -eu
D=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
OUT=$(mktemp -d)
trap 'rm -rf "$OUT"' EXIT
${CC:-cc} -O2 -Wall -msse4.2 -ffp-contract=off "$D/bands_test.c" -o "$OUT/bands_test" -lm
"$OUT/bands_test"
