#!/bin/bash
# Regenerates the ff_aac_sbr_apply proof files from this directory into a scratch dir and
# requires them to equal the checked-in Kraken/X64/Examples/Sbr/{ApplyTable,Apply,Apply/*}.lean
# byte for byte. No Lean run. Exit 1 on a difference.
set -u
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
APPLY_OUT=$T python3 "$HERE/gen.py" > /dev/null || { echo "regen: gen.py failed"; exit 1; }
n=0; d=0
while IFS= read -r f; do
  n=$((n+1))
  cmp -s "$T/$f" "$ROOT/Kraken/X64/Examples/Sbr/$f" || { echo "regen: DIFF $f"; d=$((d+1)); }
done < <(cd "$T" && find . -name '*.lean' | sed 's|^\./||' | sort)
echo "regen: $n generated files, $d differ from the checked-in ones"
[ $d = 0 ]
