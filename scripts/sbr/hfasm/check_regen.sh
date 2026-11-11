#!/bin/bash
# Regenerates the sbr_hf_assemble proof files from this directory into a scratch dir and
# requires them to equal the checked-in Kraken/X64/Examples/Sbr/HfAssemble.lean,
# HfAssembleText.lean and HfAssemble/{Base,Part1,Part2}.lean byte for byte. No Lean run.
# Exit 1 on a difference.
set -u
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
HFASM_WORK=$T/w HFASM_OUT=$T/out/HfAssemble.lean bash "$HERE/build.sh" > /dev/null || { echo "regen: build.sh failed"; exit 1; }
n=0; d=0
for f in HfAssemble.lean HfAssembleText.lean HfAssemble/Base.lean HfAssemble/Part1.lean HfAssemble/Part2.lean; do
  n=$((n+1))
  cmp -s "$T/out/$f" "$ROOT/Kraken/X64/Examples/Sbr/$f" || { echo "regen: DIFF $f"; d=$((d+1)); }
done
extra=$(cd "$T/out" && find . -name '*.lean' | wc -l)
[ "$extra" = "$n" ] || { echo "regen: generated $extra files, expected $n"; d=$((d+1)); }
echo "regen: $n generated files, $d differ from the checked-in ones"
[ $d = 0 ]
