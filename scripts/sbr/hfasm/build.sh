#!/bin/bash
# Generates the sbr_hf_assemble proof: Kraken/X64/Examples/Sbr/HfAssemble.lean,
# HfAssembleText.lean (the program text) and HfAssemble/{Base,Part1..K}.lean
# (HfAssemble/Cells.lean is hand-written, not generated).
# env: HFASM_WORK (scratch dir, default a temporary one), HFASM_OUT (output .lean, default the
#      Kraken file), HFASM_SPLIT (number of block modules, default 2; 0 = one file),
#      HFASM_OVR (override dir: <blk>.lean = full text of theorem blk_<blk>, default ./override),
#      HFASM_HB (default 1: per-block budgets from hb_table.txt, as checked in; 0 = generated budgets)
set -u
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
ROOT=$(cd "$HERE/../../.." && pwd)
cd "$HERE"
if [ -n "${HFASM_WORK:-}" ]; then W=$HFASM_WORK; mkdir -p "$W"; else W=$(mktemp -d); trap 'rm -rf "$W"' EXIT; fi
export HFASM_WORK=$W
OUT=${HFASM_OUT:-$ROOT/Kraken/X64/Examples/Sbr/HfAssemble.lean}
PYTHONDONTWRITEBYTECODE=1 python3 gen.py > "$W/gen.lean.in" || exit 1
python3 - "$W" <<'PY'
import sys
W = sys.argv[1]
spec = open('spec.lean.in').read()
head = open('proof_head.lean.in').read().replace('BODY', open('body.s').read())
frames = open(W + '/gen.lean.in').read()
open(W + '/full.lean', 'w').write(spec + head + frames)
PY
# HfAssembleText.lean: the program text, next to OUT
mkdir -p "$(dirname "$OUT")"
python3 - "$(dirname "$OUT")/HfAssembleText.lean" <<'PY'
import sys
open(sys.argv[1], 'w').write(open('text.lean.in').read().replace('BODY', open('body.s').read()))
PY
# HfAssemble/Base.lean + Part1..K.lean + HfAssemble.lean (split.py)
python3 split.py "$W/full.lean" "$OUT" "${HFASM_SPLIT:-2}" || exit 1
