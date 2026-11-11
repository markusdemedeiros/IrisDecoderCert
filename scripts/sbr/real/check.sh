#!/bin/bash
# Optional: the proofs about a real linked binary (see ../README.md, "Optional: checking
# against a real binary"). Run by ci.sh only when SBR_REAL=1.
#   0. the binary ($SBR_BIN) has the hash in ../baseline/binary.sha256
#   1. gen.py regenerates KrakenSbrReal/RealData.lean from the binary and the texts printed
#      by tv/Export.lean; it must equal the checked-in file
#   2. lake build KrakenSbrReal (RealData, Real: SbrPlaced for the binary's image, at every
#      load bias, and the witnesses under the link-time layout)
#   3. Ax.lean: #print axioms of the real theorems equals ../baseline/axioms_real.txt
#   4. RealExport.lean prints every cell of `rCE 0` with its address; check.py compares it
#      with the binary (bytes of every instruction, sizes, labels, constants)
# Exit status: 0 pass; 1 a check failed; 2 setup problem.
# Env: SBR_BIN (required), LLVM_BIN, SBR_OUT, SBR_CAP_CMD, SBR_OBJ_DIR (optional, for the
# constants' comparison with the objects; also needed by the export of step 1).
set -u
. "$(dirname "${BASH_SOURCE[0]}")/../common.sh"
REAL=$SBR_DIR/real
OUT=$SBR_OUT/real
mkdir -p "$OUT"
if [ -z "${SBR_BIN:-}" ] || [ ! -f "${SBR_BIN:-}" ]; then
  echo "real: SBR_BIN is not set or missing: point it at the FFmpeg 8.1 ffmpeg PIE (see scripts/sbr/README.md)"
  exit 2
fi
want=$(awk '{print $1}' "$SBR_DIR/baseline/binary.sha256")
have=$(sha256sum "$SBR_BIN" | awk '{print $1}')
if [ "$want" != "$have" ]; then
  echo "real: $SBR_BIN has sha256 $have, baseline/binary.sha256 says $want"; exit 2
fi
echo "binary: hash matches baseline/binary.sha256"

# -- 1. regenerate the data and compare
rm -rf "$OUT/lean"
SBR_TV_LEANDIR=$OUT/lean "${CAP[@]}" lake env lean "$SBR_DIR/tv/Export.lean" > "$OUT/export.log" 2>&1
echo "EXIT $?" >> "$OUT/export.log"
if ! grep -q '^EXIT 0$' "$OUT/export.log"; then
  echo "real: export of the texts failed:"; tail -20 "$OUT/export.log"; exit 2
fi
REAL_WORK=$OUT/work python3 "$REAL/gen.py" "$SBR_BIN" "$OUT/lean" "$OUT/RealData.lean" || exit 1
if ! cmp -s "$OUT/RealData.lean" KrakenSbrReal/RealData.lean; then
  echo "real: KrakenSbrReal/RealData.lean differs from gen.py's output ($OUT/RealData.lean)"
  diff "$OUT/RealData.lean" KrakenSbrReal/RealData.lean | head -20
  exit 1
fi
echo "RealData.lean: equal to gen.py's output"

# -- 2. build (and the source scan srcscan.py does for Kraken/X64/Examples/Sbr)
if python3 - <<'PY'
import re, glob, sys
bad = []
for f in sorted(glob.glob("KrakenSbrReal/*.lean")) + ["scripts/sbr/real/RealExport.lean", "scripts/sbr/real/Ax.lean"]:
  for i, l in enumerate(open(f), 1):
    code = l.split("--", 1)[0]
    if re.search(r"\b(sorry|admit|axiom|native_decide|bv_decide|maxHeartbeats|maxRecDepth)\b", code):
      bad.append(f"{f}:{i}: {l.rstrip()}")
print("\n".join(bad)); sys.exit(1 if bad else 0)
PY
then echo "srcscan: KrakenSbrReal clean"; else echo "real: forbidden token in the optional modules"; exit 1; fi
"${CAP[@]}" lake build KrakenSbrReal > "$OUT/build.log" 2>&1
rc=$?
echo "EXIT $rc" >> "$OUT/build.log"
if [ $rc != 0 ] || grep -qE '(^|: )error' "$OUT/build.log" || grep -qE 'declaration uses .sorry.' "$OUT/build.log"; then
  echo "real: lake build KrakenSbrReal failed:"; grep -E 'error|sorry' "$OUT/build.log" | head -20; exit 1
fi
echo "build: KrakenSbrReal ok"

# -- 3. axioms
"${CAP[@]}" lake env lean "$REAL/Ax.lean" > "$OUT/axioms.txt" 2>&1
if ! diff -q <(grep -v '^$' "$OUT/axioms.txt") <(grep -v '^$' "$SBR_DIR/baseline/axioms_real.txt") > /dev/null; then
  echo "real: axioms differ from baseline/axioms_real.txt:"
  diff <(grep -v '^$' "$OUT/axioms.txt") <(grep -v '^$' "$SBR_DIR/baseline/axioms_real.txt") | head -20
  exit 1
fi
echo "axioms: $(grep -c "depends on axioms" "$OUT/axioms.txt") theorems equal baseline/axioms_real.txt"

# -- 4. export the image and compare with the binary
SBR_REAL_OUT=$OUT "${CAP[@]}" lake env lean "$REAL/RealExport.lean" > "$OUT/realexport.log" 2>&1
echo "EXIT $?" >> "$OUT/realexport.log"
if ! grep -q '^EXIT 0$' "$OUT/realexport.log"; then
  echo "real: RealExport failed:"; tail -20 "$OUT/realexport.log"; exit 2
fi
grep '^cells' "$OUT/realexport.log"
python3 "$REAL/check.py" "$SBR_BIN" "$OUT" > "$OUT/check.txt" 2>&1
rc=$?
cat "$OUT/check.txt"

# -- 5. mutations: check.py must catch each edit of the exported image
#   m1 another constant in an operand; m2 two constants' labels swapped; m3 another branch
#   target; m4 one instruction cell one byte longer (the cells behind it shifted)
mrc=0
for m in m1 m2 m3 m4; do
  M=$OUT/mut/$m; rm -rf "$M"; mkdir -p "$M"
  cp "$OUT/texts.txt" "$M/"
  python3 - "$m" "$OUT/cells.txt" "$M/cells.txt" <<'PY'
import sys
m, src, dst = sys.argv[1:]
L = open(src).read().split("\n")
def first(pred):
  return next(i for i, l in enumerate(L) if pred(l))
if m == "m1":
  i = first(lambda l: "[rip+LCPI14_5]" in l); L[i] = L[i].replace("LCPI14_5", "LCPI14_6")
elif m == "m2":
  i = first(lambda l: l.endswith(" L LCPI14_0")); j = first(lambda l: l.endswith(" L LCPI14_10"))
  L[i], L[j] = L[i].replace("LCPI14_0", "LCPI14_10"), L[j].replace("LCPI14_10", "LCPI14_0")
elif m == "m3":
  i = first(lambda l: " I jae ff_aac_sbr_apply.L" in l)
  j = first(lambda l: " L ff_aac_sbr_apply.L" in l and l.split()[-1] not in L[i])
  L[i] = " ".join(L[i].split()[:3]) + " jae " + L[j].split()[-1]
elif m == "m4":
  i = first(lambda l: " I " in l and "ff_aac" not in l and l.split()[1] != "0")
  a, z = L[i].split()[:2]
  L[i] = f"{a} {int(z) + 1} " + L[i].split(" ", 2)[2]
  for k in range(i + 1, len(L)):
    if L[k]:
      f = L[k].split(" ", 1); L[k] = f"{int(f[0], 16) + 1:x} {f[1]}"
open(dst, "w").write("\n".join(L))
PY
  if python3 "$REAL/check.py" "$SBR_BIN" "$M" > "$M.txt" 2>&1; then
    echo "mutation $m: NOT caught"; mrc=1
  else
    echo "mutation $m: caught ($(grep -m1 -oE 'FINDING: .{0,80}' "$M.txt"))"
  fi
done
[ $mrc = 0 ] || rc=1
echo "real: exit $rc"
exit $rc
