#!/bin/bash
# Translation validation of the SBR proofs' programs (see ../README.md).
#   0. the objects in $SBR_OBJ_DIR have the hashes in ../baseline/objects.sha256, and
#      each olean was built from the current source text (Fresh.lean)
#   1. Export.lean prints the elaborated Program terms (from the built oleans)
#   2. tv.py re-assembles them with llvm-mc at the object addresses and compares
#      bytes, relocations, labels and coverage with the objects
#   3. tv_data.py checks the object identity (rela.o = pic.o = g.o) and the data the
#      proofs assume (footprint regions, alignment, values)
#   4. a2_discipline.py, the row-crossing discipline: HfAssemble crosses a row of Y only
#      through a2_row_spill
#   5. mutations: each edit in mutations/ applied to the export must be caught by tv.py
# Exit status: 0 all checks pass; 1 a check failed; 2 setup problem (objects missing or
# with other hashes, stale oleans, lean failure). Builds nothing: build the modules first.
# Env: SBR_OBJ_DIR (required), LLVM_BIN, SBR_OUT, SBR_CAP_CMD, TV_ALLOW_STALE=1.
set -u
. "$(dirname "${BASH_SOURCE[0]}")/../common.sh"
TV=$SBR_DIR/tv
OUT=$SBR_OUT/tv
mkdir -p "$OUT"

# -- 0. objects and freshness
if [ -z "${SBR_OBJ_DIR:-}" ]; then
  echo "tv: SBR_OBJ_DIR is not set: point it at the directory holding aacsbr.rela.o," \
       "aacsbr.pic.o, aacsbr.g.o, aacps_common.{rela,pic,g}.o, sbrdsp.o and float_dsp.o (see scripts/sbr/README.md)"; exit 2
fi
if ! (cd "$SBR_OBJ_DIR" && sha256sum --quiet -c "$SBR_DIR/baseline/objects.sha256"); then
  echo "tv: the objects in SBR_OBJ_DIR do not match baseline/objects.sha256"; exit 2
fi
echo "objects: hashes match baseline/objects.sha256"
export SBR_OBJ_DIR
"${CAP[@]}" lake env lean "$TV/Fresh.lean" > "$OUT/fresh.log" 2>&1
echo "EXIT $?" >> "$OUT/fresh.log"
if ! grep -q '^EXIT 0$' "$OUT/fresh.log" || grep -q '^STALE' "$OUT/fresh.log"; then
  grep -v '^FRESH' "$OUT/fresh.log"
  if [ "${TV_ALLOW_STALE:-0}" != 1 ]; then
    echo "tv: oleans are not built from the current sources; rebuild (or TV_ALLOW_STALE=1)"; exit 2
  fi
fi
echo "oleans fresh: $(grep -c '^FRESH' "$OUT/fresh.log")"
sha256sum Kraken/X64/Examples/Sbr/Dsp/*.lean Kraken/X64/Examples/Sbr/HfAssemble/*.lean Kraken/X64/Examples/Sbr/*.lean Kraken/X64/Examples/Sbr/Parse/*Text.lean > "$OUT/hashes.txt"

# -- 1. export
rm -rf "$OUT/lean"
export SBR_TV_LEANDIR=$OUT/lean
"${CAP[@]}" lake env lean "$TV/Export.lean" > "$OUT/export.log" 2>&1
echo "EXIT $?" >> "$OUT/export.log"
if ! grep -q '^EXIT 0$' "$OUT/export.log"; then
  echo "tv: export failed:"; tail -20 "$OUT/export.log"; exit 2
fi
grep -c directives "$OUT/export.log" | sed 's/^/programs exported: /'
# the constants the top theorems place at labels (tv_data.py, part D)
SBR_TV_DATA=$OUT/data.txt "${CAP[@]}" lake env lean "$TV/ExportData.lean" > "$OUT/export_data.log" 2>&1
echo "EXIT $?" >> "$OUT/export_data.log"
if ! grep -q '^EXIT 0$' "$OUT/export_data.log"; then
  echo "tv: data export failed:"; tail -20 "$OUT/export_data.log"; exit 2
fi
grep '^data:' "$OUT/export_data.log"

# -- 2./3./4. compare
rc=0
python3 "$TV/tv.py" > "$OUT/tv.txt" 2>&1 || rc=1
cat "$OUT/tv.txt"
python3 "$TV/tv_data.py" > "$OUT/tv_data.txt" 2>&1 || rc=1
grep -E '^(FAIL|== )' "$OUT/tv_data.txt"; grep -c '^ok' "$OUT/tv_data.txt" | sed 's/^/data checks ok: /'
python3 "$TV/a2_discipline.py" > "$OUT/a2.txt" 2>&1 || rc=1
cat "$OUT/a2.txt"

# -- 4b. the Huffman tables (SessionSpecData.lean, the witness of the session's `VlcC` hypotheses)
# against FFmpeg's start-up code run on its own code tables (vlc/gen.py --check); optional:
# needs the FFmpeg n8.1 source tree (SBR_FFMPEG_SRC, extra include dirs in SBR_FFMPEG_INC).
if [ -n "${SBR_FFMPEG_SRC:-}" ]; then
  inc=(); for d in ${SBR_FFMPEG_INC:-}; do inc+=(-I "$d"); done
  if python3 "$SBR_DIR/vlc/gen.py" "$SBR_FFMPEG_SRC" "${inc[@]}" --check > "$OUT/vlc.txt" 2>&1; then
    echo "vlc tables: $(tail -1 "$OUT/vlc.txt")"
  else
    echo "FAIL vlc tables: $(tail -3 "$OUT/vlc.txt")"; rc=1
  fi
else
  echo "vlc tables: not checked (SBR_FFMPEG_SRC not set)"
fi

# -- 5. mutations: the checker must catch each edit
mrc=0
for d in "$TV"/mutations/m*.diff; do
  m=$(basename "$d" .diff)
  M=$OUT/mut/$m; rm -rf "$M"; mkdir -p "$M"
  cp "$OUT"/lean/*.txt "$M/"
  if ! patch -s -d "$M" -p1 < "$d"; then
    echo "mutation $m: does not apply to the export"; mrc=1; continue
  fi
  if TV_LEANDIR=$M TV_JSON_DIR=$M python3 "$TV/tv.py" > "$M.txt" 2>&1; then
    echo "mutation $m: NOT caught"; mrc=1
  else
    echo "mutation $m: caught ($(grep -m1 -oE 'FINDING: .{0,80}' "$M.txt"))"
  fi
done
# data mutations: an edited constant must fail part D
for d in "$TV"/mutations/d*.diff; do
  m=$(basename "$d" .diff)
  M=$OUT/mut/$m; rm -rf "$M"; mkdir -p "$M"
  cp "$OUT/data.txt" "$M/"
  if ! patch -s -d "$M" -p1 < "$d"; then
    echo "mutation $m: does not apply to the data export"; mrc=1; continue
  fi
  if TV_DATA=$M/data.txt python3 "$TV/tv_data.py" > "$M.txt" 2>&1; then
    echo "mutation $m: NOT caught"; mrc=1
  else
    echo "mutation $m: caught ($(grep -m1 -oE 'FAIL .{0,100}' "$M.txt"))"
  fi
done
[ $mrc = 0 ] || rc=1
echo "tv: exit $rc"
exit $rc
