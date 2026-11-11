# Sourced by ci.sh and tv/tv.sh. Sets SBR_DIR, SBR_ROOT (the repository root, also the
# working directory), SBR_OUT (scratch/output) and CAP (the optional memory-cap prefix).
SBR_DIR=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
SBR_ROOT=$(git -C "$SBR_DIR" rev-parse --show-toplevel 2>/dev/null || (cd "$SBR_DIR/../.." && pwd))
cd "$SBR_ROOT" || exit 2
SBR_OUT=${SBR_OUT:-.lake/sbr-ci}
mkdir -p "$SBR_OUT"
SBR_OUT=$(cd "$SBR_OUT" && pwd)
export SBR_DIR SBR_ROOT SBR_OUT
# SBR_CAP_CMD: a command prefix for every lean/lake invocation, e.g. a memory cap
#   SBR_CAP_CMD="systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0"
read -r -a CAP <<< "${SBR_CAP_CMD:-}"
cap_note() {
  if [ -z "${SBR_CAP_CMD:-}" ]; then
    echo "note: SBR_CAP_CMD unset: lean runs uncapped. Modules are built one at a time;" \
         "a parallel build of the Apply shards needs far more memory (about 9.5 GB per shard)."
  fi
}
