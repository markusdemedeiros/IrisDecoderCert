#!/bin/bash
# Checks the ff_aac_sbr_apply proof (see README.md). Sequential by default: one lean process
# at a time. With SBR_JOBS>1 the build step runs up to SBR_JOBS module builds at once, within
# SBR_MEM_BUDGET_GB (default 24) of recorded peaks (pbuild.py, baseline/build_peaks.txt).
# Runs every step; exits 1 if any step failed.
#   1. build       per-module `lake build`, scanned for errors and `sorry`
#   2. axioms      `#print axioms` (Ax.lean) equals baseline/axioms.txt
#   3. tv          tv/tv.sh: translation validation against the objects, data, row-crossing
#                  discipline, mutation test of the checker
#   3b. a2         tv/a2_discipline.py (row-crossing discipline) on its own
#   3c. count      count_instr.py: instructions of the exported texts vs llvm-objdump of the objects
#   4. heartbeats  hbscan.py against baseline/hb_table.txt and baseline/hb_baseline.txt
#   5. srcscan     srcscan.py against baseline/srcscan_baseline.txt, and which baseline
#                  files are imported by Link/Witness/Linked (closure.py)
#   5a. regen      apply/ and hfasm/check_regen.sh: the generators reproduce the checked-in files
#   5b. tcb        Tcb.lean: the trusted closures of ff_aac_sbr_apply_linked and
#                  sbr_session_safe (what a reviewer reads); their fingerprints equal
#                  baseline/tcb_fingerprint.txt and baseline/tcb_fingerprint_session.txt
#   5c. spec       SpecCheck.lean: every declaration of the two closures outside the machine
#                  model and the program texts is in SessionSpec.lean/SessionSpecData.lean;
#                  text modules and SessionSpec import no proof module; spec_text.py: the
#                  generated part of SessionSpec.lean equals `parse/init/foot.py --spec`, and
#                  the statement it quotes equals sbr_session_safe's in SessionBin/Top.lean
#   6. real        OPTIONAL, only with SBR_REAL=1: real/check.sh, the proofs about a real
#                  linked binary (SBR_BIN) and their check against it
# Env: SBR_OBJ_DIR (required), LLVM_BIN, SBR_OUT, SBR_CAP_CMD, SBR_SKIP_BUILD=1,
#      SBR_JOBS, SBR_MEM_BUDGET_GB, SBR_MEM_RESERVE_GB (see pbuild.py),
#      SBR_REAL=1 with SBR_BIN (optional step 6).
set -u
. "$(dirname "${BASH_SOURCE[0]}")/common.sh"
OUT=$SBR_OUT/ci
rm -rf "$OUT"; mkdir -p "$OUT"
P=Kraken.X64.Examples.Sbr
declare -A RES
fail=0
mark() { RES[$1]=$2; [ "$2" = ok ] || fail=1; }
cap_note
if [ -z "${SBR_OBJ_DIR:-}" ]; then
  echo "ci: SBR_OBJ_DIR is not set: point it at the directory holding aacsbr.rela.o," \
       "aacsbr.pic.o, aacsbr.g.o, aacps_common.{rela,pic,g}.o, sbrdsp.o and float_dsp.o (see scripts/sbr/README.md)"; exit 2
fi

# ---- 1. build (dependency order; each module on its own)
MODS="ApplyText Dsp.NegOdd64Text Dsp.Sum64x5Text Dsp.SumSquareText Dsp.QmfPreShuffleText
 Dsp.QmfPostShuffleText Dsp.QmfDeintNegText Dsp.QmfDeintBflyText Dsp.AutocorrelateText
 Dsp.HfGenText Dsp.HfGFiltText Dsp.HfApplyNoiseText Dsp.VectorFmulText Dsp.VectorFmulAddText
 Dsp.VectorFmulRevText LfGenText HfInverseFilterText XGenText QmfSynthesisText HfAssembleText
 Parse.DecExtText Parse.HdrText Parse.DtdfText Parse.InvfText Parse.NoiseText Parse.EnvText
 Parse.PsText Parse.TlimText Parse.UsacText Parse.InitText Parse.GridText Parse.ResetBlocks
 SessionSpecData SessionSpec
 Spec DequantFloat
 Dsp.NegOdd64 Dsp.Sum64x5 Dsp.SumSquare Dsp.QmfPreShuffle Dsp.QmfPostShuffle Dsp.QmfDeintNeg
 Dsp.QmfDeintBfly Dsp.Autocorrelate Dsp.HfGen Dsp.HfGFilt Dsp.HfApplyNoise Dsp
 Dsp.FloatDspCommon Dsp.VectorFmul Dsp.VectorFmulAdd Dsp.VectorFmulRev FloatDsp
 LfGen HfInverseFilter XGen QmfSynthesis
 HfAssemble.Cells HfAssemble.Base HfAssemble.Part1 HfAssemble.Part2 HfAssemble
 ApplySpec ApplyTable
 Apply.Trap Apply.EntrySyn Apply.DqCpl Apply.DqSce Apply.AnaHf Apply.EnvALem Apply.EnvA1
 Apply.EnvA2 Apply.EnvA3 Apply.EnvBLem Apply.EnvB1 Apply.EnvB2 Apply.EnvB3 Apply.MapALem
 Apply.MapA1 Apply.MapA2 Apply.MapA3 Apply.MapA4 Apply.MapA5 Apply.MapBLem Apply.MapB1
 Apply.MapB2 Apply.MapB3 Apply.MapB4 Apply.MapB5 Apply.MapB6 Apply.MapB7 Apply.MapB8
 Apply.MapB9 Apply.MapB10 Apply.MapB11 Apply.MapB12 Apply.MapB13 Apply.GainAsm Apply
 Link Witness Placement Linked Session ParseModel
 Parse.Lib Parse.LibGb Parse.LibAbort Parse.LibCall Parse.LibMem Parse.GridFoot
 Parse.GridBlk1 Parse.GridBlk2 Parse.GridBlk3 Parse.GridBlk4 Parse.GridTrap Parse.GridSmp
 Parse.GridShA1 Parse.GridShA2 Parse.GridShA3 Parse.GridShA4 Parse.GridShA5 Parse.GridShA6 Parse.GridShA7 Parse.GridShA8 Parse.GridShB1 Parse.GridShB2 Parse.GridShB3 Parse.GridShB4
 Parse.GridShC1 Parse.GridShC2 Parse.GridShC3
 Parse.GridShD0 Parse.GridShD1 Parse.GridShD2 Parse.GridShD3 Parse.GridShD4 Parse.GridShD5 Parse.GridShD6 Parse.GridShD7 Parse.GridShD8 Parse.GridShD9 Parse.GridShD10
 Parse.GridAsm
 Parse.DecExtSpec Parse.DecExtBase Parse.DecExtMem Parse.DecExtEntry
 Parse.DecExtPro Parse.DecExtPro2 Parse.DecExtExit Parse.DecExtOff Parse.DecExtCall
 Parse.DecExtOffD Parse.DecExtDat Parse.DecExtSce Parse.DecExtSce2 Parse.DecExtHarm
 Parse.DecExtExt Parse.DecExtPs Parse.DecExtCpe Parse.DecExtCpeH Parse.DecExtCpB Parse.DecExtCpD
 Parse.DecExtCpTail Parse.DecExtCpF Parse.DecExtCpG Parse.DecExtCpInvf Parse.DecExtAll
 Parse.HdrSpec Parse.ResetText Parse.ResetSpec Parse.DecExtGlue
 Parse.DtdfSpec Parse.InvfSpec Parse.DecExtGlueC Parse.DecExtGlueR Parse.EnvVlc
 Parse.NoiseSpec Parse.EnvSpec Parse.DecExtGlueN Parse.DecExtGlueH
 Parse.DecExtGlueG Parse.PsSpec Parse.DecExtGlueP Parse.DecExtNeed Parse.DecExtWF
 Parse.DtdfBase Parse.DtdfBlk1 Parse.DtdfBlk2 Parse.DtdfLoop Parse.DtdfProc Parse.EnvLib
 Parse.EnvBase Parse.EnvFrame Parse.EnvVar Parse.EnvMem Parse.EnvBlk1 Parse.EnvBlk2 Parse.EnvBlk3
 Parse.EnvBlk6 Parse.EnvBlk7 Parse.EnvBlk8 Parse.EnvBlk11 Parse.EnvBlk10 Parse.EnvBlk12
 Parse.EnvBlk13 Parse.EnvBlk14 Parse.EnvBlk4 Parse.EnvBlk5 Parse.EnvBlk9 Parse.EnvStack
 Parse.EnvEntry Parse.EnvTrap Parse.EnvProc Parse.HdrLib Parse.HdrBase Parse.HdrMem Parse.HdrFrame
 Parse.HdrStep Parse.HdrBlk1 Parse.HdrBlk2 Parse.HdrBlk3 Parse.HdrEnd Parse.HdrBlk4 Parse.HdrCall
 Parse.HdrProc Parse.InvfBase Parse.InvfMem Parse.InvfBlk Parse.InvfProc Parse.LibQsort
 Parse.NoiseBase Parse.NoiseMem Parse.NoiseBlk1 Parse.NoiseFrame Parse.NoiseVlc Parse.NoiseBlk2
 Parse.NoiseBlk3 Parse.NoiseBlk4 Parse.NoiseBlk5 Parse.NoiseBlk6 Parse.NoiseBlk7 Parse.NoiseBlk8
 Parse.NoiseProc Parse.PsLib Parse.PsCore Parse.PsInvH Parse.PsInvL Parse.PsInvX Parse.PsInvT1
 Parse.PsInvT2 Parse.PsInvT Parse.PsCfg Parse.PsCfgH Parse.PsCfgL Parse.PsCfgX Parse.PsCfgT
 Parse.PsBase Parse.PsFrame Parse.PsBlkHLib Parse.PsBlkH0 Parse.PsBlkH1 Parse.PsBlkH2
 Parse.PsBlkH3 Parse.PsBlkH4 Parse.PsBlkH5 Parse.PsBlkHNLib Parse.PsBlkHN1 Parse.PsBlkHN2
 Parse.PsBlkHN3 Parse.PsBlkHNLib2 Parse.PsBlkHNAvx Parse.PsBlkHN4 Parse.PsBlkHN5 Parse.PsBlkLLib
 Parse.PsBlkL1 Parse.PsBlkL2 Parse.PsBlkL3 Parse.PsBlkL4 Parse.PsBlkL5 Parse.PsBlkL6 Parse.PsBlkL7
 Parse.PsBlkLPLib Parse.PsBlkLE1 Parse.PsBlkLP1 Parse.PsBlkLP2 Parse.PsBlkT1Lib Parse.PsBlkT1L1
 Parse.PsBlkT1_1 Parse.PsBlkT1_2 Parse.PsBlkT1_3 Parse.PsBlkT1_4 Parse.PsBlkT1_5 Parse.PsBlkT1_6
 Parse.PsBlkT1_7 Parse.PsBlkT1_8 Parse.PsBlkT2Lib Parse.PsBlkT2L1 Parse.PsBlkT2_1 Parse.PsBlkT2_10
 Parse.PsBlkT2_2 Parse.PsBlkT2_3 Parse.PsBlkT2_4 Parse.PsBlkT2_5 Parse.PsBlkT2_6 Parse.PsBlkT2_7
 Parse.PsBlkT2_8 Parse.PsBlkT2_9 Parse.PsBlkXLib Parse.PsBlkX1 Parse.PsBlkX2 Parse.PsBlkX3
 Parse.PsBlkX4 Parse.PsBlkX5 Parse.PsBlkX6 Parse.PsBlkX7 Parse.PsBlkX8 Parse.PsBlkX9 Parse.PsConv
 Parse.PsEntry Parse.ResetA1Avx Parse.ResetA1Avx2 Parse.ResetLib Parse.ResetBase Parse.ResetFoot
 Parse.ResetIface Parse.ResetTable Parse.ResetA1Lib Parse.ResetA1Disp Parse.ResetA2Lib
 Parse.ResetA1Mem Parse.ResetModel Parse.ResetA1K2 Parse.ResetA1F0 Parse.ResetA1Inc
 Parse.ResetA1F1 Parse.ResetA1F2 Parse.ResetA1F3 Parse.ResetA1F4 Parse.ResetA1W Parse.ResetA2Lane
 Parse.ResetA1F5 Parse.ResetA1Fail Parse.ResetLog Parse.ResetA1Float Parse.ResetA1G
 Parse.ResetA1G2 Parse.ResetA1G3 Parse.ResetA1K0 Parse.ResetA1Pro Parse.ResetA1Stop
 Parse.ResetA1Sum Parse.ResetA2Spec Parse.ResetA2Exit Parse.ResetA2Blk Parse.ResetA2Flt
 Parse.ResetA2Mk Parse.ResetA2Mk2 Parse.ResetA2Pfx Parse.ResetA2Loop Parse.ResetA2Loop2
 Parse.ResetA2Loop3 Parse.ResetExitW Parse.ResetA2Mc Parse.ResetA2Pfx1 Parse.ResetA2Pfx0
 Parse.ResetA2Rem Parse.ResetDerLib Parse.ResetOff2 Parse.ResetDer Parse.ResetELib Parse.ResetE1
 Parse.ResetE2 Parse.ResetE3 Parse.ResetE4 Parse.ResetE5 Parse.ResetE6 Parse.ResetE7 Parse.ResetE8
 Parse.ResetExit Parse.ResetFail Parse.ResetPatLib Parse.ResetNoiseLib Parse.ResetNoise1
 Parse.ResetNq Parse.ResetNz Parse.ResetNzB Parse.ResetNzC Parse.ResetOff Parse.ResetPat1
 Parse.ResetPat2 Parse.ResetPat3 Parse.ResetPat5 Parse.ResetPat6 Parse.ResetPat7 Parse.ResetQsFr
 Parse.ResetQs1A Parse.ResetQsLib Parse.ResetQs1B Parse.ResetQs1Lib Parse.ResetQs1C
 Parse.ResetQs1D Parse.ResetQs1E Parse.ResetQs2Lib Parse.ResetQs2Lib2 Parse.ResetQs2Lib3
 Parse.ResetQs2Lib4 Parse.ResetQs1F Parse.ResetQs1G Parse.ResetQs2A Parse.ResetQs2B
 Parse.ResetQs2C Parse.ResetQs2D Parse.ResetQs2E Parse.ResetQs2F Parse.ResetQs2G Parse.ResetQs2H
 Parse.ResetQs2I Parse.ResetQs2J Parse.ResetQs3Lib Parse.ResetQs3A Parse.ResetQs3B Parse.ResetQs3C
 Parse.ResetQs3D Parse.ResetQs3E Parse.ResetQs3F Parse.ResetQs3G Parse.ResetQs4Lib Parse.ResetQs4A
 Parse.ResetQs4B Parse.ResetQs4C Parse.ResetQs4D Parse.ResetQs4E Parse.ResetQs4F Parse.ResetQs4G
 Parse.ResetTail Parse.ResetTrap Parse.ResetProc Parse.TlimSpec Parse.TlimLib
 Parse.TlimBase Parse.TlimVar Parse.TlimTab Parse.TlimMem Parse.TlimAcc Parse.TlimBlkA
 Parse.TlimBlkB Parse.TlimBlkC Parse.TlimBlkD Parse.TlimBlkE Parse.TlimMc Parse.TlimFin
 Parse.TlimCmp Parse.TlimCmp2 Parse.TlimCmp3 Parse.TlimGlue Parse.TlimHdr Parse.TlimTrap
 Parse.TlimQsLib Parse.TlimQsA Parse.TlimQsB Parse.TlimQsLib2 Parse.TlimQsC Parse.TlimQsD
 Parse.TlimQsG1 Parse.TlimQsG2 Parse.TlimQsG3 Parse.TlimQsG4 Parse.TlimQsG5 Parse.TlimQsE
 Parse.TlimQsF Parse.TlimQsH1 Parse.TlimQsH2 Parse.TlimQsH3 Parse.TlimProc
 Parse.UsacSpec Parse.UsacCfg Parse.UsacBase Parse.UsacModel Parse.UsacTbl1 Parse.UsacTbl5
 Parse.UsacTbl6 Parse.UsacBlk1 Parse.UsacTbl2 Parse.UsacTbl3 Parse.UsacBlk2 Parse.UsacTbl4
 Parse.UsacBlk3 Parse.UsacBlk7 Parse.UsacBlk8 Parse.UsacBlk9 Parse.UsacBlk10 Parse.UsacBlk11
 Parse.UsacBlk12 Parse.UsacBlk13 Parse.UsacBlk14 Parse.UsacBlk15 Parse.UsacBlk16 Parse.UsacBlk17
 Parse.UsacBlk18 Parse.UsacBlk19 Parse.UsacBlk20 Parse.UsacBlk21 Parse.UsacBlk22 Parse.UsacBlk23
 Parse.UsacBlk24 Parse.UsacBlk25 Parse.UsacBlk4 Parse.UsacBlk5 Parse.UsacBlk6 Parse.UsacGrd
 Parse.UsacGrd2 Parse.UsacCall Parse.UsacCall2 Parse.UsacGC1 Parse.UsacCpM Parse.UsacCpL
 Parse.UsacCp1 Parse.UsacCp2 Parse.UsacCp3 Parse.UsacCp4 Parse.UsacAsm
 Parse.UsacGlueL Parse.UsacGlueR Parse.UsacGlueH
 Parse.VlcWit Parse.GridJtWit
 Parse.InitFoot Parse.InitSpec Parse.InitBase Parse.InitFrame Parse.InitMem
 Parse.InitTx Parse.InitBlk1 Parse.InitBlk2 Parse.InitBlk3 Parse.InitBlk4 Parse.InitBlk5
 Parse.InitBlk6 Parse.InitBlk7 Parse.InitEnd Parse.InitBlk8 Parse.InitProc Parse.InitLinkBase
 Parse.InitLink
 SessionBin.Defs SessionBin.LeafDerive SessionBin.Bridge SessionBin.Inv SessionBin.FApplyD SessionBin.FApplyS
 SessionBin.FApply SessionBin.DecAsm SessionBin.FDec SessionBin.FCfgA SessionBin.FCfg
 SessionBin.SApply SessionBin.SConfig SessionBin.SDec SessionBin.BridgeU SessionBin.UsacAsmS
 SessionBin.FUsac SessionBin.SUsac SessionBin.Main
 SessionBin.SInit SessionBin.TopDefs SessionBin.InitSafe SessionBin.TopCalls
 SessionBin.Top"
# tv/Export.lean imports Kraken.X64.PrintIntel (tv/Fresh.lean checks its olean), which no
# module in MODS imports: build it first, alone, so it never races with the module builds
tvlib=ok
if [ "${SBR_SKIP_BUILD:-0}" != 1 ]; then
  "${CAP[@]}" lake build Kraken.X64.PrintIntel > "$OUT/build_tvlib.txt" 2>&1 || tvlib=FAIL
  echo "Kraken.X64.PrintIntel (tv) build: $tvlib"
fi
if [ "${SBR_SKIP_BUILD:-0}" != 1 ] && [ "${SBR_JOBS:-1}" -gt 1 ]; then
  # memory-aware parallel build (pbuild.py): same per-module logs, caps and scans
  python3 "$SBR_DIR/pbuild.py" "$OUT" "$P" $MODS > "$OUT/build_sched.log" 2>&1
  rc=$?
  cat "$OUT/build.txt" 2>/dev/null; tail -1 "$OUT/build_sched.log"
  [ $rc = 0 ] && [ $tvlib = ok ] && mark build ok || mark build FAIL
elif [ "${SBR_SKIP_BUILD:-0}" != 1 ]; then
  bfail=0
  : > "$OUT/build.txt"
  for m in $MODS; do
    L=$OUT/build_$m.txt
    TIMER=(); [ -x /usr/bin/time ] && TIMER=(/usr/bin/time -f "%e s %M KB" -o "$L.time")
    "${TIMER[@]}" "${CAP[@]}" lake build "$P.$m" > "$L" 2>&1
    rc=$?
    e=$(grep -c '^error' "$L"); s=$(grep -cE 'declaration uses .sorry.' "$L")
    echo "$m rc=$rc $(tail -1 "$L.time" 2>/dev/null) errors=$e sorry=$s" >> "$OUT/build.txt"
    { [ $rc -ne 0 ] || [ "$e" -ne 0 ] || [ "$s" -ne 0 ]; } && bfail=1
  done
  cat "$OUT/build.txt"
  [ $bfail = 0 ] && [ $tvlib = ok ] && mark build ok || mark build FAIL
else
  RES[build]=skipped
fi

# ---- 2. axioms
"${CAP[@]}" lake env lean "$SBR_DIR/Ax.lean" > "$OUT/axioms.txt" 2>&1
rc=$?
cat "$OUT/axioms.txt"
if [ $rc = 0 ] && diff "$SBR_DIR/baseline/axioms.txt" "$OUT/axioms.txt" > "$OUT/axioms.diff"; then
  echo "axioms: output equals baseline/axioms.txt ($(wc -l < "$OUT/axioms.txt") theorems)"
  mark axioms ok
else
  echo "axioms: differs from baseline/axioms.txt (rc=$rc):"; cat "$OUT/axioms.diff"
  mark axioms FAIL
fi

# ---- 3. tv
bash "$SBR_DIR/tv/tv.sh" > "$OUT/tv.txt" 2>&1; rc=$?
grep -E '^(objects|oleans|programs|data|vlc tables|ok a2|FAIL|mutation|tv:)|FINDING|LINK' "$OUT/tv.txt"
[ $rc = 0 ] && mark tv ok || mark tv FAIL

# ---- 3b. row-crossing discipline (also part of tv.sh; listed on its own)
python3 "$SBR_DIR/tv/a2_discipline.py" > "$OUT/a2.txt" 2>&1; rc=$?
cat "$OUT/a2.txt"
[ $rc = 0 ] && mark a2 ok || mark a2 FAIL

# ---- 3c. instruction count, independent of tv.py (uses tv.sh's export)
python3 "$SBR_DIR/count_instr.py" "$SBR_OUT/tv/lean" "$SBR_OBJ_DIR" > "$OUT/count.txt" 2>&1; rc=$?
tail -2 "$OUT/count.txt"
[ $rc = 0 ] && mark count ok || mark count FAIL

# ---- 4. heartbeats
python3 "$SBR_DIR/hbscan.py" > "$OUT/hbscan.txt" 2>&1; rc=$?
cat "$OUT/hbscan.txt"
[ $rc = 0 ] && mark heartbeats ok || mark heartbeats FAIL

# ---- 5. source scan
python3 "$SBR_DIR/srcscan.py" > "$OUT/srcscan.txt" 2>&1; rc=$?
python3 "$SBR_DIR/closure.py" $P.Link $P.Witness $P.Linked >> "$OUT/srcscan.txt" 2>&1
cat "$OUT/srcscan.txt"
[ $rc = 0 ] && mark srcscan ok || mark srcscan FAIL

# ---- 5a. the Apply and HfAssemble generators reproduce the checked-in files (no Lean)
bash "$SBR_DIR/apply/check_regen.sh" > "$OUT/regen.txt" 2>&1; rc=$?
bash "$SBR_DIR/hfasm/check_regen.sh" >> "$OUT/regen.txt" 2>&1; rc2=$?
cat "$OUT/regen.txt"
[ $rc = 0 ] && [ $rc2 = 0 ] && mark regen ok || mark regen FAIL

# ---- 5b. trusted closures: change exactly when the meaning of a statement can change
"${CAP[@]}" lake env lean "$SBR_DIR/Tcb.lean" > "$OUT/tcb.txt" 2>&1; rc=$?
grep -E '^(TOTAL|FINGERPRINT|== )' "$OUT/tcb.txt"
tcbok=1
for pair in "FINGERPRINT:tcb_fingerprint.txt" "FINGERPRINT_SESSION:tcb_fingerprint_session.txt"; do
  tag=${pair%%:*}; base=${pair#*:}
  fpn=$(sed -n "s/^$tag //p" "$OUT/tcb.txt"); fpb=$(cat "$SBR_DIR/baseline/$base" 2>/dev/null)
  if [ $rc = 0 ] && [ -n "$fpn" ] && [ "$fpn" = "$fpb" ]; then
    echo "tcb: $tag equals baseline/$base"
  else
    echo "tcb: $tag $fpn differs from baseline/$base ($fpb), rc=$rc: the statement's"
    echo "     specification, machine model or a program text changed; review it, then re-record"
    tcbok=0
  fi
done
[ $tcbok = 1 ] && mark tcb ok || mark tcb FAIL

# ---- 5c. the specification is one file, importing no proofs
"${CAP[@]}" lake env lean "$SBR_DIR/SpecCheck.lean" > "$OUT/spec.txt" 2>&1; rc=$?
python3 "$SBR_DIR/spec_text.py" >> "$OUT/spec.txt" 2>&1; rc2=$?
grep -vE '^text module' "$OUT/spec.txt" | head -40
[ $rc = 0 ] && [ $rc2 = 0 ] && grep -q '^SPECCHECK ok' "$OUT/spec.txt" && mark spec ok || mark spec FAIL

# ---- 6. real (optional)
STEPS="build axioms tv a2 count heartbeats srcscan regen tcb spec"
if [ "${SBR_REAL:-0}" = 1 ]; then
  bash "$SBR_DIR/real/check.sh" > "$OUT/real.txt" 2>&1; rc=$?
  cat "$OUT/real.txt"
  [ $rc = 0 ] && mark real ok || mark real FAIL
  STEPS="$STEPS real"
fi

echo
echo "== CI summary"
for k in $STEPS; do printf "%-11s %s\n" "$k" "${RES[$k]:-?}"; done
echo "ci: exit $fail"
exit $fail
