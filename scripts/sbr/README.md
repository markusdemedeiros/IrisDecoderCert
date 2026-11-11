# Checking the `ff_aac_sbr_apply` proof

`ci.sh` re-checks the memory-safety proof of FFmpeg's `ff_aac_sbr_apply` (with its callees
`sbr_qmf_synthesis`, `sbr_lf_gen`, `sbr_hf_inverse_filter`, `sbr_x_gen`, `sbr_hf_assemble` and
the x86 `SBRDSPContext` routines) in `Kraken/X64/Examples/Sbr/`. The final theorem is
`Kraken.Examples.Sbr.ff_aac_sbr_apply_linked` (`Link.lean`); its docstring lists what is
assumed and what is open.

```
SBR_OBJ_DIR=/path/to/objects LLVM_BIN=/path/to/llvm/bin \
SBR_CAP_CMD="systemd-run --user --scope -q -p MemoryMax=12G -p MemorySwapMax=0" \
  scripts/sbr/ci.sh
```

Run it from anywhere inside the repository; everything is resolved from the repository root.

## Steps

| step | checks |
|---|---|
| build | `lake build` of each module of the proof, one at a time in dependency order (Spec, Dsp/*, the C procedures, ApplySpec, ApplyTable, the Apply shards, Apply, Link, Witness, Linked, Session, ParseModel); fails on a nonzero exit, an `error`, or `declaration uses 'sorry'` |
| axioms | `#print axioms` (`Ax.lean`) of the final theorem, every procedure specification and the four satisfiability witnesses equals `baseline/axioms.txt`: each exactly `[propext, Classical.choice, Quot.sound]` |
| tv | `tv/tv.sh`, translation validation. The objects' hashes equal `baseline/objects.sha256`; the oleans are built from the current sources. The elaborated program texts (`tv/Export.lean`) are re-assembled with `llvm-mc` at the object addresses and compared with the objects byte for byte (relocations resolved, labels at their symbols, padding sized). `tv/tv_data.py` checks that the object variants agree and that every data region, alignment and constant the proofs assume holds in the objects. The row-crossing discipline (below). Finally each edit in `tv/mutations/` is applied to the exported text and must be caught |
| a2 | `tv/a2_discipline.py`, the row-crossing discipline: `HfAssemble.lean` (with `HfAssemble/*.lean`) crosses a row of `Y` only through `a2_row_spill` |
| count | `count_instr.py`: counts the non-padding instructions of each exported text and, separately, of the same routine in the objects with `llvm-objdump` (range from the ELF symbol size, or to the next function symbol for NASM code); fails unless the two agree for all 39 texts. Independent of `tv.py`. Run alone: `python3 scripts/sbr/count_instr.py $SBR_OUT/tv/lean $SBR_OBJ_DIR` after `tv/tv.sh`. |
| heartbeats | `hbscan.py`: the generated per-block `maxHeartbeats` of the Apply shards equal `baseline/hb_table.txt`; no other `maxHeartbeats`/`maxRecDepth` option beyond `baseline/hb_baseline.txt` |
| srcscan | `srcscan.py`: no `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide`, and none of the kernel-bypassing `debug.*` options (e.g. `debug.skipKernelTC`), `implemented_by`, `@[extern]`, `unsafe`, in `Kraken/X64/Examples/Sbr/`; elsewhere in `Kraken/` nothing beyond `baseline/srcscan_baseline.txt` (19 upstream uses, one an `unsafe def` in `Eval.lean`). `closure.py` prints which of those files the proof imports (`Rules/IntMisc.lean`, `Specs.lean`; the axioms step shows none of their `bv_decide` lemmas is used) |
| regen | `apply/check_regen.sh` and `hfasm/check_regen.sh`: the generators regenerate `ApplyText.lean`, `ApplyTable.lean`, `Apply.lean`, `Apply/*.lean`, and `HfAssemble.lean`, `HfAssemble/{Base,Part1,Part2}.lean`, into a scratch directory; they must equal the checked-in files byte for byte (no Lean run) |
| spec | `SpecCheck.lean`: every declaration of the two trusted closures that is neither the machine model (`Kraken.*` outside `Kraken.X64.Examples`, and Lean) nor a program text is defined in `SessionSpec.lean` or `SessionSpecData.lean`; the modules holding the program texts import (transitively) only the machine model and other text modules; `SessionSpec`/`SessionSpecData` import only those. Also `spec_text.py`: `parse/init/foot.py --spec` (the generated `EV`, `ElemS`) must appear verbatim in `SessionSpec.lean`, and the statement of `sbr_session_safe` quoted in its module docstring must equal the one in `SessionBin/Top.lean` (up to `:=`, whitespace-normalized) |
| tcb | `Tcb.lean`: the trusted closures of the two final theorems, `ff_aac_sbr_apply_linked` and `SessionBin.sbr_session_safe`, i.e. every declaration reachable from a statement through statements and definition bodies but not proofs, with its source lines per module, and a fingerprint of each closure's names, types and bodies. The fingerprints must equal `baseline/tcb_fingerprint.txt` (`FINGERPRINT`) and `baseline/tcb_fingerprint_session.txt` (`FINGERPRINT_SESSION`). They change exactly when the specification, the machine model or a program text changes; review such a change, then re-record the printed line |

## What to review

The kernel checks every proof; what it cannot check is what the statement means. A
reviewer reads the trusted closure (`tcb` step), not the proofs:

- the specification: `SessionSpec.lean`, with the Huffman tables in `SessionSpecData.lean`.
  It holds every definition the two final statements depend on other than the machine model and
  the program texts, in dependency order, one section per proof module (callee contracts,
  `ApplySpec`, the placement and slot facts, the session vocabulary `Live`/`Ready`/`AcFields`,
  the models, the parser contracts, and the parts of `sbr_session_safe`); its module docstring
  has a table of contents. It imports only the machine model, the program texts (the
  `…Text.lean` modules, `ApplyText.lean`, `Parse/ResetBlocks.lean`, which import only the parser
  and the machine model) and `SessionSpecData`; the `spec` step checks all of this. The final
  statements are in `Link.lean` (`ff_aac_sbr_apply_linked`) and `SessionBin/Top.lean`
  (`sbr_session_safe`);
- the machine model this work added to: `Kraken/X64/Semantics.lean`, `Syntax.lean`;
- not the program texts themselves but the checker that matches them to the objects:
  `tv/tv.py`, `tv/tv_data.py`, `tv/tv.sh`, `tv/Export.lean`, `tv/Fresh.lean`,
  `Kraken/X64/PrintIntel.lean`;
- these scripts: `Ax.lean` with `baseline/axioms.txt`, `srcscan.py`, `Tcb.lean`;
- for adequacy: whether the `SbrAssumed` contracts hold of the real routines (an over-strong
  one makes the theorem vacuous; see FD1) and the statements, not the proofs, of
  the satisfiability witnesses (`Witness.lean`, `Linked.lean`).
- for the use of the theorem across calls: `Session.lean` (not in the trusted closure; it imports
  `Link.lean` and nothing imports it). It states a decoding session of one element: the values
  after `ff_aac_sbr_ctx_alloc_init` (`xInit`, with `SbrWF` proved), the reachable values
  (`Reachable`) and the assumptions they rest on: `ParseStep` (the parser preserves `SbrWF`
  together with a parser-side invariant) and `CallerFrame` (each call state owns the footprint
  at the current values). Read the statements of `ParseStep`, `FrameStep`, `xInit`,
  `CallerFrame` and `session_call`.
  `ParseModel.lean` (imports `Session.lean`, nothing imports it) is a functional model of the
  parser transcribed from the C source, with `ParseStep ModelStep (GridInv ∧ Inv2)` proved
  (`modelStep_parseStep`; `ModelStep` has no guard on the visible values): evidence that `ParseStep` is satisfiable by the parser's source
  semantics, not a statement about its machine code. Its abstractions are listed in its doc
  comments.

Block proofs, label tables and entry assertions, helper lemmas, the generated `Apply/*.lean`,
`HfAssemble/*.lean` and the tactics need no review for soundness.

## Environment

| variable | |
|---|---|
| `SBR_OBJ_DIR` | required: directory with `aacsbr.rela.o`, `aacsbr.pic.o`, `aacsbr.g.o`, `aacps_common.rela.o`, `aacps_common.pic.o`, `aacps_common.g.o`, `log2_tab.g.o`, `sbrdsp.o`, `float_dsp.o` (hashes in `baseline/objects.sha256`) |
| `LLVM_BIN` | directory of `llvm-objdump`, `llvm-objcopy`, `llvm-mc`, `llvm-readelf` (LLVM 21 was used); default: from `PATH` |
| `SBR_CAP_CMD` | optional command prefix for every `lake`/`lean` call, e.g. a memory cap. Without it lean runs uncapped. The largest module (`Apply.GainAsm`) peaks at about 9.5 GB, so modules must be built one at a time (`ci.sh` does); a plain parallel `lake build` of the Apply shards runs out of memory on ordinary machines |
| `SBR_FFMPEG_SRC`, `SBR_FFMPEG_INC` | optional: the FFmpeg n8.1 source tree (and extra include directories, space-separated) for the tv check of the Huffman tables `SessionSpecData.lean` (`vlc/gen.py --check`); without it that check is skipped and says so |
| `SBR_OUT` | scratch and output, default `.lake/sbr-ci` |
| `SBR_SKIP_BUILD=1` | skip the build step (the tv step still refuses stale oleans) |

## The objects

FFmpeg n8_1, built with clang at `-O3 -mavx -msse4.2 -fPIC -mcmodel=medium
-fno-omit-frame-pointer -mtune=haswell -mprefer-vector-width=128 -fno-strict-aliasing
-ffunction-sections` (x86-64, optimized build of `libavcodec`):

- `aacsbr.pic.o`: `libavcodec/aacsbr.c` as compiled (one section per function);
- `aacsbr.rela.o`: the same object merged into one `.text` (`ld -r`), the addresses the
  Lean texts are named after (`ff_aac_sbr_apply.L66e0` …);
- `aacsbr.g.o`: the same compilation with debug information (DWARF);
- `aacps_common.pic.o`, `aacps_common.rela.o`, `aacps_common.g.o`: the same three for
  `libavcodec/aacps_common.c` (`ff_ps_read_data`, which `aacsbr.o` calls);
- `log2_tab.g.o`: `libavutil/log2_tab.c` of the same build, with debug information
  (`ff_log2_tab`, which `ff_ps_read_data` reads through the GOT);
- `sbrdsp.o`: `libavcodec/x86/sbrdsp.asm`, assembled with NASM for x86-64;
- `float_dsp.o`: `libavutil/x86/float_dsp.asm`, assembled with NASM 3.01 from the
  FFmpeg source root: `nasm -f elf64 -DPIC -g -F dwarf -I./ -P./config.asm
  libavutil/x86/float_dsp.asm -o float_dsp.o`.

`tv_data.py` checks that the C procedures tv compares (apply's six and the session's twelve in
`aacsbr`, `ff_ps_read_data` in `aacps_common`) are identical in the three objects of each, and (part D) that every constant
byte list the two top theorems place at a label (printed from their elaborated closures by
`tv/ExportData.lean`) equals the object's bytes there.

## Expected output

The last lines of a passing run:

```
== CI summary
build       ok
axioms      ok
tv          ok
a2          ok
heartbeats  ok
srcscan     ok
regen       ok
tcb         ok
ci: exit 0
```

`tv` prints one line per program (39 programs, `findings=0 link=0`), `mutation m1` … `m12:
caught`, and `tv: exit 0`. Exit status 1 means a check failed; 2 means a setup problem
(objects missing or different, stale oleans).

## Why `Kraken.lean` does not import the proof

`Kraken.lean` (the default `lake build` target) does not import `Apply`, `Link` or `Witness`.
The Apply proof is split into about 35 shards, several of which need 8–9.5 GB each; the
default parallel build would run them together and exhaust memory. `ci.sh` builds the
whole proof, module by module.

## Optional: checking against a real binary

Off by default; the steps above and their output do not change. `SBR_REAL=1` adds a step
`real` (`real/check.sh`) that proves and checks the placement of the texts in a linked
executable:

```
SBR_REAL=1 SBR_BIN=/path/to/ffmpeg SBR_OBJ_DIR=… LLVM_BIN=… scripts/sbr/ci.sh
```

**The binary.** The FFmpeg 8.1 `ffmpeg` executable (x86-64 PIE, not stripped) of the same
optimized build as the objects above (same sources and compiler flags): it links
`aacsbr.o`, `sbrdsp.o` and `float_dsp.o` unchanged. The six C procedures are byte-identical
to `aacsbr.rela.o`, and the texts of `sbrdsp.o` and `float_dsp.o` to the binary's, outside
relocation fields. Its hash
is in `baseline/binary.sha256`. It is not in the repository; `SBR_BIN` points at it (with
`SBR_REAL=1` and no `SBR_BIN` the step fails).

**The Lean side** is the library `KrakenSbrReal` (`KrakenSbrReal/`, its own `lean_lib`, not
a default target; nothing in `Kraken/` imports it):

- `RealData.lean`, generated by `real/gen.py` from the binary and the texts `tv/Export.lean`
  prints: the address range from the QMF windows to `_GLOBAL_OFFSET_TABLE_` in address order
  (the twenty-six texts at their symbols, one cell per constant, string, callee and the GOT at
  the address the binary's instructions encode, labelled gaps between), with the size of
  every cell (the binary's instruction lengths).
- `Real.lean`: `rCE b` (that image at load bias `b`); `rPlaced b : SbrPlaced` for every `b`;
  `ff_aac_sbr_apply_real` (the linked theorem under `rCE b`, `SbrPlaced` discharged);
  `rlab_*` (each constant at `b` plus its link-time address); `rLab` (`LabAligned` for every
  page-aligned `b`); `rCst` and `real_hyps_sat_{sce,ps,cpe,a3}` under `rCE 0`.

**The check** (`real/check.sh`): the binary's hash; `gen.py`'s output equals the checked-in
`RealData.lean`; `lake build KrakenSbrReal` (and a source scan of it); `real/Ax.lean` equals
`baseline/axioms_real.txt`; `real/RealExport.lean` prints every cell of `rCE 0` with its
address, and `real/check.py` re-assembles every instruction there (llvm-mc, relocations
resolved against the Lean label addresses) and requires the binary's bytes, the binary's
instruction length as the cell size, the texts at their symbols, every referenced constant
pinned by an instruction, and the constants' values; finally four edits of the export must
each be caught. Adding a text: one entry in `real/real_lib.py`'s `TEXTS` and one in
`Real.rTexts`, then regenerate `RealData.lean` with `gen.py`.

`SbrSlots` stays a hypothesis: the slots are written at run time by the initialisation code.

## Line counts

`python3 scripts/sbr/loc.py [BASE [HEAD]] [--json FILE]` counts the Lean lines added between
`BASE` (default `28ca345`, the commit before the SBR work) and `HEAD`, by purpose: block
proofs, label tables and definitions, helper lemmas, program texts, procedure `spec`
compositions, proof-local tactics, comments; the headline files; the library (hand-written,
added to existing files, generated rules); tests; tooling. Each line of a new file is
attributed to the top-level declaration it belongs to. It needs only git and Python, and does
not build anything. The document's "Development effort" table is taken from its output.

## The `ff_aac_sbr_apply` generator

`ApplyTable.lean`, `Apply.lean` and `Apply/*.lean` are generated by `apply/gen.py`; edit its
inputs and regenerate (`python3 scripts/sbr/apply/gen.py`, writing into
`Kraken/X64/Examples/Sbr/`; `APPLY_OUT=<dir>` writes elsewhere). `ApplySpec.lean` is
hand-written and not generated. Inputs:

- `body.s`, `blocks.json`: the text cut into 434 blocks, by `apply/cut.py` from the
  disassembly `ff_aac_sbr_apply.s` and its relocation notes (`APPLY_PROG_DIR`);
- `templates/{head_table,mid,tail}.lean.in`: the fixed parts of `ApplyTable.lean`;
- `spec/<Shard>.py`: entry assertions and frames per block (`define(g)`);
- `override/<block>.lean`: the proof of each block (`theorem blk_<block>`);
- `lemmas/<Shard>.lean`, `lemmas/_table.lean`: shard helper lemmas and table lemmas;
- `../baseline/hb_table.txt`: per-block `maxHeartbeats`.

`gen.py`'s docstring lists the environment switches. The `regen` CI step checks that the
checked-in files are exactly the generator's output.

## The `sbr_hf_assemble` generator

`HfAssemble.lean` and `HfAssemble/{Base,Part1,Part2}.lean` are generated by `hfasm/build.sh`
(`gen.py`, then `split.py`, which balances the block theorems over the parts by the
heartbeats in `hfasm/hb_table.txt`); `HfAssemble/Cells.lean` is hand-written. Inputs:

- `body.s`: the text cut into 116 blocks, by `hfasm/mkbody.py` from the disassembly
  `sbr_hf_assemble.s` (`HFASM_PROG_DIR`);
- `spec.lean.in`, `proof_head.lean.in`: the fixed parts (the footprint and specification, the text);
- `spec_hf.py` (with `mregion.py`, `skel.py`): label assertions, frames, the generic block proofs;
- `override/<block>.lean`, `override/_lemmas.lean`, `lb01d_dev.lean`, `dev2.lean`: hand-written
  block proofs and lemmas;
- `hb_table.txt`: `<block> <measured> <budget>`; the budget becomes the block's `maxHeartbeats`.

`build.sh` writes into `Kraken/X64/Examples/Sbr/` (`HFASM_OUT` elsewhere; its header lists
the switches). The `regen` CI step checks that the checked-in files are its output.

## How to prove a parser routine

The parser proofs (`Kraken/X64/Examples/Sbr/Parse/`) share a library:

| file | contents |
|---|---|
| `Parse/Lib.lean` | havoc rules for values that are never needed (`bswap32_havoc`, `shl_cl32_havoc`, `shr_cl32_havoc`, `shr_cl8_havoc`), `shl_cl64_val`, `get64_ite`; byte lists (`bsplit`, `bmerge`, `getD_set_*`); focus (`focus`, `pick_*`, `eq_*`, `Hide`); cell access (`cell4_load`/`cell4_store`, `cell1_*`, `cell8_*`, `slot_load`/`slot_store`, `blocks_load`); `lt4_cases`, `zx8`, `sub_add_lit`; `jt_target`; the `cells_grind` tactic |
| `Parse/LibGb.lean` | `GetBitContext`: `GbW`, `GbC`, `gb_load_buf`/`gb_load_idx`/`gb_load_p8`, `gb_store_idx`, `rd_off`, `shr30_lt`/`shr_lt`/`shr7_lt`, `gb_clamp`/`gb_clamp64` (the index update of `get_bits`) |
| `Parse/LibAbort.lean` | `ProcSpecA` (a run returns or reaches `abort`), `ProcSpec.toA`, `call_procA_spec_at`, `call_abort_at`, `ProcSpecA.of_cfg_post` |
| `Parse/LibCall.lean` | callee contracts with values (`MemcpyValSpec`, `MemsetValSpec`) |
| `scripts/sbr/parse/focus.py` | writes a routine's footprint `T`, its opaque cell groups, one AC equation per focus target and the access lemmas, from a layout (`scripts/sbr/parse/layouts/grid.py` writes `Parse/GridFoot.lean`) |

The recipe (the `read_sbr_grid` files are the worked example):

1. Text. Extract the routine with `to_program`, name the `0x0(%rip)` operands from the
   relocations, and cut the text into blocks of at most about ten instructions, two stores and one
   conditional exit for unrolled code (`scripts/sbr/grid/gen.py`, its `CUTS`). A bit read (`get_bits`)
   is one block or the head of one.
2. Spec. Logical variables (`GArgs`), the state between blocks (`GSt`: the fields the routine
   writes, as cells), the footprint (`GF`), the side conditions (`GridC`), `Pre`/`Post` as
   `CallPre`/`CallPost`. A routine that can reach `abort` gets a `ProcSpecA`.
3. Footprint. Write the layout and run `focus.py`: every struct region is an opaque `def` (one atom
   for `simp`/`grind`), byte arrays are one 1-byte cell per element, and every cell a block touches
   has a focus equation `T_x : T … = X ⋆ Tx …` and access lemmas (`T_storeN`, `T_loadTe`, `T_storeTeO`, …).
4. Table. One assertion per label: the registers the later blocks read, `∃ st,` an invariant of
   `st`, `s.dmem =⋆ T … st`. Loops need a progress clause in `var` (a back edge must decrease it).
   Error returns reached from inside a body need an invariant that implies the postcondition
   there (for `read_sbr_grid`: `SInv`, which holds on every edge into an error path).
   A large table is a match on the label's Nat key (`lkey "f.Lxxxx"` patterns, `labKey`), with
   `def table l s := tableK (labKey l) s` and dsimprocs that reduce a lookup at a literal label
   (`reduceTable`/`reduceVar` in `Parse/GridBase.lean`); a match on `String` literals costs
   ~0.4 M heartbeats per compared label.
5. Blocks. `cfg_block`, `measure_hb`, `Triple.pin`, destructure the entry assertion; derive the
   memory facts the block needs from the access lemmas *before* `vcgen` (stores as functions of the
   stored value: `have hs := fun v => T_storeN hm v`); hide the footprint (`have hmT : Hide _ := hm`,
   `clear hm`) and register facts (`PLift`); `vcgen [havoc rules]`; normalize; close each VC with
   the prepared facts (`with_reducible exact`), the table goals with `Table.ofLabels_at` then
   `dsimp only [reduceTable, reduceVar]`, the edge order with `edge_lt`, a jump to a trap with
   `exfalso`.
6. Assembly. `scripts/sbr/grid/asm.py BODY.s` writes `Parse/GridAsm.lean`: the whole-routine
   `ProcSpecA` from the proved block theorems and a structure `GridOpen` whose fields are the
   open obligations; add a block to `PROVED`/`SMP` when it is proved and regenerate.

Rules (measured on `read_sbr_grid`):

1. Never `grind` over a whole footprint: ~50 cells cost 0.3–2 M heartbeats per block or fail. Focus
   (an AC equation plus one access lemma) costs a few thousand.
2. A variable-index access is never split inside a block: use the array lemma that takes the
   index as a parameter (the split is paid once, in the lemma).
3. Keep big hypotheses away from `simp … at *` (`Hide`, `PLift`): it rewrites them (it turned a
   register fact into `True` through another register equation).
4. Never leave `all_goals try grind` over goals that include the `Table.ofLabels` disjunctions: a
   failing `grind` burns its whole budget. Target the VCs (`case vcN => …`).
5. Cut blocks rather than raise `maxHeartbeats` (no options in `Parse/`): an unrolled 44-instruction
   block did not close at 420 k heartbeats.

Pitfalls:

* Inaccessible names after `vcgen` need `rename_i`.
* `exact h` against a goal that matches only up to unfolding `storeInt`/`loadInt` can hit the
  recursion limit, and `try` does not catch it: use `with_reducible exact`.
* `decide` on a consistent flag hypothesis recurses instead of failing: normalize with
  `simp only [CondCode.interp, StatusFlags.from_result, BitVec.reduce…]` and require `done`.
* `simp (config := {decide := true}) at *` times out on block goals.
* `grind` does not identify `d + 1 + 12` with `d + 13`: normalize offsets first (`BitVec.add_assoc`,
  `BitVec.reduceAdd`, `sub_add_lit` for the stack slots after pops).
* `Blocks` must be at the head of a focused hypothesis for its lemmas (`T_blocks`).
