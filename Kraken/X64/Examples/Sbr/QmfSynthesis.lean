import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.IndirectCall
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat
import Kraken.Rules.CallFrame
import Kraken.Rules.CfgList
import Kraken.Rules.LeafLemmas
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.QmfSynthesisText

/-!
# `sbr_qmf_synthesis` as a `ProcSpec` (scaling probe)

**Notes** (the scaling probe for `ff_aac_sbr_apply`).

`sbr_qmf_synthesis` from the `-c opt` object: 284 instructions, 33 cut
labels (one after every call, and 7 inside the prologue's run of stores),
16 indirect calls (`sbrdsp->*`, `fdsp->*`,
`mdct_fn`) and one `call memcpy`. The proof is `ProcSpec.of_cfg_post` over
an invariant `table` per `div = d`. Its three parts:

* `hblocks`: 33 block goals, one theorem `blk_<label>` each (below);
* `hpre`: the precondition into the entry invariant;
* `hpost`: the exit invariant into the postcondition.

Status: all 33 blocks, `hpre` and `hpost` are proved; no `sorry`. The five
blocks that stayed open longest, and what closed them:

* `entry`, the prologue (98 instructions, about 40 stores into the frame):
  cut into 8 blocks by 7 labels (`.e1` … `.e7`), each with a `<blk>_pre`/
  `_post` lemma that puts the cells it touches in front of one `Mem.Hid` atom.
  The rule for `shr %cl` that sets `zf`/`sf`/`pf` grows the state as 4^k after
  k shifts; the opt-in flags-forgetting rules of
  `Kraken.Rules.IntMisc.ShiftClOpaque` keep it linear. `d ∈ {0,1}` is split
  before `vcgen`.
* `L9fd2`, the `jge` after a signed 32-bit `cmp`:
  `CondCode.interp_ge_cmp_toInt32`, then explicit terms (no `grind`).
* `lend` and `L9ff9`, the `*v_off` cell read back as a signed `int` and
  related to `v` across the back edge: `BitVec.cltq_lea_bridge` and the
  `int`↔`Nat` lemmas of `Kraken.Rules.FrameLemmas`; jump goals through
  `Table.ofLabels_at`; address equations as closed lemmas (never `bv_omega`
  in a block context).
* `.ds`, 33 straight-line vector instructions: the accessed blocks carved into
  one `Blocks` list, the rest generalized to one atom, the postcondition
  weakened (`Triple.post_imp`), stored values made opaque (`opaque_stores`),
  and `offset64`/`Int64` literals normalised before `grind`.

Recipe (each point fixed a timeout or a failure):

* **Opaque regions.** A memory invariant with about 70 cells is out of reach
  for `grind`. Each region a block does not touch is an opaque `def`:
  `DataW` (the data), `FnsW` (the function-pointer slots), `ArgsW` (the stack
  arguments), `BlankLW` (the forgotten frame). Each has an `_open` lemma,
  used only in the blocks that access the region. Wrappers stay closed (no
  continuation inside).
* **Lists end in a continuation.** `Locals … CC Tl`, `Saved t₀ K` and
  `BlankL r K` all take one. `Split.at_val` only finds a cell that is the
  left child of a `⋆`.
* **`grind_cells'`** is `grind` with `(mbtc := false)`: with model-based
  theory combination on, `grind` spends its case splits equating the saved
  registers' values.
* **`qmf_norm`** splits `d ∈ {0,1}`, then `dsimp`s the `{regs := …}.regs`
  projections, then reduces the `Nat` literals. Before it, one load took
  10 minutes; after, 1.5 s.
* **Call blocks** (`qmf_call`, `qmf_callA`, `qmf_fblock`):
  * `Triple.pin` fixes the entry state;
  * the callee's `x` is literal: (the data region, the rest of the tree);
  * `Mem.push_slot_res` discharges the memory side;
  * one carve lemma per callee footprint shape (`DataW_carve_*`), with its
    bounds by `grind`;
  * after the call, `vcgen; grind_cells'`.
* **Stack arguments**: `T` only appears after `vcgen` reduces the table's
  `match`, so `ArgsW` is opened after `vcgen`, or in the memory fact before
  a call (`qmf_callA`).

Cost: each block is its own theorem with its own `maxHeartbeats` (about 1.5×
its measured cost; none where the default 200000 suffices), so the blocks
elaborate in parallel. The frame-slot loads are discharged by read facts
stated before `vcgen` (section "F6 slot reads"), the prologue stores by a
store chain stated before `vcgen` (section "Stage 2 store threading").
Measured per block (`measure_hb`), in heartbeats:

* `ret` 60 M, the epilogue 110 M;
* the prologue pieces 70–230 M;
* the other blocks 90–360 M;
* a `vector_fmul(_add)` or `memcpy` call 170–210 M;
* `lend` 170 M.

In total about 5.8 G heartbeats: about 1.5 min of wall time for the file.

The added side conditions are those of `QmfC`, the bounds on `*v_off` and
the callees' contracts as assumed in `QmfCallees`.

`*v_off`. `QmfC` only bounds the entry value by 1664 (with any `div`). The
loop head keeps it at most `vhi d off` (see `vhi`; normally the reset value
`2304 - (1152 >> div)`, aacsbr_template.c:1427-1432), since between resets the
value only decreases. The window reads from `v = v0 + 4 (*v_off - (128 >> div))`
end at most `4 vhi + 4 (1152 >> div)` bytes into `v0`: exactly `qmfVSize d off`
(`vsz`, `vfacts`). The writes into `v0`
(`qmf_deint_bfly`/`qmf_deint_neg` at `v`, at most 6656 bytes in, and the
`memcpy`) stay inside its first 9216 bytes. The `av_tx` context and tables
travel together as one context `CT Ctx TxTab` (`QmfCallees'`).
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.FrameLemmas.Int32Nat Kraken.Rules.IntMisc.ShiftClOpaque

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.QmfSynthesis


variable [CodeEnv]

abbrev K (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

/-- The caller's memory behind the footprint: the return address and `R`. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The 31 spill slots `-0x120(%rbp)` … `-0x30(%rbp)` (`rbp = rsp₀ - 8`) with
the values the prologue stores; `CC` is the loop counter's slot. -/
abbrev Locals (d : Nat) (x : QmfArgs) (t₀ : MachineData) (CC Tl : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  let w := qmfWin d
  CC
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (c8 (r - 0x118#64) (w)
    ⋆ (c8 (r - 0x110#64) (K (128 / 2 ^ d))
    ⋆ (c8 (r - 0x108#64) (K (64 / 2 ^ d))
    ⋆ (c8 (r - 0x100#64) (K (192 / 2 ^ d))
    ⋆ (c8 (r - 0xf8#64) (K (256 / 2 ^ d))
    ⋆ (c8 (r - 0xf0#64) (K (448 / 2 ^ d))
    ⋆ (c8 (r - 0xe8#64) (K (512 / 2 ^ d))
    ⋆ (c8 (r - 0xe0#64) (K (704 / 2 ^ d))
    ⋆ (c8 (r - 0xd8#64) (w + K (4 * (320 / 2 ^ d)))
    ⋆ (c8 (r - 0xd0#64) (K (768 / 2 ^ d))
    ⋆ (c8 (r - 0xc8#64) (K (960 / 2 ^ d))
    ⋆ (c8 (r - 0xc0#64) (K (1024 / 2 ^ d))
    ⋆ (c8 (r - 0xb8#64) (K (1216 / 2 ^ d))
    ⋆ (c8 (r - 0xb0#64) (w + K (4 * (384 / 2 ^ d)))
    ⋆ (c8 (r - 0xa8#64) (w + K (4 * (576 / 2 ^ d)))
    ⋆ (c8 (r - 0xa0#64) (K (4 * (64 / 2 ^ d)))
    ⋆ (c8 (r - 0x98#64) (w + K (4 * (64 / 2 ^ d)))
    ⋆ (c8 (r - 0x90#64) (w + K (4 * (128 / 2 ^ d)))
    ⋆ (c8 (r - 0x88#64) (w + K (4 * (192 / 2 ^ d)))
    ⋆ (c8 (r - 0x80#64) (w + K (4 * (256 / 2 ^ d)))
    ⋆ (c8 (r - 0x78#64) (w + K (4 * (448 / 2 ^ d)))
    ⋆ (c8 (r - 0x70#64) (w + K (4 * (512 / 2 ^ d)))
    ⋆ (c8 (r - 0x68#64) (K (4 * (1152 / 2 ^ d)))
    ⋆ (c8 (r - 0x60#64) (K (2304 - 1152 / 2 ^ d))
    ⋆ (c8 (r - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d)))
    ⋆ (c8 (r - 0x50#64) (x.mdctBuf + 256#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Tl))))))))))))))))))))))))))))))

/-- The six saved registers. -/
abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K)))))

abbrev BlankL (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (8 ?@ (r - 0xa8#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (8 ?@ (r - 0x48#64)
    ⋆ (8 ?@ (r - 0x40#64)
    ⋆ (8 ?@ (r - 0x38#64) ⋆ K))))))))))))))))))))))))))))))

abbrev BlankS (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x30#64)
    ⋆ (8 ?@ (r - 0x28#64)
    ⋆ (8 ?@ (r - 0x20#64)
    ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64)
    ⋆ (8 ?@ (r - 0x8#64) ⋆ K)))))

/-- The bytes of `v0` in the footprint, `qmfVSize d off`, behind a
name `grind` does not unfold. -/
def vsz (d : Nat) (off : BitVec 32) : Nat := qmfVSize d off

/-- The largest `*v_off` the loop head sees: the reset value `2304 - (1152 >> div)`
(aacsbr_template.c:1427-1432) or, if the entry value is larger, 1664: the value only
decreases until it is reset. -/
def vhi (d : Nat) (off : BitVec 32) : Int :=
  if d = 0 ∧ 1152 < off.toInt then 1664 else 2304 - ((1152 / 2 ^ d : Nat) : Int)

omit [CodeEnv] in
theorem vsz_ge (d : Nat) (off : BitVec 32) : 9216 ≤ vsz d off := by
  unfold vsz qmfVSize; split <;> omega

omit [CodeEnv] in
theorem vsz_le (d : Nat) (off : BitVec 32) : vsz d off ≤ 11264 := by
  unfold vsz qmfVSize; split <;> omega

omit [CodeEnv] in
/-- The entry value of `*v_off` (at most 1664, `QmfC`) is at most `vhi`. -/
theorem off_le_vhi (d : Nat) (off : BitVec 32) (hd : d ≤ 1) (h : off.toInt ≤ 1664) :
    off.toInt ≤ vhi d off := by
  unfold vhi
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · by_cases hc : 1152 < off.toInt
    · simp -implicitDefEqProofs only [hc, and_self, ite_true]; omega
    · simp -implicitDefEqProofs only [hc, and_false, ite_false]; omega
  · simp -implicitDefEqProofs only [Nat.one_ne_zero, false_and, ite_false]; omega

omit [CodeEnv] in
/-- The arithmetic of the two bounds: the reset value is at most `vhi`; one step
below `vhi` leaves `v` at most 6656 bytes in; the window read from there ends
exactly at `vsz`. -/
theorem vfacts (d : Nat) (off : BitVec 32) (hd : d ≤ 1) :
    2304 - ((1152 / 2 ^ d : Nat) : Int) ≤ vhi d off
    ∧ vhi d off - ((128 / 2 ^ d : Nat) : Int) ≤ 1664
    ∧ (vsz d off : Int) = 4 * vhi d off + 4 * ((1152 / 2 ^ d : Nat) : Int)
    ∧ 128 / 2 ^ d + 1152 / 2 ^ d = 1280 / 2 ^ d := by
  unfold vhi vsz qmfVSize
  obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  · by_cases hc : 1152 < off.toInt
    · rw [if_pos ⟨rfl, hc⟩, if_pos ⟨rfl, hc⟩]; omega
    · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2)]; omega
  · rw [if_neg (fun h => Nat.one_ne_zero h.1), if_neg (fun h => Nat.one_ne_zero h.1)]; omega

omit [CodeEnv] in
/-- `vfacts` at `div = 0`, with literal numbers (for `omega` after `qmf_norm`). -/
theorem vfacts0 (off : BitVec 32) :
    1152 ≤ vhi 0 off ∧ vhi 0 off ≤ 1664 ∧ vsz 0 off = 4 * (vhi 0 off).toNat + 4608 := by
  unfold vhi vsz qmfVSize
  by_cases hc : 1152 < off.toInt
  · rw [if_pos ⟨rfl, hc⟩, if_pos ⟨rfl, hc⟩]; omega
  · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2)]; omega

omit [CodeEnv] in
/-- `vfacts` at `div = 1`, with literal numbers. -/
theorem vfacts1 (off : BitVec 32) : vhi 1 off = 1728 ∧ vsz 1 off = 9216 := by
  unfold vhi vsz qmfVSize
  rw [if_neg (fun h => Nat.one_ne_zero h.1), if_neg (fun h => Nat.one_ne_zero h.1)]
  omega

/-- The `av_tx` context together with the `av_tx` tables: `QmfData'` ends in
`Ctx (arg0 t) ⋆ TxTab`, and `TxF Ctx TxTab` is `Blocks … ⋆ (Ctx (arg0 t) ⋆ TxTab)`, so
the proof below carries the pair as one context `CT Ctx TxTab`. -/
abbrev CT (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) :
    BitVec 64 → Mem 64 → Prop :=
  fun c => Ctx c ⋆ TxTab

/-- `QmfCallees` with the `av_tx` footprint over one context `C` (the blocks'
form; `QmfCallees k Ctx TxTab fs` is `QmfCallees' k (CT Ctx TxTab) fs`). -/
abbrev QmfCallees' (k : Nat) (C : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) : Prop :=
  LeafSpecAt fs.negOdd64 0 NegOdd64F NegOdd64C
    ∧ LeafSpecAt fs.deintNeg 0 QmfDeintNegF QmfDeintNegC
    ∧ LeafSpecAt fs.deintBfly 0 QmfDeintBflyF QmfDeintBflyC
    ∧ LeafSpecAt fs.tx k (fun t => Blocks [(arg1 t, 256), (arg2 t, 256)] ⋆ C (arg0 t)) TxC
    ∧ VectorFmulSpec k fs.fmul ∧ VectorFmulAddSpec k fs.fmulAdd
    ∧ MemcpySpec k

/-- `QmfData`, `QmfArgCells` and the blank slots behind names `grind` does not
unfold: a block that touches none of their cells sees one atom each. -/
def DataW (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) : Mem 64 → Prop :=
  Blocks [(arg5 t, 19456)] ⋆ (256 ?@ x.mdctBuf ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (vsz d x.off ?@ x.v0
    ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ps_mask2" ⋆ (16 ?@ lab "ff_ps_neg" ⋆ Ctx (arg0 t))))))))))

/-- The five function-pointer slots, read-only, outside the data the callees
are handed. -/
def FnsW (fs : QmfFns) (t : MachineData) : Mem 64 → Prop :=
  FnCell (arg2 t + 0x10#64) fs.negOdd64 ⋆ (FnCell (arg2 t + 0x28#64) fs.deintNeg
    ⋆ (FnCell (arg2 t + 0x30#64) fs.deintBfly ⋆ (FnCell (arg3 t) fs.fmul
    ⋆ FnCell (arg3 t + 0x30#64) fs.fmulAdd)))

omit [CodeEnv] in
theorem FnsW_open (fs : QmfFns) (t : MachineData) (K : Mem 64 → Prop) :
    FnsW fs t ⋆ K = FnCell (arg2 t + 0x10#64) fs.negOdd64 ⋆ (FnCell (arg2 t + 0x28#64) fs.deintNeg
      ⋆ (FnCell (arg2 t + 0x30#64) fs.deintBfly ⋆ (FnCell (arg3 t) fs.fmul
      ⋆ (FnCell (arg3 t + 0x30#64) fs.fmulAdd ⋆ K)))) := by
  simp -implicitDefEqProofs only [FnsW, Std.ExtHashMap.sep_assoc]

theorem QmfData_eq (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop)
    (fs : QmfFns) (x : QmfArgs) (t : MachineData) (VC K : Mem 64 → Prop) :
    QmfData d Ctx TxTab fs x t VC ⋆ K
      = DataW d (CT Ctx TxTab) x t Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t ⋆ K)) := by
  simp -implicitDefEqProofs only [QmfData, QmfData', DataW, FnsW, FnCell, CT, vsz, Std.ExtHashMap.sep_assoc,
    Std.ExtHashMap.emp_sep]
  ac_rfl

def ArgsW (d : Nat) (x : QmfArgs) (t : MachineData) : Mem 64 → Prop := QmfArgCells d x t

def BlankLW (r : BitVec 64) : Mem 64 → Prop := BlankL r Std.ExtHashMap.emp

omit [CodeEnv] in
/-- `ArgsW` opened in front of `K`, as a list ending in `K`: the `SepCells`
rules split a tree only at a cell that is the left child of a `⋆`. -/
theorem ArgsW_open (d : Nat) (x : QmfArgs) (t : MachineData) (K : Mem 64 → Prop) :
    ArgsW d x t ⋆ K = Int.toBytes 8 x.mdctBuf.toInt =@ (t.regs.get64 .rsp + 8#64)
      ⋆ (Int.toBytes 8 x.v0.toInt =@ (t.regs.get64 .rsp + 16#64)
      ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t.regs.get64 .rsp + 24#64)
      ⋆ (Int.toBytes 4 (d : Int) =@ (t.regs.get64 .rsp + 32#64) ⋆ K))) := by
  simp -implicitDefEqProofs only [ArgsW, QmfArgCells, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem BlankLW_open (r : BitVec 64) (K : Mem 64 → Prop) : BlankLW r ⋆ K = BlankL r K := by
  simp -implicitDefEqProofs only [BlankLW, BlankL, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.emp_sep]

/-- The memory at every label but the entry and `.ds`: the slot of the
callees' return address, their reservation, the data, the frame, the rest. -/
abbrev T (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs) (ra : Int64)
    (t₀ : MachineData) (VC : Mem 64 → Prop) (FR : (Mem 64 → Prop) → Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x130#64) ⋆ (Reserve k (r - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp
    ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ FR (Rest x.R ra t₀))))))

/-- The frame in the loop: spill slots with the counter `c`, saved registers. -/
abbrev Fr (d : Nat) (x : QmfArgs) (t₀ : MachineData) (CC K : Mem 64 → Prop) : Mem 64 → Prop :=
  Locals d x t₀ CC (Saved t₀ K)

/-- The frame at `.e1`: the spill slots the prologue has written so far (0 of 30), the rest blank, then the saved registers. -/
abbrev FrE1 (_d : Nat) (_x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x128#64)
    ⋆ (8 ?@ (r - 0x120#64)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (8 ?@ (r - 0xa8#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (8 ?@ (r - 0x48#64)
    ⋆ (8 ?@ (r - 0x40#64)
    ⋆ (8 ?@ (r - 0x38#64) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The frame at `.e2`: the spill slots the prologue has written so far (4 of 30), the rest blank, then the saved registers. -/
abbrev FrE2 (_d : Nat) (_x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x128#64)
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (8 ?@ (r - 0xa8#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (8 ?@ (r - 0x68#64)
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The frame at `.e3`: the spill slots the prologue has written so far (5 of 30), the rest blank, then the saved registers. -/
abbrev FrE3 (d : Nat) (_x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x128#64)
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (8 ?@ (r - 0xe0#64)
    ⋆ (8 ?@ (r - 0xd8#64)
    ⋆ (8 ?@ (r - 0xd0#64)
    ⋆ (8 ?@ (r - 0xc8#64)
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (8 ?@ (r - 0xa8#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (K (4 * (1152 / 2 ^ d)))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The frame at `.e4`: the spill slots the prologue has written so far (9 of 30), the rest blank, then the saved registers. -/
abbrev FrE4 (d : Nat) (_x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  let w := qmfWin d
  8 ?@ (r - 0x128#64)
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (c8 (r - 0xe0#64) (K (704 / 2 ^ d))
    ⋆ (c8 (r - 0xd8#64) (w + K (4 * (320 / 2 ^ d)))
    ⋆ (c8 (r - 0xd0#64) (K (768 / 2 ^ d))
    ⋆ (c8 (r - 0xc8#64) (K (960 / 2 ^ d))
    ⋆ (8 ?@ (r - 0xc0#64)
    ⋆ (8 ?@ (r - 0xb8#64)
    ⋆ (8 ?@ (r - 0xb0#64)
    ⋆ (8 ?@ (r - 0xa8#64)
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (K (4 * (1152 / 2 ^ d)))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The frame at `.e5`: the spill slots the prologue has written so far (13 of 30), the rest blank, then the saved registers. -/
abbrev FrE5 (d : Nat) (_x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  let w := qmfWin d
  8 ?@ (r - 0x128#64)
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (8 ?@ (r - 0x108#64)
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (c8 (r - 0xe0#64) (K (704 / 2 ^ d))
    ⋆ (c8 (r - 0xd8#64) (w + K (4 * (320 / 2 ^ d)))
    ⋆ (c8 (r - 0xd0#64) (K (768 / 2 ^ d))
    ⋆ (c8 (r - 0xc8#64) (K (960 / 2 ^ d))
    ⋆ (c8 (r - 0xc0#64) (K (1024 / 2 ^ d))
    ⋆ (c8 (r - 0xb8#64) (K (1216 / 2 ^ d))
    ⋆ (c8 (r - 0xb0#64) (w + K (4 * (384 / 2 ^ d)))
    ⋆ (c8 (r - 0xa8#64) (w + K (4 * (576 / 2 ^ d)))
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (K (4 * (1152 / 2 ^ d)))
    ⋆ (8 ?@ (r - 0x60#64)
    ⋆ (8 ?@ (r - 0x58#64)
    ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The frame at `.e6`: the spill slots the prologue has written so far (17 of 30), the rest blank, then the saved registers. -/
abbrev FrE6 (d : Nat) (x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  let w := qmfWin d
  8 ?@ (r - 0x128#64)
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (c8 (r - 0x108#64) (K (64 / 2 ^ d))
    ⋆ (8 ?@ (r - 0x100#64)
    ⋆ (8 ?@ (r - 0xf8#64)
    ⋆ (8 ?@ (r - 0xf0#64)
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (c8 (r - 0xe0#64) (K (704 / 2 ^ d))
    ⋆ (c8 (r - 0xd8#64) (w + K (4 * (320 / 2 ^ d)))
    ⋆ (c8 (r - 0xd0#64) (K (768 / 2 ^ d))
    ⋆ (c8 (r - 0xc8#64) (K (960 / 2 ^ d))
    ⋆ (c8 (r - 0xc0#64) (K (1024 / 2 ^ d))
    ⋆ (c8 (r - 0xb8#64) (K (1216 / 2 ^ d))
    ⋆ (c8 (r - 0xb0#64) (w + K (4 * (384 / 2 ^ d)))
    ⋆ (c8 (r - 0xa8#64) (w + K (4 * (576 / 2 ^ d)))
    ⋆ (8 ?@ (r - 0xa0#64)
    ⋆ (8 ?@ (r - 0x98#64)
    ⋆ (8 ?@ (r - 0x90#64)
    ⋆ (8 ?@ (r - 0x88#64)
    ⋆ (8 ?@ (r - 0x80#64)
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (K (4 * (1152 / 2 ^ d)))
    ⋆ (c8 (r - 0x60#64) (K (2304 - 1152 / 2 ^ d))
    ⋆ (c8 (r - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d)))
    ⋆ (c8 (r - 0x50#64) (x.mdctBuf + 256#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The frame at `.e7`: the spill slots the prologue has written so far (25 of 30), the rest blank, then the saved registers. -/
abbrev FrE7 (d : Nat) (x : QmfArgs) (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  let w := qmfWin d
  8 ?@ (r - 0x128#64)
    ⋆ (c8 (r - 0x120#64) (arg3 t₀)
    ⋆ (8 ?@ (r - 0x118#64)
    ⋆ (8 ?@ (r - 0x110#64)
    ⋆ (c8 (r - 0x108#64) (K (64 / 2 ^ d))
    ⋆ (c8 (r - 0x100#64) (K (192 / 2 ^ d))
    ⋆ (c8 (r - 0xf8#64) (K (256 / 2 ^ d))
    ⋆ (c8 (r - 0xf0#64) (K (448 / 2 ^ d))
    ⋆ (8 ?@ (r - 0xe8#64)
    ⋆ (c8 (r - 0xe0#64) (K (704 / 2 ^ d))
    ⋆ (c8 (r - 0xd8#64) (w + K (4 * (320 / 2 ^ d)))
    ⋆ (c8 (r - 0xd0#64) (K (768 / 2 ^ d))
    ⋆ (c8 (r - 0xc8#64) (K (960 / 2 ^ d))
    ⋆ (c8 (r - 0xc0#64) (K (1024 / 2 ^ d))
    ⋆ (c8 (r - 0xb8#64) (K (1216 / 2 ^ d))
    ⋆ (c8 (r - 0xb0#64) (w + K (4 * (384 / 2 ^ d)))
    ⋆ (c8 (r - 0xa8#64) (w + K (4 * (576 / 2 ^ d)))
    ⋆ (c8 (r - 0xa0#64) (K (4 * (64 / 2 ^ d)))
    ⋆ (c8 (r - 0x98#64) (w + K (4 * (64 / 2 ^ d)))
    ⋆ (c8 (r - 0x90#64) (w + K (4 * (128 / 2 ^ d)))
    ⋆ (c8 (r - 0x88#64) (w + K (4 * (192 / 2 ^ d)))
    ⋆ (c8 (r - 0x80#64) (w + K (4 * (256 / 2 ^ d)))
    ⋆ (8 ?@ (r - 0x78#64)
    ⋆ (8 ?@ (r - 0x70#64)
    ⋆ (c8 (r - 0x68#64) (K (4 * (1152 / 2 ^ d)))
    ⋆ (c8 (r - 0x60#64) (K (2304 - 1152 / 2 ^ d))
    ⋆ (c8 (r - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d)))
    ⋆ (c8 (r - 0x50#64) (x.mdctBuf + 256#64)
    ⋆ (c8 (r - 0x48#64) (arg1 t₀)
    ⋆ (c8 (r - 0x40#64) (arg0 t₀)
    ⋆ (c8 (r - 0x38#64) (arg2 t₀) ⋆ Saved t₀ Kt))))))))))))))))))))))))))))))

/-- The row offset `i * 256` of the loop, read off `rbx = X + j`. -/
abbrev jOf (t₀ s : MachineData) : Nat := (s.regs.get64 .rbx - arg5 t₀).toNat

/-- The counter slot holds `32 - i`. -/
abbrev Ctr (t₀ s : MachineData) : Mem 64 → Prop :=
  c8 (t₀.regs.get64 .rsp - 0x128#64) (K (32 - jOf t₀ s / 256))

/-- Registers in the loop: the frame, `rbx = X + 256 i`, `r14 = out + (256 >> d) i`. -/
abbrev LoopRegs (d : Nat) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x128#64 ∧ s.regs.get64 .rbp = r - 8#64
    ∧ jOf t₀ s % 256 = 0 ∧ jOf t₀ s < 8192
    ∧ s.regs.get64 .r14 = arg4 t₀ + K (jOf t₀ s / 2 ^ d)

/-- `v = r13`, its byte offset into `v0`. -/
abbrev vbOf (x : QmfArgs) (s : MachineData) : Nat := (s.regs.get64 .r13 - x.v0).toNat

abbrev VInv (d : Nat) (x : QmfArgs) (s : MachineData) : Prop :=
  vbOf x s % 32 = 0 ∧ vbOf x s + 4 * (1280 / 2 ^ d) ≤ vsz d x.off ∧ vbOf x s ≤ 6656

/-- `*v_off` after the update: `(v - v0) / 4`. -/
abbrev VCell (x : QmfArgs) (s : MachineData) : Mem 64 → Prop :=
  Int.toBytes 4 ((vbOf x s / 4 : Nat) : Int) =@ x.vOff

/-- `*v_off` at the loop head, as the cell holds it. -/
abbrev vo (x : QmfArgs) (s : MachineData) : Int := (Mem.loadInt s.dmem x.vOff 4).getD 0

/-- What the loop head needs of `*v_off` (as a signed `int`). -/
abbrev VOffOk' (d : Nat) (off : BitVec 32) (c : Int) : Prop :=
  (BitVec.ofInt 32 c).toInt ≤ vhi d off
    ∧ (BitVec.ofInt 32 c).toNat % 8 = 0

/-- What the loop head needs of `*v_off`. -/
abbrev VOffOk (d : Nat) (o : Option Int) : Prop :=
  ∀ w, o = some w → (BitVec.ofInt 32 w).toInt ≤ 2304 - ((1152 / 2 ^ d : Nat) : Int)
    ∧ (BitVec.ofInt 32 w).toNat % 8 = 0

/-- The table at `div = d`. -/
abbrev table (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "sbr_qmf_synthesis", s => s = t₀ ∧ QmfC d fs x t₀
      ∧ (t₀.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff)
          (fun K => BlankL (t₀.regs.get64 .rsp) (BlankS (t₀.regs.get64 .rsp) K)))
  | "sbr_qmf_synthesis.e1", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = arg5 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE1 d x t₀))
  | "sbr_qmf_synthesis.e2", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE2 d x t₀))
  | "sbr_qmf_synthesis.e3", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE3 d x t₀))
  | "sbr_qmf_synthesis.e4", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d) ∧ s.regs.get64 .rax = K (384 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE4 d x t₀))
  | "sbr_qmf_synthesis.e5", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE5 d x t₀))
  | "sbr_qmf_synthesis.e6", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE6 d x t₀))
  | "sbr_qmf_synthesis.e7", s => QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d) ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE7 d x t₀))
  | "sbr_qmf_synthesis.L9fd2", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s
      ∧ s.regs.get64 .rax = K (32 - jOf t₀ s / 256) ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ VOffOk' d x.off (vo x s)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 (vo x s) =@ x.vOff)
          (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))))
  | "sbr_qmf_synthesis.mc", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s
      ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (4 ?@ x.vOff) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.mc1", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s
      ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (4 ?@ x.vOff) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.L9ff9", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s
      ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ ((128 / 2 ^ d : Nat) : Int) ≤ ((s.regs.get64 .rax).setWidth 32).toInt
      ∧ ((s.regs.get64 .rax).setWidth 32).toInt ≤ vhi d x.off
      ∧ ((s.regs.get64 .rax).setWidth 32).toNat % 8 = 0
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (4 ?@ x.vOff) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.L9df0", s => d = 0 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.c1", s => d = 0 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.c2", s => d = 0 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r15 = arg1 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.c3", s => d = 0 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = x.mdctBuf + 256#64
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.L9e42", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f1", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f2", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f3", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f4", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f5", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f6", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f7", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f8", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.f9", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = K (64 / 2 ^ d) ∧ s.regs.get64 .r15 = arg3 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.lend", s => QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.ds", s => d = 1 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.ds1", s => d = 1 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.ds2", s => d = 1 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ s.regs.get64 .r12 = x.mdctBuf
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.ds3", s => d = 1 ∧ QmfC d fs x t₀ ∧ LoopRegs d t₀ s ∧ VInv d x s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VCell x s) (Fr d x t₀ (Ctr t₀ s)))
  | "sbr_qmf_synthesis.La125", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VOffW x.vOff)
          (fun K => BlankLW (t₀.regs.get64 .rsp) ⋆ Saved t₀ K))
  | "sbr_qmf_synthesis.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (VOffW x.vOff)
          (fun K => BlankLW (t₀.regs.get64 .rsp) ⋆ Saved t₀ K))
  | _, _ => False

/-- The loop counter, as the slot `-0x120(%rbp)` holds it. -/
abbrev ctr (s : MachineData) : Nat :=
  (BitVec.ofInt 64 ((Mem.loadInt s.dmem (s.regs.get64 .rbp - 0x120#64) 8).getD 0)).toNat

/-- The variant: `3 c` from the loop head to the `div` test and on the
downsampled path, `3 c - 1` behind the two back edges (`je .L9df0`,
`jmp .L9e42`), 0 at the exit. -/
abbrev var : Label → MachineData → Nat
  | "sbr_qmf_synthesis.L9fd2", s => 3 * (s.regs.get64 .rax).toNat
  | "sbr_qmf_synthesis.mc", s => 3 * ctr s
  | "sbr_qmf_synthesis.mc1", s => 3 * ctr s
  | "sbr_qmf_synthesis.L9ff9", s => 3 * ctr s
  | "sbr_qmf_synthesis.ds", s => 3 * ctr s
  | "sbr_qmf_synthesis.ds1", s => 3 * ctr s
  | "sbr_qmf_synthesis.ds2", s => 3 * ctr s
  | "sbr_qmf_synthesis.ds3", s => 3 * ctr s
  | "sbr_qmf_synthesis.L9df0", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.c1", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.c2", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.c3", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.L9e42", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f1", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f2", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f3", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f4", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f5", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f6", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f7", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f8", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.f9", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.lend", s => 3 * ctr s - 1
  | "sbr_qmf_synthesis.La125", _ => 0
  | "sbr_qmf_synthesis.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves. -/
abbrev Post' (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (_ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ 8 ?@ (r - 0x130#64) ⋆ (Reserve k (r - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp
    ⋆ (VOffW x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (BlankLW r ⋆ Saved t₀ (8 ?@ r ⋆ x.R))))))))

/-- `grind_cells` without model-based theory combination: on a frame of
many `Int.toBytes 8 v =@ a` cells it spends its case splits equating the
values of distinct saved registers. -/
macro "grind_cells'" : tactic =>
  `(tactic| ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod]))

/-- The footprint of `vector_fmul`/`vector_fmul_add` as `sbr_qmf_synthesis`
calls them (an `out` row, a stretch of `v`, a stretch of the window) inside
the data. -/
theorem DataW_carve_fmul (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (o v w : BitVec 64) (n : Nat)
    (ho : (o - arg4 t).toNat + n ≤ 8192 >>> d) (hv : (v - x.v0).toNat + n ≤ vsz d x.off)
    (hw : (w - qmfWin d).toNat + n ≤ 2560 >>> d) :
    ∃ H, DataW d Ctx x t VC = Blocks [(o, n), (v, n), (w, n)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex ho (by have := Nat.shiftRight_le 8192 d; omega)
  obtain ⟨H2, e2⟩ := Block.carve_ex hv (by have := vsz_le d x.off; omega)
  obtain ⟨H3, e3⟩ := Block.carve_ex hw (by have := Nat.shiftRight_le 2560 d; omega)
  refine ⟨Blocks [(arg5 t, 19456)] ⋆ (256 ?@ x.mdctBuf ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (H2
    ⋆ (VC ⋆ (H1 ⋆ (H3 ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ps_mask2" ⋆ (16 ?@ lab "ff_ps_neg" ⋆ Ctx (arg0 t)))))))))), ?_⟩
  rw [DataW, e1, e2, e3]
  simp -implicitDefEqProofs only [Blocks]
  ac_rfl

/-- `neg_odd_64`'s footprint (a row of `X`, `ps_mask2`) inside the data. -/
theorem DataW_carve_negodd (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (o : BitVec 64)
    (ho : (o - arg5 t).toNat + 256 ≤ 19456) :
    ∃ H, DataW d Ctx x t VC = Blocks [(o, 256), (lab "ps_mask2", 16)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex ho (by omega)
  refine ⟨H1 ⋆ (256 ?@ x.mdctBuf ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (vsz d x.off ?@ x.v0
    ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ff_ps_neg" ⋆ Ctx (arg0 t))))))))), ?_⟩
  simp -implicitDefEqProofs only [DataW, Blocks]
  rw [e1]
  ac_rfl

/-- `av_tx`'s footprint (one half of `mdct_buf`, a row of `X`, the context)
inside the data; `hi` picks the upper half. -/
theorem DataW_carve_tx (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (hi : Bool) (b o c : BitVec 64)
    (hb : b = if hi then x.mdctBuf + 256#64 else x.mdctBuf)
    (ho : (o - arg5 t).toNat + 256 ≤ 19456) (hc : c = arg0 t) :
    ∃ H, DataW d Ctx x t VC = (Blocks [(b, 256), (o, 256)] ⋆ Ctx c) ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex ho (by omega)
  subst hc
  cases hi
  · subst hb
    refine ⟨H1 ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (vsz d x.off ?@ x.v0
      ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
      ⋆ (16 ?@ lab "ps_mask2" ⋆ 16 ?@ lab "ff_ps_neg"))))))), ?_⟩
    simp -implicitDefEqProofs only [DataW, Blocks, Bool.false_eq_true, ite_false]
    rw [e1]
    ac_rfl
  · subst hb
    refine ⟨H1 ⋆ (256 ?@ x.mdctBuf ⋆ (vsz d x.off ?@ x.v0
      ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
      ⋆ (16 ?@ lab "ps_mask2" ⋆ 16 ?@ lab "ff_ps_neg"))))))), ?_⟩
    simp -implicitDefEqProofs only [DataW, Blocks, ite_true]
    rw [e1]
    ac_rfl

/-- `qmf_deint_bfly`'s footprint (512 bytes of `v`, the two halves of
`mdct_buf`) inside the data. -/
theorem DataW_carve_bfly (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (v a b : BitVec 64)
    (hv : (v - x.v0).toNat + 512 ≤ 9216) (ha : a = x.mdctBuf + 256#64) (hb : b = x.mdctBuf) :
    ∃ H, DataW d Ctx x t VC
      = Blocks [(v, 512), (a, 256), (b, 256)] ⋆ H := by
  subst ha hb
  obtain ⟨H2, e2⟩ := Block.carve_ex (Nat.le_trans hv (vsz_ge d x.off))
    (by have := vsz_le d x.off; omega)
  refine ⟨Blocks [(arg5 t, 19456)] ⋆ (H2
    ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ps_mask2" ⋆ (16 ?@ lab "ff_ps_neg" ⋆ Ctx (arg0 t)))))))), ?_⟩
  rw [DataW, e2]
  simp -implicitDefEqProofs only [Blocks]
  ac_rfl

/-- `qmf_deint_neg`'s footprint (256 bytes of `v`, the lower half of
`mdct_buf`, `ff_ps_neg`) inside the data. -/
theorem DataW_carve_dneg (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (v b : BitVec 64)
    (hv : (v - x.v0).toNat + 256 ≤ 9216) (hb : b = x.mdctBuf) :
    ∃ H, DataW d Ctx x t VC
      = Blocks [(v, 256), (b, 256), (lab "ff_ps_neg", 16)] ⋆ H := by
  subst hb
  obtain ⟨H2, e2⟩ := Block.carve_ex (Nat.le_trans hv (vsz_ge d x.off))
    (by have := vsz_le d x.off; omega)
  refine ⟨Blocks [(arg5 t, 19456)] ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (H2
    ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ps_mask2" ⋆ Ctx (arg0 t)))))))), ?_⟩
  rw [DataW, e2]
  simp -implicitDefEqProofs only [Blocks]
  ac_rfl

/-- `memcpy`'s footprint: two disjoint stretches of `v0`, the source below. -/
theorem DataW_carve_memcpy (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (a b : BitVec 64) (n : Nat)
    (h1 : (b - x.v0).toNat + n ≤ (a - x.v0).toNat) (h2 : (a - x.v0).toNat + n ≤ 9216) :
    ∃ H, DataW d Ctx x t VC = Blocks [(a, n), (b, n)] ⋆ H := by
  obtain ⟨H2, e2⟩ := Block.carve2_ex h1 (Nat.le_trans h2 (vsz_ge d x.off))
    (by have := vsz_le d x.off; omega)
  refine ⟨Blocks [(arg5 t, 19456)] ⋆ (256 ?@ x.mdctBuf ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (H2
    ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d ⋆ (4 ?@ lab "LCPI15_1"
    ⋆ (16 ?@ lab "ps_mask2" ⋆ (16 ?@ lab "ff_ps_neg" ⋆ Ctx (arg0 t)))))))))), ?_⟩
  rw [DataW, e2]
  rcases n with _ | n
  · simp -implicitDefEqProofs only [Blocks]; ac_rfl
  · simp -implicitDefEqProofs only [Blocks]; ac_rfl

/-! ## NEW LEMMAS (ds) -/

/-- (block-specific) What `.ds` touches inside the data: `LCPI15_1`, the 256 bytes of
`X` at `b` (read and written) and 128 bytes of `X` at `c` (read), as one `Blocks`
list whose `Inside` rules cover the offset accesses; the rest of `DataW` is `H`. -/
theorem DataW_carve_ds (d : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (x : QmfArgs)
    (t : MachineData) (VC : Mem 64 → Prop) (b c : BitVec 64)
    (hb : (b - arg5 t).toNat + 256 ≤ (c - arg5 t).toNat) (hc : (c - arg5 t).toNat + 128 ≤ 19456) :
    ∃ H, DataW d Ctx x t VC = Blocks [(lab "LCPI15_1", 4), (b, 256), (c, 128)] ⋆ H := by
  obtain ⟨H2, e2⟩ := Block.carve2_ex hb hc (by omega)
  refine ⟨H2 ⋆ (256 ?@ x.mdctBuf ⋆ (256 ?@ (x.mdctBuf + 256#64) ⋆ (vsz d x.off ?@ x.v0
    ⋆ (VC ⋆ ((8192 >>> d) ?@ arg4 t ⋆ ((2560 >>> d) ?@ qmfWin d
    ⋆ (16 ?@ lab "ps_mask2" ⋆ (16 ?@ lab "ff_ps_neg" ⋆ Ctx (arg0 t))))))))), ?_⟩
  simp -implicitDefEqProofs only [DataW, Blocks]
  rw [e2]
  ac_rfl

/-- (block-specific) The frame without its counter slot, behind a name `grind` does
not unfold. -/
def FrTail (d : Nat) (x : QmfArgs) (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  Locals d x t₀ Std.ExtHashMap.emp (Saved t₀ K)

theorem Fr_eq_tail (d : Nat) (x : QmfArgs) (t₀ : MachineData) (CC K : Mem 64 → Prop) :
    Fr d x t₀ CC K = CC ⋆ FrTail d x t₀ K := by
  simp -implicitDefEqProofs only [Fr, FrTail, Locals, Std.ExtHashMap.emp_sep]

omit [CodeEnv] in
/-- An `if` equal to a value: either branch. (`split` runs out of `simp` steps
on this text's block map.) -/
theorem ite_cases {α : Type} {c : Prop} {inst : Decidable c} {a b x : α}
    (h : @ite α c inst a b = x) : (c ∧ a = x) ∨ (¬c ∧ b = x) := by
  by_cases hc : c
  · exact Or.inl ⟨hc, by rw [if_pos hc] at h; exact h⟩
  · exact Or.inr ⟨hc, by rw [if_neg hc] at h; exact h⟩

omit [CodeEnv] in
/-- A block of `n + 8` bytes is 8 bytes and the rest. -/
theorem Block.split8 (a : BitVec 64) (n : Nat) (hw : n + 8 ≤ 2 ^ 64) :
    (n + 8) ?@ a = 8 ?@ a ⋆ n ?@ (a + 8#64) := by
  rw [Nat.add_comm, Block.split a 8 n (by omega)]

omit [CodeEnv] in
/-- The own 0x128 bytes as the 37 cells the code uses. -/
theorem frame_cells (r : BitVec 64) (K : Mem 64 → Prop) :
    0x128 ?@ (r - 0x128#64) ⋆ K = BlankL r (BlankS r K) := by
  rw [show (296 ?@ (r - 0x128#64) : Mem 64 → Prop) = (288 + 8) ?@ (r - 0x128#64) from rfl,
    Block.split8 _ 288 (by decide), show r - 0x128#64 + 8#64 = r - 0x120#64 by bv_omega]
  rw [show (288 ?@ (r - 0x120#64) : Mem 64 → Prop) = (280 + 8) ?@ (r - 0x120#64) from rfl,
    Block.split8 _ 280 (by decide), show r - 0x120#64 + 8#64 = r - 0x118#64 by bv_omega]
  rw [show (280 ?@ (r - 0x118#64) : Mem 64 → Prop) = (272 + 8) ?@ (r - 0x118#64) from rfl,
    Block.split8 _ 272 (by decide), show r - 0x118#64 + 8#64 = r - 0x110#64 by bv_omega]
  rw [show (272 ?@ (r - 0x110#64) : Mem 64 → Prop) = (264 + 8) ?@ (r - 0x110#64) from rfl,
    Block.split8 _ 264 (by decide), show r - 0x110#64 + 8#64 = r - 0x108#64 by bv_omega]
  rw [show (264 ?@ (r - 0x108#64) : Mem 64 → Prop) = (256 + 8) ?@ (r - 0x108#64) from rfl,
    Block.split8 _ 256 (by decide), show r - 0x108#64 + 8#64 = r - 0x100#64 by bv_omega]
  rw [show (256 ?@ (r - 0x100#64) : Mem 64 → Prop) = (248 + 8) ?@ (r - 0x100#64) from rfl,
    Block.split8 _ 248 (by decide), show r - 0x100#64 + 8#64 = r - 0xf8#64 by bv_omega]
  rw [show (248 ?@ (r - 0xf8#64) : Mem 64 → Prop) = (240 + 8) ?@ (r - 0xf8#64) from rfl,
    Block.split8 _ 240 (by decide), show r - 0xf8#64 + 8#64 = r - 0xf0#64 by bv_omega]
  rw [show (240 ?@ (r - 0xf0#64) : Mem 64 → Prop) = (232 + 8) ?@ (r - 0xf0#64) from rfl,
    Block.split8 _ 232 (by decide), show r - 0xf0#64 + 8#64 = r - 0xe8#64 by bv_omega]
  rw [show (232 ?@ (r - 0xe8#64) : Mem 64 → Prop) = (224 + 8) ?@ (r - 0xe8#64) from rfl,
    Block.split8 _ 224 (by decide), show r - 0xe8#64 + 8#64 = r - 0xe0#64 by bv_omega]
  rw [show (224 ?@ (r - 0xe0#64) : Mem 64 → Prop) = (216 + 8) ?@ (r - 0xe0#64) from rfl,
    Block.split8 _ 216 (by decide), show r - 0xe0#64 + 8#64 = r - 0xd8#64 by bv_omega]
  rw [show (216 ?@ (r - 0xd8#64) : Mem 64 → Prop) = (208 + 8) ?@ (r - 0xd8#64) from rfl,
    Block.split8 _ 208 (by decide), show r - 0xd8#64 + 8#64 = r - 0xd0#64 by bv_omega]
  rw [show (208 ?@ (r - 0xd0#64) : Mem 64 → Prop) = (200 + 8) ?@ (r - 0xd0#64) from rfl,
    Block.split8 _ 200 (by decide), show r - 0xd0#64 + 8#64 = r - 0xc8#64 by bv_omega]
  rw [show (200 ?@ (r - 0xc8#64) : Mem 64 → Prop) = (192 + 8) ?@ (r - 0xc8#64) from rfl,
    Block.split8 _ 192 (by decide), show r - 0xc8#64 + 8#64 = r - 0xc0#64 by bv_omega]
  rw [show (192 ?@ (r - 0xc0#64) : Mem 64 → Prop) = (184 + 8) ?@ (r - 0xc0#64) from rfl,
    Block.split8 _ 184 (by decide), show r - 0xc0#64 + 8#64 = r - 0xb8#64 by bv_omega]
  rw [show (184 ?@ (r - 0xb8#64) : Mem 64 → Prop) = (176 + 8) ?@ (r - 0xb8#64) from rfl,
    Block.split8 _ 176 (by decide), show r - 0xb8#64 + 8#64 = r - 0xb0#64 by bv_omega]
  rw [show (176 ?@ (r - 0xb0#64) : Mem 64 → Prop) = (168 + 8) ?@ (r - 0xb0#64) from rfl,
    Block.split8 _ 168 (by decide), show r - 0xb0#64 + 8#64 = r - 0xa8#64 by bv_omega]
  rw [show (168 ?@ (r - 0xa8#64) : Mem 64 → Prop) = (160 + 8) ?@ (r - 0xa8#64) from rfl,
    Block.split8 _ 160 (by decide), show r - 0xa8#64 + 8#64 = r - 0xa0#64 by bv_omega]
  rw [show (160 ?@ (r - 0xa0#64) : Mem 64 → Prop) = (152 + 8) ?@ (r - 0xa0#64) from rfl,
    Block.split8 _ 152 (by decide), show r - 0xa0#64 + 8#64 = r - 0x98#64 by bv_omega]
  rw [show (152 ?@ (r - 0x98#64) : Mem 64 → Prop) = (144 + 8) ?@ (r - 0x98#64) from rfl,
    Block.split8 _ 144 (by decide), show r - 0x98#64 + 8#64 = r - 0x90#64 by bv_omega]
  rw [show (144 ?@ (r - 0x90#64) : Mem 64 → Prop) = (136 + 8) ?@ (r - 0x90#64) from rfl,
    Block.split8 _ 136 (by decide), show r - 0x90#64 + 8#64 = r - 0x88#64 by bv_omega]
  rw [show (136 ?@ (r - 0x88#64) : Mem 64 → Prop) = (128 + 8) ?@ (r - 0x88#64) from rfl,
    Block.split8 _ 128 (by decide), show r - 0x88#64 + 8#64 = r - 0x80#64 by bv_omega]
  rw [show (128 ?@ (r - 0x80#64) : Mem 64 → Prop) = (120 + 8) ?@ (r - 0x80#64) from rfl,
    Block.split8 _ 120 (by decide), show r - 0x80#64 + 8#64 = r - 0x78#64 by bv_omega]
  rw [show (120 ?@ (r - 0x78#64) : Mem 64 → Prop) = (112 + 8) ?@ (r - 0x78#64) from rfl,
    Block.split8 _ 112 (by decide), show r - 0x78#64 + 8#64 = r - 0x70#64 by bv_omega]
  rw [show (112 ?@ (r - 0x70#64) : Mem 64 → Prop) = (104 + 8) ?@ (r - 0x70#64) from rfl,
    Block.split8 _ 104 (by decide), show r - 0x70#64 + 8#64 = r - 0x68#64 by bv_omega]
  rw [show (104 ?@ (r - 0x68#64) : Mem 64 → Prop) = (96 + 8) ?@ (r - 0x68#64) from rfl,
    Block.split8 _ 96 (by decide), show r - 0x68#64 + 8#64 = r - 0x60#64 by bv_omega]
  rw [show (96 ?@ (r - 0x60#64) : Mem 64 → Prop) = (88 + 8) ?@ (r - 0x60#64) from rfl,
    Block.split8 _ 88 (by decide), show r - 0x60#64 + 8#64 = r - 0x58#64 by bv_omega]
  rw [show (88 ?@ (r - 0x58#64) : Mem 64 → Prop) = (80 + 8) ?@ (r - 0x58#64) from rfl,
    Block.split8 _ 80 (by decide), show r - 0x58#64 + 8#64 = r - 0x50#64 by bv_omega]
  rw [show (80 ?@ (r - 0x50#64) : Mem 64 → Prop) = (72 + 8) ?@ (r - 0x50#64) from rfl,
    Block.split8 _ 72 (by decide), show r - 0x50#64 + 8#64 = r - 0x48#64 by bv_omega]
  rw [show (72 ?@ (r - 0x48#64) : Mem 64 → Prop) = (64 + 8) ?@ (r - 0x48#64) from rfl,
    Block.split8 _ 64 (by decide), show r - 0x48#64 + 8#64 = r - 0x40#64 by bv_omega]
  rw [show (64 ?@ (r - 0x40#64) : Mem 64 → Prop) = (56 + 8) ?@ (r - 0x40#64) from rfl,
    Block.split8 _ 56 (by decide), show r - 0x40#64 + 8#64 = r - 0x38#64 by bv_omega]
  rw [show (56 ?@ (r - 0x38#64) : Mem 64 → Prop) = (48 + 8) ?@ (r - 0x38#64) from rfl,
    Block.split8 _ 48 (by decide), show r - 0x38#64 + 8#64 = r - 0x30#64 by bv_omega]
  rw [show (48 ?@ (r - 0x30#64) : Mem 64 → Prop) = (40 + 8) ?@ (r - 0x30#64) from rfl,
    Block.split8 _ 40 (by decide), show r - 0x30#64 + 8#64 = r - 0x28#64 by bv_omega]
  rw [show (40 ?@ (r - 0x28#64) : Mem 64 → Prop) = (32 + 8) ?@ (r - 0x28#64) from rfl,
    Block.split8 _ 32 (by decide), show r - 0x28#64 + 8#64 = r - 0x20#64 by bv_omega]
  rw [show (32 ?@ (r - 0x20#64) : Mem 64 → Prop) = (24 + 8) ?@ (r - 0x20#64) from rfl,
    Block.split8 _ 24 (by decide), show r - 0x20#64 + 8#64 = r - 0x18#64 by bv_omega]
  rw [show (24 ?@ (r - 0x18#64) : Mem 64 → Prop) = (16 + 8) ?@ (r - 0x18#64) from rfl,
    Block.split8 _ 16 (by decide), show r - 0x18#64 + 8#64 = r - 0x10#64 by bv_omega]
  rw [show (16 ?@ (r - 0x10#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x10#64) from rfl,
    Block.split8 _ 8 (by decide), show r - 0x10#64 + 8#64 = r - 0x8#64 by bv_omega]
  simp -implicitDefEqProofs only [BlankL, BlankS, Std.ExtHashMap.sep_assoc]

/-! ## Stage 2 store threading

`store_keep_at`: a store into a front cell of the block's view, read back as the view with that
cell known, in place (the same `Split` path before and after), the store address in the `rbp` form
of the `vcgen` goals (`qa_<off>`). The prologue blocks state the chain before `vcgen`. -/

theorem store_keep_at {m : Mem 64} {H H' R : Mem 64 → Prop} {a b : BitVec 64} {n : Nat} {v : Int}
    (h : m =⋆ H) (hs : Mem.Split (n ?@ a) R H) (ht : Mem.Split (Int.toBytes n v =@ a) R H')
    (hb : b = a) : m.storeInt b n v =⋆ H' := by
  subst hb; unfold Mem.Split at ht; rw [ht]; exact Mem.Block.storeInt_val h hs v

theorem store_keep_val_at {m : Mem 64} {H H' R : Mem 64 → Prop} {a b : BitVec 64} {bs : List UInt8}
    {n : Nat} {v : Int} (h : m =⋆ H) (hs : Mem.Split (bs =@ a) R H) (hlen : bs.length = n)
    (ht : Mem.Split (Int.toBytes n v =@ a) R H') (hb : b = a) : m.storeInt b n v =⋆ H' := by
  subst hb; unfold Mem.Split at ht; rw [ht]; exact Mem.Val.storeInt h hs hlen v

theorem qa_30 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-48) = t - 0x38#64 := by
  rw [show Int64.toBitVec (-48) = (0 : BitVec 64) - 48#64 from rfl]; bv_omega

theorem qa_38 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-56) = t - 0x40#64 := by
  rw [show Int64.toBitVec (-56) = (0 : BitVec 64) - 56#64 from rfl]; bv_omega

theorem qa_40 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-64) = t - 0x48#64 := by
  rw [show Int64.toBitVec (-64) = (0 : BitVec 64) - 64#64 from rfl]; bv_omega

theorem qa_48 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-72) = t - 0x50#64 := by
  rw [show Int64.toBitVec (-72) = (0 : BitVec 64) - 72#64 from rfl]; bv_omega

theorem qa_50 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-80) = t - 0x58#64 := by
  rw [show Int64.toBitVec (-80) = (0 : BitVec 64) - 80#64 from rfl]; bv_omega

theorem qa_58 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-88) = t - 0x60#64 := by
  rw [show Int64.toBitVec (-88) = (0 : BitVec 64) - 88#64 from rfl]; bv_omega

theorem qa_60 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-96) = t - 0x68#64 := by
  rw [show Int64.toBitVec (-96) = (0 : BitVec 64) - 96#64 from rfl]; bv_omega

theorem qa_68 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-104) = t - 0x70#64 := by
  rw [show Int64.toBitVec (-104) = (0 : BitVec 64) - 104#64 from rfl]; bv_omega

theorem qa_70 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-112) = t - 0x78#64 := by
  rw [show Int64.toBitVec (-112) = (0 : BitVec 64) - 112#64 from rfl]; bv_omega

theorem qa_78 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-120) = t - 0x80#64 := by
  rw [show Int64.toBitVec (-120) = (0 : BitVec 64) - 120#64 from rfl]; bv_omega

theorem qa_80 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-128) = t - 0x88#64 := by
  rw [show Int64.toBitVec (-128) = (0 : BitVec 64) - 128#64 from rfl]; bv_omega

theorem qa_88 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-136) = t - 0x90#64 := by
  rw [show Int64.toBitVec (-136) = (0 : BitVec 64) - 136#64 from rfl]; bv_omega

theorem qa_90 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-144) = t - 0x98#64 := by
  rw [show Int64.toBitVec (-144) = (0 : BitVec 64) - 144#64 from rfl]; bv_omega

theorem qa_98 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-152) = t - 0xa0#64 := by
  rw [show Int64.toBitVec (-152) = (0 : BitVec 64) - 152#64 from rfl]; bv_omega

theorem qa_a0 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-160) = t - 0xa8#64 := by
  rw [show Int64.toBitVec (-160) = (0 : BitVec 64) - 160#64 from rfl]; bv_omega

theorem qa_a8 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-168) = t - 0xb0#64 := by
  rw [show Int64.toBitVec (-168) = (0 : BitVec 64) - 168#64 from rfl]; bv_omega

theorem qa_b0 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-176) = t - 0xb8#64 := by
  rw [show Int64.toBitVec (-176) = (0 : BitVec 64) - 176#64 from rfl]; bv_omega

theorem qa_b8 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-184) = t - 0xc0#64 := by
  rw [show Int64.toBitVec (-184) = (0 : BitVec 64) - 184#64 from rfl]; bv_omega

theorem qa_c0 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-192) = t - 0xc8#64 := by
  rw [show Int64.toBitVec (-192) = (0 : BitVec 64) - 192#64 from rfl]; bv_omega

theorem qa_c8 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-200) = t - 0xd0#64 := by
  rw [show Int64.toBitVec (-200) = (0 : BitVec 64) - 200#64 from rfl]; bv_omega

theorem qa_d0 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-208) = t - 0xd8#64 := by
  rw [show Int64.toBitVec (-208) = (0 : BitVec 64) - 208#64 from rfl]; bv_omega

theorem qa_d8 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-216) = t - 0xe0#64 := by
  rw [show Int64.toBitVec (-216) = (0 : BitVec 64) - 216#64 from rfl]; bv_omega

theorem qa_e0 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-224) = t - 0xe8#64 := by
  rw [show Int64.toBitVec (-224) = (0 : BitVec 64) - 224#64 from rfl]; bv_omega

theorem qa_e8 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-232) = t - 0xf0#64 := by
  rw [show Int64.toBitVec (-232) = (0 : BitVec 64) - 232#64 from rfl]; bv_omega

theorem qa_f0 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-240) = t - 0xf8#64 := by
  rw [show Int64.toBitVec (-240) = (0 : BitVec 64) - 240#64 from rfl]; bv_omega

theorem qa_f8 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-248) = t - 0x100#64 := by
  rw [show Int64.toBitVec (-248) = (0 : BitVec 64) - 248#64 from rfl]; bv_omega

theorem qa_100 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-256) = t - 0x108#64 := by
  rw [show Int64.toBitVec (-256) = (0 : BitVec 64) - 256#64 from rfl]; bv_omega

theorem qa_108 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-264) = t - 0x110#64 := by
  rw [show Int64.toBitVec (-264) = (0 : BitVec 64) - 264#64 from rfl]; bv_omega

theorem qa_110 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-272) = t - 0x118#64 := by
  rw [show Int64.toBitVec (-272) = (0 : BitVec 64) - 272#64 from rfl]; bv_omega

theorem qa_118 (t : BitVec 64) : t - 8#64 + Int64.toBitVec (-280) = t - 0x120#64 := by
  rw [show Int64.toBitVec (-280) = (0 : BitVec 64) - 280#64 from rfl]; bv_omega

/-! ## F6 slot reads

Closed lemmas for the loads of the spill slots (`T_ld_<off>`, generated by a one-off
script from the frame layout), the `fdsp->vector_fmul_add` pointer and the callees'
return-address slot: the blocks state them before `vcgen`, so the arithmetic side goals get the
loaded values without `grind` walking the frame. -/

/-- (F6 slot read) The spill slot `-0x118(%rbp)` (`rsp₀ - 0x120`) holds `arg3 t₀`. -/
theorem T_ld_118 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-280)) 8 = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-280)
      = t₀.regs.get64 .rsp - 0x120#64 by
    rw [show Int64.toBitVec (-280) = (0 : BitVec 64) - 280#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x110(%rbp)` (`rsp₀ - 0x118`) holds `qmfWin d`. -/
theorem T_ld_110 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-272)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-272)
      = t₀.regs.get64 .rsp - 0x118#64 by
    rw [show Int64.toBitVec (-272) = (0 : BitVec 64) - 272#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x108(%rbp)` (`rsp₀ - 0x110`) holds `K (128 / 2 ^ d)`. -/
theorem T_ld_108 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-264)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (128 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-264)
      = t₀.regs.get64 .rsp - 0x110#64 by
    rw [show Int64.toBitVec (-264) = (0 : BitVec 64) - 264#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x100(%rbp)` (`rsp₀ - 0x108`) holds `K (64 / 2 ^ d)`. -/
theorem T_ld_100 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-256)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (64 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-256)
      = t₀.regs.get64 .rsp - 0x108#64 by
    rw [show Int64.toBitVec (-256) = (0 : BitVec 64) - 256#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xf8(%rbp)` (`rsp₀ - 0x100`) holds `K (192 / 2 ^ d)`. -/
theorem T_ld_f8 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-248)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (192 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-248)
      = t₀.regs.get64 .rsp - 0x100#64 by
    rw [show Int64.toBitVec (-248) = (0 : BitVec 64) - 248#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xf0(%rbp)` (`rsp₀ - 0xf8`) holds `K (256 / 2 ^ d)`. -/
theorem T_ld_f0 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-240)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (256 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-240)
      = t₀.regs.get64 .rsp - 0xf8#64 by
    rw [show Int64.toBitVec (-240) = (0 : BitVec 64) - 240#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xe8(%rbp)` (`rsp₀ - 0xf0`) holds `K (448 / 2 ^ d)`. -/
theorem T_ld_e8 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-232)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (448 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-232)
      = t₀.regs.get64 .rsp - 0xf0#64 by
    rw [show Int64.toBitVec (-232) = (0 : BitVec 64) - 232#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xe0(%rbp)` (`rsp₀ - 0xe8`) holds `K (512 / 2 ^ d)`. -/
theorem T_ld_e0 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-224)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (512 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-224)
      = t₀.regs.get64 .rsp - 0xe8#64 by
    rw [show Int64.toBitVec (-224) = (0 : BitVec 64) - 224#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xd8(%rbp)` (`rsp₀ - 0xe0`) holds `K (704 / 2 ^ d)`. -/
theorem T_ld_d8 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-216)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (704 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-216)
      = t₀.regs.get64 .rsp - 0xe0#64 by
    rw [show Int64.toBitVec (-216) = (0 : BitVec 64) - 216#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xd0(%rbp)` (`rsp₀ - 0xd8`) holds `qmfWin d + K (4 * (320 / 2 ^ d))`. -/
theorem T_ld_d0 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-208)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (320 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-208)
      = t₀.regs.get64 .rsp - 0xd8#64 by
    rw [show Int64.toBitVec (-208) = (0 : BitVec 64) - 208#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xc8(%rbp)` (`rsp₀ - 0xd0`) holds `K (768 / 2 ^ d)`. -/
theorem T_ld_c8 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-200)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (768 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-200)
      = t₀.regs.get64 .rsp - 0xd0#64 by
    rw [show Int64.toBitVec (-200) = (0 : BitVec 64) - 200#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xc0(%rbp)` (`rsp₀ - 0xc8`) holds `K (960 / 2 ^ d)`. -/
theorem T_ld_c0 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-192)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (960 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-192)
      = t₀.regs.get64 .rsp - 0xc8#64 by
    rw [show Int64.toBitVec (-192) = (0 : BitVec 64) - 192#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xb8(%rbp)` (`rsp₀ - 0xc0`) holds `K (1024 / 2 ^ d)`. -/
theorem T_ld_b8 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-184)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (1024 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-184)
      = t₀.regs.get64 .rsp - 0xc0#64 by
    rw [show Int64.toBitVec (-184) = (0 : BitVec 64) - 184#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xb0(%rbp)` (`rsp₀ - 0xb8`) holds `K (1216 / 2 ^ d)`. -/
theorem T_ld_b0 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-176)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (1216 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-176)
      = t₀.regs.get64 .rsp - 0xb8#64 by
    rw [show Int64.toBitVec (-176) = (0 : BitVec 64) - 176#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xa8(%rbp)` (`rsp₀ - 0xb0`) holds `qmfWin d + K (4 * (384 / 2 ^ d))`. -/
theorem T_ld_a8 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-168)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (384 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-168)
      = t₀.regs.get64 .rsp - 0xb0#64 by
    rw [show Int64.toBitVec (-168) = (0 : BitVec 64) - 168#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0xa0(%rbp)` (`rsp₀ - 0xa8`) holds `qmfWin d + K (4 * (576 / 2 ^ d))`. -/
theorem T_ld_a0 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-160)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (576 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-160)
      = t₀.regs.get64 .rsp - 0xa8#64 by
    rw [show Int64.toBitVec (-160) = (0 : BitVec 64) - 160#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x98(%rbp)` (`rsp₀ - 0xa0`) holds `K (4 * (64 / 2 ^ d))`. -/
theorem T_ld_98 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-152)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (4 * (64 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-152)
      = t₀.regs.get64 .rsp - 0xa0#64 by
    rw [show Int64.toBitVec (-152) = (0 : BitVec 64) - 152#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x90(%rbp)` (`rsp₀ - 0x98`) holds `qmfWin d + K (4 * (64 / 2 ^ d))`. -/
theorem T_ld_90 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-144)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (64 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-144)
      = t₀.regs.get64 .rsp - 0x98#64 by
    rw [show Int64.toBitVec (-144) = (0 : BitVec 64) - 144#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x88(%rbp)` (`rsp₀ - 0x90`) holds `qmfWin d + K (4 * (128 / 2 ^ d))`. -/
theorem T_ld_88 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-136)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (128 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-136)
      = t₀.regs.get64 .rsp - 0x90#64 by
    rw [show Int64.toBitVec (-136) = (0 : BitVec 64) - 136#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x80(%rbp)` (`rsp₀ - 0x88`) holds `qmfWin d + K (4 * (192 / 2 ^ d))`. -/
theorem T_ld_80 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-128)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (192 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-128)
      = t₀.regs.get64 .rsp - 0x88#64 by
    rw [show Int64.toBitVec (-128) = (0 : BitVec 64) - 128#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x78(%rbp)` (`rsp₀ - 0x80`) holds `qmfWin d + K (4 * (256 / 2 ^ d))`. -/
theorem T_ld_78 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-120)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (256 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-120)
      = t₀.regs.get64 .rsp - 0x80#64 by
    rw [show Int64.toBitVec (-120) = (0 : BitVec 64) - 120#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x70(%rbp)` (`rsp₀ - 0x78`) holds `qmfWin d + K (4 * (448 / 2 ^ d))`. -/
theorem T_ld_70 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-112)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (448 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-112)
      = t₀.regs.get64 .rsp - 0x78#64 by
    rw [show Int64.toBitVec (-112) = (0 : BitVec 64) - 112#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x68(%rbp)` (`rsp₀ - 0x70`) holds `qmfWin d + K (4 * (512 / 2 ^ d))`. -/
theorem T_ld_68 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-104)) 8 = some (Int.ofBytes (Int.toBytes 8 (qmfWin d + K (4 * (512 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-104)
      = t₀.regs.get64 .rsp - 0x70#64 by
    rw [show Int64.toBitVec (-104) = (0 : BitVec 64) - 104#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x60(%rbp)` (`rsp₀ - 0x68`) holds `K (4 * (1152 / 2 ^ d))`. -/
theorem T_ld_60 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-96)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (4 * (1152 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-96)
      = t₀.regs.get64 .rsp - 0x68#64 by
    rw [show Int64.toBitVec (-96) = (0 : BitVec 64) - 96#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x58(%rbp)` (`rsp₀ - 0x60`) holds `K (2304 - 1152 / 2 ^ d)`. -/
theorem T_ld_58 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-88)) 8 = some (Int.ofBytes (Int.toBytes 8 (K (2304 - 1152 / 2 ^ d)).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-88)
      = t₀.regs.get64 .rsp - 0x60#64 by
    rw [show Int64.toBitVec (-88) = (0 : BitVec 64) - 88#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x50(%rbp)` (`rsp₀ - 0x58`) holds `x.v0 + K (4 * (2304 - 1152 / 2 ^ d))`. -/
theorem T_ld_50 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-80)) 8 = some (Int.ofBytes (Int.toBytes 8 (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-80)
      = t₀.regs.get64 .rsp - 0x58#64 by
    rw [show Int64.toBitVec (-80) = (0 : BitVec 64) - 80#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x48(%rbp)` (`rsp₀ - 0x50`) holds `x.mdctBuf + 256#64`. -/
theorem T_ld_48 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-72)) 8 = some (Int.ofBytes (Int.toBytes 8 (x.mdctBuf + 256#64).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-72)
      = t₀.regs.get64 .rsp - 0x50#64 by
    rw [show Int64.toBitVec (-72) = (0 : BitVec 64) - 72#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x40(%rbp)` (`rsp₀ - 0x48`) holds `arg1 t₀`. -/
theorem T_ld_40 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-64)) 8 = some (Int.ofBytes (Int.toBytes 8 (arg1 t₀).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-64)
      = t₀.regs.get64 .rsp - 0x48#64 by
    rw [show Int64.toBitVec (-64) = (0 : BitVec 64) - 64#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x38(%rbp)` (`rsp₀ - 0x40`) holds `arg0 t₀`. -/
theorem T_ld_38 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-56)) 8 = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-56)
      = t₀.regs.get64 .rsp - 0x40#64 by
    rw [show Int64.toBitVec (-56) = (0 : BitVec 64) - 56#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The spill slot `-0x30(%rbp)` (`rsp₀ - 0x38`) holds `arg2 t₀`. -/
theorem T_ld_30 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC CC : Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ CC)) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-48)) 8 = some (Int.ofBytes (Int.toBytes 8 (arg2 t₀).toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-48)
      = t₀.regs.get64 .rsp - 0x38#64 by
    rw [show Int64.toBitVec (-48) = (0 : BitVec 64) - 48#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The stack argument `0x10(%rbp)` (`rsp₀ + 0x8`) holds `x.mdctBuf.toInt`. -/
theorem T_lda_10 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec 16) 8 = some (Int.ofBytes (Int.toBytes 8 x.mdctBuf.toInt)) := by
  simp -implicitDefEqProofs only [T, ArgsW_open] at h
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec 16
      = t₀.regs.get64 .rsp + 8#64 by
    rw [show Int64.toBitVec 16 = 16#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The stack argument `0x18(%rbp)` (`rsp₀ + 0x10`) holds `x.v0.toInt`. -/
theorem T_lda_18 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec 24) 8 = some (Int.ofBytes (Int.toBytes 8 x.v0.toInt)) := by
  simp -implicitDefEqProofs only [T, ArgsW_open] at h
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec 24
      = t₀.regs.get64 .rsp + 16#64 by
    rw [show Int64.toBitVec 24 = 24#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The stack argument `0x20(%rbp)` (`rsp₀ + 0x18`) holds `x.vOff.toInt`. -/
theorem T_lda_20 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec 32) 8 = some (Int.ofBytes (Int.toBytes 8 x.vOff.toInt)) := by
  simp -implicitDefEqProofs only [T, ArgsW_open] at h
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec 32
      = t₀.regs.get64 .rsp + 24#64 by
    rw [show Int64.toBitVec 32 = 32#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The stack argument `0x28(%rbp)` (`rsp₀ + 0x20`) holds `(d : Int)`. -/
theorem T_lda_28 {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec 40) 4 = some (Int.ofBytes (Int.toBytes 4 (d : Int))) := by
  simp -implicitDefEqProofs only [T, ArgsW_open] at h
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec 40
      = t₀.regs.get64 .rsp + 32#64 by
    rw [show Int64.toBitVec 40 = 40#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (F6 slot read) The loop counter's slot `-0x120(%rbp)` (`rsp₀ - 0x128`), in the form
`vcgen` leaves for `mov -0x120(%rbp),%rax`. -/
theorem T_ldc {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop} {m : Mem 64} {w rbp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w)))
    (hrbp : rbp = t₀.regs.get64 .rsp - 8#64) :
    m.loadInt (rbp + 0 + Int64.toBitVec (-288)) 8 = some (Int.ofBytes (Int.toBytes 8 w.toInt)) := by
  rw [hrbp, show t₀.regs.get64 .rsp - 8#64 + 0 + Int64.toBitVec (-288)
      = t₀.regs.get64 .rsp - 0x128#64 by
    rw [show Int64.toBitVec (-288) = (0 : BitVec 64) - 288#64 from rfl]; bv_omega]
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)


/-- (F6) `fdsp->vector_fmul_add`, the pointer at `fdsp + 0x30` (`r15 = arg3`), read from
the table's memory. -/
theorem T_fn_fma {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {r15 : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) (h15 : r15 = arg3 t₀) :
    Option.map (fun v => Int64.ofBitVec (BitVec.ofInt 64 v)) (m.loadInt (r15 + 0 + Int64.toBitVec 48) 8)
      = some fs.fmulAdd := by
  simp -implicitDefEqProofs only [T, FnsW_open] at h
  rw [h15, show arg3 t₀ + 0 + Int64.toBitVec 48 = arg3 t₀ + 0x30#64 by
    rw [show Int64.toBitVec 48 = 0x30#64 from rfl]; bv_omega,
    Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
      _) _) _) _) _) (Int.toBytes_length _ _) (by decide)]
  simp -implicitDefEqProofs only [Option.map_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]

/-- (F6) The callees' return-address slot `rsp₀ - 0x130` (`rsp - 8` in the loop) can be
loaded. -/
theorem T_push_isSome {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {rsp : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) (hrsp : rsp = t₀.regs.get64 .rsp - 296#64) :
    (m.loadInt (rsp - 8#64) 8).isSome = true := by
  rw [hrsp, show t₀.regs.get64 .rsp - 296#64 - 8#64 = t₀.regs.get64 .rsp - 0x130#64 by bv_omega]
  exact Mem.Block.loadInt_isSome_at h (Mem.Split.here _ _)

set_option hygiene false in
/-- (F6) The slot values of the block's loads, from the `T_ld_*` facts `hL0 …` stated
before `vcgen`: the load hypotheses become equations on the values, the memory fact goes. -/
macro "qmf_slots " "[" ls:ident,* "]" : tactic => do
  let ls : Array Lean.Syntax := ls.getElems
  let args : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ls.mapM fun l => `(Lean.Parser.Tactic.simpLemma| $(⟨l⟩):ident)
  `(tactic| (
    clear hm
    try simp -implicitDefEqProofs only [$args,*, Option.some.injEq] at *
    try subst_vars
    try simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Reg64s.get64_set64,
      reduceCtorEq, ite_true, ite_false] at *))


set_option hygiene false in
/-- The reductions after `vcgen` at a literal `div`. -/
macro "qmf_norm" : tactic => `(tactic| (
  all_goals call_simp
  all_goals try subst_vars
  all_goals try dsimp only at *
  all_goals try obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
  all_goals try simp -implicitDefEqProofs only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub,
    Nat.reduceShiftRight, AddrIndex.offset64, ite_true, ite_false, Nat.zero_ne_one,
    Nat.one_ne_zero] at *))

set_option hygiene false in
/-- One of the nine `vector_fmul_add` blocks `.f1` … `.f9`: three spill-slot
loads, the call through `fdsp->vector_fmul_add` on (`out` row, a stretch of
`v`, a stretch of the window), fall through to the next block. -/
macro "qmf_fblock " h:term:max f:term:max " [" ls:ident,* "]" : tactic => do
  let ls : Array Lean.Syntax := ls.getElems
  let ns : Array Lean.Ident := (Array.range ls.size).map fun i => Lean.mkIdent (Lean.Name.mkSimple s!"hL{i}")
  let mut pre ← `(tactic| skip)
  for i in [0:ls.size] do
    pre ← `(tactic| ($pre; have $(ns[i]!) := $(⟨ls[i]!⟩) hm hrbp))
  let args : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
  `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, h12, h15, hm⟩, hn⟩ := hs₀
  $pre:tactic
  have hF := T_fn_fma hm h15
  have hP := T_push_isSome hm hrsp
  vcgen [MachineWP.call_mem_proc_spec_at
    (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀
      ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀))))
    $f (Kraken.Executable.ProcSpec.widen (k := k) $h (Nat.le_refl k) (by omega))]
  all_goals try clear hNeg hDN hDB hTx hFm hFma hMc
  qmf_norm
  all_goals first
    | (refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
       · exact hF
       · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
       · qmf_slots [$ns,*]
         try simp -implicitDefEqProofs only [isAligned, beq_iff_eq] at *
         grind_cells'
       · qmf_slots [$ns,*]
         apply DataW_carve_fmul <;> grind_cells'
       · vcgen
         all_goals grind_cells'
       · exact hP)
    | (simp -implicitDefEqProofs only [$args,*, Option.isSome_some]; done)
    | grind_cells'))

set_option hygiene false in
/-- `.L9e42`: the `vector_fmul` call on the same three regions as the
`vector_fmul_add` blocks, through `fdsp->vector_fmul`. -/
macro "qmf_eblock " h:term:max f:term:max " [" ls:ident,* "]" : tactic => do
  let ls : Array Lean.Syntax := ls.getElems
  let ns : Array Lean.Ident := (Array.range ls.size).map fun i => Lean.mkIdent (Lean.Name.mkSimple s!"hL{i}")
  let mut pre ← `(tactic| skip)
  for i in [0:ls.size] do
    pre ← `(tactic| ($pre; have $(ns[i]!) := $(⟨ls[i]!⟩) hm hrbp))
  let args : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
  `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, hm⟩, hn⟩ := hs₀
  $pre:tactic
  have hP := T_push_isSome hm hrsp
  vcgen [MachineWP.call_mem_proc_spec_at
    (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀
      ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀))))
    $f (Kraken.Executable.ProcSpec.widen (k := k) $h (Nat.le_refl k) (by omega))]
  all_goals try clear hNeg hDN hDB hTx hFm hFma hMc
  qmf_norm
  all_goals first
    | (refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
       · simp -implicitDefEqProofs only [FnsW_open] at *; grind_cells'
       · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
       · qmf_slots [$ns,*]
         try simp -implicitDefEqProofs only [isAligned, beq_iff_eq] at *
         grind_cells'
       · qmf_slots [$ns,*]
         apply DataW_carve_fmul <;> grind_cells'
       · vcgen
         all_goals grind_cells'
       · exact hP)
    | (simp -implicitDefEqProofs only [$args,*, Option.isSome_some]; done)
    | grind_cells'))

set_option hygiene false in
/-- A call block: the entry state pinned, the hypotheses named by `pat`
(with `hrsp` and the memory fact `hm`), the call stepped with `rule`, the
callee's footprint carved by `carve`. Indirect calls have the pointer
obligation first, a direct call has none. -/
macro "qmf_call " "[" ls:ident,* "] " pat:Lean.Parser.Tactic.rcasesPatMed " using " rule:Lean.Parser.Tactic.simpLemma " carve " carve:tacticSeq : tactic => do
  let ls : Array Lean.Syntax := ls.getElems
  let ns : Array Lean.Ident := (Array.range ls.size).map fun i => Lean.mkIdent (Lean.Name.mkSimple s!"hL{i}")
  let mut pre ← `(tactic| skip)
  for i in [0:ls.size] do
    pre ← `(tactic| ($pre; have $(ns[i]!) := $(⟨ls[i]!⟩) hm hrbp))
  let args : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
  `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain $pat := hs₀
  $pre:tactic
  vcgen [$rule]
  all_goals try clear hNeg hDN hDB hTx hFm hFma hMc
  qmf_norm
  all_goals first
    | (refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
       · simp -implicitDefEqProofs only [FnsW_open] at *; grind_cells'
       · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
       · first | exact True.intro | (qmf_slots [$ns,*]; try simp -implicitDefEqProofs only [isAligned, beq_iff_eq] at *; grind_cells')
       · qmf_slots [$ns,*]
         ($carve)
       · vcgen
         all_goals grind_cells'
       · grind_cells')
    | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
       · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
       · first | exact True.intro | (qmf_slots [$ns,*]; try simp -implicitDefEqProofs only [isAligned, beq_iff_eq] at *; grind_cells')
       · qmf_slots [$ns,*]
         ($carve)
       · vcgen
         all_goals grind_cells'
       · grind_cells')
    | (simp -implicitDefEqProofs only [$args,*, Option.isSome_some]; done)
    | grind_cells'))

set_option hygiene false in
/-- `qmf_call` for a block that also reads a stack argument: `ArgsW` opened
in the memory fact and in the goal behind the call. -/
macro "qmf_callA " "[" ls:ident,* "] " pat:Lean.Parser.Tactic.rcasesPatMed " using " rule:Lean.Parser.Tactic.simpLemma " carve " cv:tacticSeq : tactic => do
  let ls : Array Lean.Syntax := ls.getElems
  let ns : Array Lean.Ident := (Array.range ls.size).map fun i => Lean.mkIdent (Lean.Name.mkSimple s!"hL{i}")
  let mut pre ← `(tactic| skip)
  for i in [0:ls.size] do
    pre ← `(tactic| ($pre; have $(ns[i]!) := $(⟨ls[i]!⟩) hm hrbp))
  let args : Array (Lean.TSyntax `Lean.Parser.Tactic.simpLemma) ←
    ns.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $n:ident)
  `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain $pat := hs₀
  $pre:tactic
  simp -implicitDefEqProofs only [T, ArgsW_open] at hm
  vcgen [$rule]
  all_goals try clear hNeg hDN hDB hTx hFm hFma hMc
  qmf_norm
  all_goals first
    | (refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
       · simp -implicitDefEqProofs only [FnsW_open] at *; grind_cells'
       · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
       · first | exact True.intro | (qmf_slots [$ns,*]; try simp -implicitDefEqProofs only [isAligned, beq_iff_eq] at *; grind_cells')
       · qmf_slots [$ns,*]
         ($cv)
       · vcgen
         all_goals (try simp -implicitDefEqProofs only [ArgsW_open] at *)
         all_goals grind_cells'
       · grind_cells')
    | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
       · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
       · first | exact True.intro | (qmf_slots [$ns,*]; try simp -implicitDefEqProofs only [isAligned, beq_iff_eq] at *; grind_cells')
       · qmf_slots [$ns,*]
         ($cv)
       · vcgen
         all_goals (try simp -implicitDefEqProofs only [ArgsW_open] at *)
         all_goals grind_cells'
       · grind_cells')
    | (simp -implicitDefEqProofs only [$args,*, Option.isSome_some]; done)
    | grind_cells'))

omit [CodeEnv] in
/-- The procedure's `0x130` bytes off the top of the reservation: the callees'
return-address slot, their reservation below it, the frame above. -/
theorem reserve_frame (k : Nat) {r : BitVec 64} (hw : 0x130 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x130 + k) r ⋆ K
      = 8 ?@ (r - 0x130#64) ⋆ (Reserve k (r - 0x130#64) ⋆ (0x128 ?@ (r - 0x128#64) ⋆ K)) :=
  Reserve_split_frame 0x130 k (by decide) r (by omega) K

omit [CodeEnv] in
/-- The saved registers' slots, their contents forgotten. -/
theorem Saved_blank (t₀ : MachineData) (K : Mem 64 → Prop) :
    Mem.Entails (Saved t₀ K) (BlankS (t₀.regs.get64 .rsp) K) :=
  Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.refl _))))))

/-! ## NEW LEMMAS (entry) -/

-- block-specific: each block's memory as the cells it touches in front of one `Hid` atom
theorem entry_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (fun K => BlankL (t₀.regs.get64 .rsp) (BlankS (t₀.regs.get64 .rsp) K)) =
      8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x28#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x20#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x18#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x10#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x8#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x120#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x48#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem entry_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE1 d x t₀) =
      c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x120#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x48#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e1_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE1 d x t₀) =
      Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x120#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x48#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ ((8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, ArgsW_open, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e1_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE2 d x t₀) =
      Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ ((8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, ArgsW_open, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e2_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE2 d x t₀) =
      8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e2_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE3 d x t₀) =
      c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e3_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE3 d x t₀) =
      8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e3_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE4 d x t₀) =
      c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e4_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE4 d x t₀) =
      8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e4_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE5 d x t₀) =
      c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e5_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE5 d x t₀) =
      Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ ((8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, ArgsW_open, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e5_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE6 d x t₀) =
      Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ ((8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, ArgsW_open, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e6_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE6 d x t₀) =
      8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e6_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE7 d x t₀) =
      c8 (t₀.regs.get64 .rsp - 0x100#64) (K (192 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf8#64) (K (256 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf0#64) (K (448 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa0#64) (K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x98#64) (qmfWin d + K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x90#64) (qmfWin d + K (4 * (128 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x88#64) (qmfWin d + K (4 * (192 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x80#64) (qmfWin d + K (4 * (256 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e7_pre (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (FrE7 d x t₀) =
      8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x100#64) (K (192 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf8#64) (K (256 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf0#64) (K (448 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa0#64) (K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x98#64) (qmfWin d + K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x90#64) (qmfWin d + K (4 * (128 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x88#64) (qmfWin d + K (4 * (192 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x80#64) (qmfWin d + K (4 * (256 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

theorem e7_post (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (VC : Mem 64 → Prop) :
    T d k Ctx fs x ra t₀ VC (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))) =
      c8 (t₀.regs.get64 .rsp - 0x118#64) (qmfWin d) ⋆ (c8 (t₀.regs.get64 .rsp - 0x110#64) (K (128 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe8#64) (K (512 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x78#64) (qmfWin d + K (4 * (448 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x70#64) (qmfWin d + K (4 * (512 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (VC ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x100#64) (K (192 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf8#64) (K (256 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf0#64) (K (448 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa0#64) (K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x98#64) (qmfWin d + K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x90#64) (qmfWin d + K (4 * (128 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x88#64) (qmfWin d + K (4 * (192 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x80#64) (qmfWin d + K (4 * (256 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀)))))))))))))))))))))))))))))))))))))))))))) := by
  simp -implicitDefEqProofs only [T, Hid, Saved, BlankL, BlankS, Locals, Fr, FrE1, FrE2, FrE3, FrE4, FrE5, FrE6, FrE7, Std.ExtHashMap.sep_assoc]
  ac_rfl

/-- The table at `.e1`, its memory as `entry_post` arranges it. -/
theorem e1_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = arg5 t₀
      ∧ (s.dmem =⋆ c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x120#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x48#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e1" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = arg5 t₀
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE1 d x t₀))
  rw [entry_post]
  exact h

/-- The table at `.e2`, its memory as `e1_post` arranges it. -/
theorem e2_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d
      ∧ (s.dmem =⋆ Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ ((8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e2" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE2 d x t₀))
  rw [e1_post]
  exact h

/-- The table at `.e3`, its memory as `e2_post` arranges it. -/
theorem e3_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xd0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e3" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE3 d x t₀))
  rw [e2_post]
  exact h

/-- The table at `.e4`, its memory as `e3_post` arranges it. -/
theorem e4_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d) ∧ s.regs.get64 .rax = K (384 / 2 ^ d)
      ∧ (s.dmem =⋆ c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xc0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e4" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .rcx = K d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d) ∧ s.regs.get64 .rax = K (384 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE4 d x t₀))
  rw [e3_post]
  exact h

/-- The table at `.e5`, its memory as `e4_post` arranges it. -/
theorem e5_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x108#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e5" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE5 d x t₀))
  rw [e4_post]
  exact h

/-- The table at `.e6`, its memory as `e5_post` arranges it. -/
theorem e6_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ ((8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x100#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xf0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xa0#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x98#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x90#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x88#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e6" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r13 = K (128 / 2 ^ d) ∧ s.regs.get64 .rdi = K (2304 - 1152 / 2 ^ d) ∧ s.regs.get64 .r8 = K (64 / 2 ^ d) ∧ s.regs.get64 .r9 = K (192 / 2 ^ d) ∧ s.regs.get64 .r10 = K (256 / 2 ^ d) ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE6 d x t₀))
  rw [e5_post]
  exact h

/-- The table at `.e7`, its memory as `e6_post` arranges it. -/
theorem e7_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) :
    (QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d) ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ (s.dmem =⋆ c8 (t₀.regs.get64 .rsp - 0x100#64) (K (192 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf8#64) (K (256 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf0#64) (K (448 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa0#64) (K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x98#64) (qmfWin d + K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x90#64) (qmfWin d + K (4 * (128 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x88#64) (qmfWin d + K (4 * (192 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x80#64) (qmfWin d + K (4 * (256 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x118#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x110#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0xe8#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))))
      → table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e7" s := by
  intro h
  show QmfC d fs x t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rbx = arg5 t₀ ∧ s.regs.get64 .r14 = arg4 t₀ ∧ s.regs.get64 .rsi = qmfWin d ∧ s.regs.get64 .r11 = K (448 / 2 ^ d) ∧ s.regs.get64 .r12 = K (512 / 2 ^ d) ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff) (FrE7 d x t₀))
  rw [e6_post]
  exact h

/-- The loop head's table entry from the frame the prologue leaves (`e7_post`). -/
theorem L9fd2_tbl (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ s : MachineData) (hC : QmfC d fs x t₀)
    (hrsp : s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x128#64)
    (hrbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (hrbx : s.regs.get64 .rbx = arg5 t₀) (hr14 : s.regs.get64 .r14 = arg4 t₀)
    (hrax : s.regs.get64 .rax = 32#64) (hr13 : s.regs.get64 .r13 = K (128 / 2 ^ d))
    (hm : s.dmem =⋆ c8 (t₀.regs.get64 .rsp - 0x118#64) (qmfWin d) ⋆ (c8 (t₀.regs.get64 .rsp - 0x110#64) (K (128 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe8#64) (K (512 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x78#64) (qmfWin d + K (4 * (448 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x70#64) (qmfWin d + K (4 * (512 / 2 ^ d))) ⋆ (Hid (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64) ⋆ (DataW d Ctx x t₀ Std.ExtHashMap.emp ⋆ (Int.toBytes 4 x.off.toInt =@ x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x120#64) (arg3 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x108#64) (K (64 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x100#64) (K (192 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf8#64) (K (256 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xf0#64) (K (448 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xe0#64) (K (704 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd8#64) (qmfWin d + K (4 * (320 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xd0#64) (K (768 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc8#64) (K (960 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xc0#64) (K (1024 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb8#64) (K (1216 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0xb0#64) (qmfWin d + K (4 * (384 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa8#64) (qmfWin d + K (4 * (576 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0xa0#64) (K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x98#64) (qmfWin d + K (4 * (64 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x90#64) (qmfWin d + K (4 * (128 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x88#64) (qmfWin d + K (4 * (192 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x80#64) (qmfWin d + K (4 * (256 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x68#64) (K (4 * (1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x60#64) (K (2304 - 1152 / 2 ^ d)) ⋆ (c8 (t₀.regs.get64 .rsp - 0x58#64) (x.v0 + K (4 * (2304 - 1152 / 2 ^ d))) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (x.mdctBuf + 256#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg1 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x38#64) (arg2 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12) ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (Rest x.R ra t₀))))))))))))))))))))))))))))))))))))))))))))) :
    table d k Ctx fs x ra t₀ "sbr_qmf_synthesis.L9fd2" s := by
  have hm' : s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 x.off.toInt =@ x.vOff)
      (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))) := by
    rw [e7_post]; exact hm
  have hl : Mem.loadInt s.dmem x.vOff 4 = some (Int.ofBytes (Int.toBytes 4 x.off.toInt)) :=
    Mem.Val.loadInt hm'
      (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
      (Int.toBytes_length _ _) (by decide)
  have hj : jOf t₀ s = 0 := by simp -implicitDefEqProofs only [jOf, hrbx, BitVec.sub_self, BitVec.toNat_zero]
  have hv : VOffOk' d x.off (vo x s) := by
    simp -implicitDefEqProofs only [vo, VOffOk', hl, Option.getD_some, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    exact ⟨off_le_vhi d x.off hC.1 hC.2.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.2.2.2.2⟩
  have hm'' : s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 (vo x s) =@ x.vOff)
      (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))) := by
    simp -implicitDefEqProofs only [vo, hl, Option.getD_some, Int.toBytes_ofBytes_toBytes]; exact hm'
  show QmfC d fs x t₀ ∧ LoopRegs d t₀ s
      ∧ s.regs.get64 .rax = K (32 - jOf t₀ s / 256) ∧ s.regs.get64 .r13 = K (128 / 2 ^ d)
      ∧ VOffOk' d x.off (vo x s)
      ∧ (s.dmem =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 (vo x s) =@ x.vOff)
          (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))))
  refine ⟨hC, ⟨hrsp, hrbp, ?_, ?_, ?_⟩, ?_, hr13, hv, hm''⟩
  · rw [hj]
  · rw [hj]; decide
  · rw [hr14, hj]; simp -implicitDefEqProofs only [Nat.zero_div, K, BitVec.add_zero]
  · rw [hrax, hj]

omit [CodeEnv] in
/-- (block-specific) The stack-argument addresses of `.e5` (`0x18(%rbp)`, `0x10(%rbp)`). -/
theorem e5_a24 (a : BitVec 64) : a - 8#64 + 0 + Int64.toBitVec 24 = a + 16#64 := by
  rw [show Int64.toBitVec 24 = 24#64 from rfl]; bv_omega

omit [CodeEnv] in
theorem e5_a16 (a : BitVec 64) : a - 8#64 + 0 + Int64.toBitVec 16 = a + 8#64 := by
  rw [show Int64.toBitVec 16 = 16#64 from rfl]; bv_omega

/-! ## NEW LEMMAS (vofs) -/

/-- (block-specific: `lend` → `.L9fd2`) The loop head's memory from the end
of the loop body: the `*v_off` cell read back as the loop head names it, the
counter slot forgotten (the head rewrites it). -/
theorem T_head {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {m : Mem 64} {v : Int} {w : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 v =@ x.vOff)
      (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w))) :
    m =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 ((Mem.loadInt m x.vOff 4).getD 0) =@ x.vOff)
      (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))) := by
  have hl : Mem.loadInt m x.vOff 4 = some (Int.ofBytes (Int.toBytes 4 v)) :=
    Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
      (Int.toBytes_length 4 v) (by decide)
  rw [hl, Option.getD_some, Int.toBytes_ofBytes_toBytes]
  have e : Mem.Entails (T d k Ctx fs x ra t₀ (Int.toBytes 4 v =@ x.vOff)
      (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w)))
      (T d k Ctx fs x ra t₀ (Int.toBytes 4 v =@ x.vOff)
      (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64)))) :=
    Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Mem.Entails.forget8 _ _ (Mem.Entails.refl _)))))))
  exact e m h

omit [CodeEnv] in
/-- `Entails` in both parts of a separating conjunction. -/
theorem Entails_sep_mono {X Y K K' : Mem 64 → Prop} (e₁ : Mem.Entails X Y)
    (e₂ : Mem.Entails K K') : Mem.Entails (X ⋆ K) (Y ⋆ K') := by
  intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
  exact ⟨m₁, m₂, hd, hm, e₁ m₁ h₁, e₂ m₂ h₂⟩

omit [CodeEnv] in
/-- The `*v_off` cell after the update, `n = (v - v0) / 4` with `v` at most 6656
bytes into `v0` and 32-aligned there, meets `VOffW`. -/
theorem voffw_of {a : BitVec 64} {n : Nat} (hn : n ≤ 1664) (h8 : n % 8 = 0) :
    Mem.Entails (Int.toBytes 4 (n : Int) =@ a) (VOffW a) := by
  intro m h
  refine ⟨BitVec.ofInt 32 (n : Int), ?_, ?_, ?_⟩
  · rw [BitVec.toInt_ofInt32_natCast _ (by omega)]; omega
  · rw [BitVec.toNat_ofInt32_natCast _ (by omega)]; exact h8
  · rw [BitVec.toInt_ofInt32_natCast _ (by omega)]; exact h

/-- (block-specific: `lend` → `.La125`) The exit's memory from the end of the
loop body: the `*v_off` cell as `VOffW` (the value of the last update), the
spill slots forgotten. -/
theorem T_exit {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {m : Mem 64} {n : Nat} {w : BitVec 64}
    (hn : n ≤ 1664) (h8 : n % 8 = 0)
    (h : m =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 (n : Int) =@ x.vOff)
      (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w))) :
    m =⋆ T d k Ctx fs x ra t₀ (VOffW x.vOff)
      (fun K => BlankLW (t₀.regs.get64 .rsp) ⋆ Saved t₀ K) := by
  have e : Mem.Entails (T d k Ctx fs x ra t₀ (Int.toBytes 4 (n : Int) =@ x.vOff)
      (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w)))
      (T d k Ctx fs x ra t₀ (VOffW x.vOff)
      (fun K => BlankL (t₀.regs.get64 .rsp) (Saved t₀ K))) := by
    refine Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left ?_))
    refine Entails_sep_mono (voffw_of hn h8) ?_
    refine Mem.Entails.sep_left (Mem.Entails.sep_left ?_)
    repeat (first | exact Mem.Entails.refl _ | refine Mem.Entails.forget8 _ _ ?_)
  have := e m h
  simpa only [BlankLW_open] using this

/-- (block-specific: `.L9ff9`) The store `mov %eax,(%rcx)` into the
`*v_off` cell of the table's memory. -/
theorem T_store_vc {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ (4 ?@ x.vOff) FR) (v : Int) :
    m.storeInt x.vOff 4 v =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 v =@ x.vOff) FR := by
  have h' := Mem.Block.storeInt_val h
    (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) v
  simp -implicitDefEqProofs only [T] at h' ⊢
  exact Mem.ac h'

/-- (block-specific: `.L9ff9`) The stack arguments `v0`, `v_off`, `div`
read from the table's memory. -/
theorem T_args {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC FR) :
    m.loadInt (t₀.regs.get64 .rsp + 16#64) 8 = some (Int.ofBytes (Int.toBytes 8 x.v0.toInt))
    ∧ m.loadInt (t₀.regs.get64 .rsp + 24#64) 8 = some (Int.ofBytes (Int.toBytes 8 x.vOff.toInt))
    ∧ m.loadInt (t₀.regs.get64 .rsp + 32#64) 4 = some (Int.ofBytes (Int.toBytes 4 (d : Int))) := by
  simp -implicitDefEqProofs only [T, ArgsW_open] at h
  exact ⟨Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide),
    Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide),
    Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
      _) _) _) _) _) _)
      (Int.toBytes_length _ _) (by decide)⟩

/-- (block-specific: `.L9ff9`) The loop counter's slot read from the
table's memory. -/
theorem T_ctr {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop} {m : Mem 64} {w : BitVec 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w))) :
    m.loadInt (t₀.regs.get64 .rsp - 0x128#64) 8 = some (Int.ofBytes (Int.toBytes 8 w.toInt)) :=
  Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
    (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

omit [CodeEnv] in
/-- (block-specific: `.L9ff9`) The frame addresses the block reads, from
`rbp = rsp₀ - 8`. Stated closed: `bv_omega` in the block's context would
preprocess its memory facts. -/
theorem l9ff9_addrs (r : BitVec 64) :
    r - 8#64 + 0 + Int64.toBitVec 32 = r + 24#64 ∧ r - 8#64 + 0 + Int64.toBitVec 24 = r + 16#64
    ∧ r - 8#64 + Int64.toBitVec 40 = r + 32#64 ∧ r - 8#64 - 288#64 = r - 0x128#64 := by
  rw [show Int64.toBitVec 32 = 32#64 from rfl, show Int64.toBitVec 24 = 24#64 from rfl,
    show Int64.toBitVec 40 = 40#64 from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> bv_omega

omit [CodeEnv] in
/-- (block-specific: `.L9ff9`) `cmpl $0, div` on the `div` cell read back. -/
theorem zf_div0 (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 ((0 : Nat) : Int)))
      - BitVec.setWidth 32 0#64) f).zf = true := rfl

omit [CodeEnv] in
theorem zf_div1 (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 ((1 : Nat) : Int)))
      - BitVec.setWidth 32 0#64) f).zf = false := rfl

omit [CodeEnv] in
/-- (block-specific: `.L9ff9`, VInv) The new `v` offset in bytes, `4 * (c - r)`,
    is 32-aligned when `c` and `r` are multiples of 8. -/
theorem vinv_mod32 (c r : BitVec 32) (h8 : c.toNat % 8 = 0) (hr0 : 0 ≤ r.toInt)
    (hrc : r.toInt ≤ c.toInt) (hr8 : r.toInt % 8 = 0) :
    4 * (c.toInt - r.toInt).toNat % 32 = 0 := by
  have hn := BitVec.toNat_eq_toInt_of_nonneg c (by omega)
  omega

/-! ## NEW LEMMAS (l9fd2) -/

section L9fd2Lemmas

omit [CodeEnv] in
/-- (block-specific: `.L9fd2`) The frame addresses the block touches, from
`rbp = rsp₀ - 8`. Stated closed (no `bv_omega` in the block context). -/
theorem fd2_addrs (r : BitVec 64) :
    r - 8#64 + Int64.toBitVec (-288) = r - 0x128#64 ∧ r - 8#64 + 0 + Int64.toBitVec 32 = r + 24#64
    ∧ ∀ a : BitVec 64, a + Int64.toBitVec 0 = a := by
  refine ⟨?_, ?_, fun a => ?_⟩
  · rw [show Int64.toBitVec (-288) = 0xFFFFFFFFFFFFFEE0#64 from rfl]; bv_omega
  · rw [show Int64.toBitVec 32 = 32#64 from rfl]; bv_omega
  · rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]

/-- (block-specific: `.L9fd2`) The store `mov %rax,-0x120(%rbp)` into the
blank counter slot. -/
theorem T_store_ctr {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))))
    (w : BitVec 64) :
    m.storeInt (t₀.regs.get64 .rsp - 0x128#64) 8 w.toInt
      =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w)) := by
  have h' := Mem.Block.storeInt_val h (Mem.Split.right (Mem.Split.right (Mem.Split.right
    (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) w.toInt
  simp -implicitDefEqProofs only [T, Fr, Locals, Saved, c8] at h' ⊢
  exact Mem.ac h'

/-- (block-specific: `.L9fd2`) Forget the `*v_off` cell's value. -/
theorem T_forget_vc {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {m : Mem 64} {v : Int}
    (h : m =⋆ T d k Ctx fs x ra t₀ (Int.toBytes 4 v =@ x.vOff) FR) :
    m =⋆ T d k Ctx fs x ra t₀ (4 ?@ x.vOff) FR := by
  have e : Mem.Entails (T d k Ctx fs x ra t₀ (Int.toBytes 4 v =@ x.vOff) FR)
      (T d k Ctx fs x ra t₀ (4 ?@ x.vOff) FR) := by
    refine Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left ?_))
    exact Mem.Entails.forget (Mem.Split.here _ _) (Mem.Entails.refl _) (Int.toBytes_length 4 v)
      (by decide)
  exact e m h

/-- (block-specific: `.L9fd2`) `T_store_ctr` with the stored value and the
cell's value related by an equation (the register vs. the table's `K` form). -/
theorem T_store_ctr' {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64))))
    (w w' : BitVec 64) (hw : w = w') :
    m.storeInt (t₀.regs.get64 .rsp - 0x128#64) 8 w.toInt
      =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (c8 (t₀.regs.get64 .rsp - 0x128#64) w')) := by
  subst hw; exact T_store_ctr h w

/-- (block-specific: `.L9fd2`) The blank counter slot can be written (its load succeeds). -/
theorem T_ctr_isSome {d k : Nat} {Ctx : BitVec 64 → Mem 64 → Prop} {fs : QmfFns} {x : QmfArgs}
    {ra : Int64} {t₀ : MachineData} {VC : Mem 64 → Prop} {m : Mem 64}
    (h : m =⋆ T d k Ctx fs x ra t₀ VC (Fr d x t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x128#64)))) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x128#64) 8).isSome = true :=
  Mem.Block.loadInt_isSome_at h (Mem.Split.right (Mem.Split.right (Mem.Split.right
    (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)

end L9fd2Lemmas

/-! ## The block lemmas

`ProcSpec.of_cfg_post`'s block obligation at one label (`BlockOb`), proved
by one theorem per block (`blk_<label>`), each with its own heartbeat budget,
so that the blocks elaborate in parallel (`cfg_block` opens each);
`spec` dispatches on the label. -/

/-- The block obligation of `ProcSpec.of_cfg_post` at label `l` of `body`. -/
abbrev BlockOb (d k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns) (x : QmfArgs)
    (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table d k Ctx fs x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table d k Ctx fs x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table d k Ctx fs x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' d k Ctx fs x ra t₀ s) ⦄

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_entry (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hs, hC, hm⟩, hn⟩ := hs₀
    rw [entry_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e1_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero, BitVec.sub_sub_eight, BitVec.reduceAdd] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_e1 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e1" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hg4, hg5, hm⟩, hn⟩ := hs₀
    rw [e1_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB4 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-280)) 8).isSome = true := by
      rw [hrbp, qa_118]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    have hB7 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-48)) 8).isSome = true := by
      rw [hrbp, qa_30]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    have hB5 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-64)) 8).isSome = true := by
      rw [hrbp, qa_40]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    have hB6 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-56)) 8).isSome = true := by
      rw [hrbp, qa_38]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-280)) hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (by rw [hrbp, qa_118]) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-48)) (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (by rw [hrbp, qa_30]) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-64)) (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (by rw [hrbp, qa_40]) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-56)) (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (by rw [hrbp, qa_38]) (v := v4)
    clear hS1 hS2 hS3
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e2_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3, hg4, hg5,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_e2 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e2" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hm⟩, hn⟩ := hs₀
    rw [e2_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB0 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-96)) 8).isSome = true := by
      rw [hrbp, qa_60]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.here _ _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-96)) hm (Mem.Split.here _ _) (Mem.Split.here _ _) (by rw [hrbp, qa_60]) (v := v1)
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e3_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_e3 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e3" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hm⟩, hn⟩ := hs₀
    rw [e3_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB0 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-216)) 8).isSome = true := by
      rw [hrbp, qa_d8]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.here _ _)
    have hB1 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-208)) 8).isSome = true := by
      rw [hrbp, qa_d0]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.here _ _) _)
    have hB2 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-200)) 8).isSome = true := by
      rw [hrbp, qa_c8]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
    have hB3 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-192)) 8).isSome = true := by
      rw [hrbp, qa_c0]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-216)) hm (Mem.Split.here _ _) (Mem.Split.here _ _) (by rw [hrbp, qa_d8]) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-208)) (hS1 v1) (Mem.Split.right (Mem.Split.here _ _) _) (Mem.Split.right (Mem.Split.here _ _) _) (by rw [hrbp, qa_d0]) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-200)) (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (by rw [hrbp, qa_c8]) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-192)) (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (by rw [hrbp, qa_c0]) (v := v4)
    clear hS1 hS2 hS3
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e4_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_e4 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e4" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11, hm⟩, hn⟩ := hs₀
    rw [e4_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB0 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-184)) 8).isSome = true := by
      rw [hrbp, qa_b8]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.here _ _)
    have hB1 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-176)) 8).isSome = true := by
      rw [hrbp, qa_b0]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.here _ _) _)
    have hB2 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-168)) 8).isSome = true := by
      rw [hrbp, qa_a8]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
    have hB3 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-160)) 8).isSome = true := by
      rw [hrbp, qa_a0]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-184)) hm (Mem.Split.here _ _) (Mem.Split.here _ _) (by rw [hrbp, qa_b8]) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-176)) (hS1 v1) (Mem.Split.right (Mem.Split.here _ _) _) (Mem.Split.right (Mem.Split.here _ _) _) (by rw [hrbp, qa_b0]) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-168)) (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (by rw [hrbp, qa_a8]) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-160)) (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (by rw [hrbp, qa_a0]) (v := v4)
    clear hS1 hS2 hS3
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e5_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hg10, hg11,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_e5 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e5" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hm⟩, hn⟩ := hs₀
    rw [e5_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB5 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-88)) 8).isSome = true := by
      rw [hrbp, qa_58]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    have hB6 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-80)) 8).isSome = true := by
      rw [hrbp, qa_50]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    have hB7 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-72)) 8).isSome = true := by
      rw [hrbp, qa_48]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    have hB4 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-256)) 8).isSome = true := by
      rw [hrbp, qa_100]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-88)) hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (by rw [hrbp, qa_58]) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-80)) (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (by rw [hrbp, qa_50]) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-72)) (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (by rw [hrbp, qa_48]) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-256)) (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (by rw [hrbp, qa_100]) (v := v4)
    clear hS1 hS2 hS3
    have hvA : ∀ v, Mem.loadInt s₀.dmem (s₀.regs.get64 .rbp + 0 + Int64.toBitVec 24) 8 = some v →
        BitVec.ofInt 64 v = x.v0 := by
      intro v h
      rw [hrbp, e5_a24, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _)
        (Int.toBytes_length _ _) (by decide)] at h
      cases h
      rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    have hvB : ∀ v, Mem.loadInt s₀.dmem (s₀.regs.get64 .rbp + 0 + Int64.toBitVec 16) 8 = some v →
        BitVec.ofInt 64 v = x.mdctBuf := by
      intro v h
      rw [hrbp, e5_a16, Mem.Val.loadInt hm (Mem.Split.here _ _)
        (Int.toBytes_length _ _) (by decide)] at h
      cases h
      rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e6_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try dsimp only at hn ⊢
    all_goals try simp -implicitDefEqProofs only [AddrIndex.offset64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_e6 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e6" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9, hm⟩, hn⟩ := hs₀
    rw [e6_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB3 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-152)) 8).isSome = true := by
      rw [hrbp, qa_98]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
    have hB4 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-144)) 8).isSome = true := by
      rw [hrbp, qa_90]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    have hB5 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-136)) 8).isSome = true := by
      rw [hrbp, qa_88]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    have hB0 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-248)) 8).isSome = true := by
      rw [hrbp, qa_f8]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.here _ _)
    have hB6 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-128)) 8).isSome = true := by
      rw [hrbp, qa_80]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    have hB1 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-240)) 8).isSome = true := by
      rw [hrbp, qa_f0]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.here _ _) _)
    have hB7 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-120)) 8).isSome = true := by
      rw [hrbp, qa_78]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    have hB2 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-232)) 8).isSome = true := by
      rw [hrbp, qa_e8]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-152)) hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (by rw [hrbp, qa_98]) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-144)) (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (by rw [hrbp, qa_90]) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-136)) (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (by rw [hrbp, qa_88]) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-248)) (hS3 v1 v2 v3) (Mem.Split.here _ _) (Mem.Split.here _ _) (by rw [hrbp, qa_f8]) (v := v4)
    have hS5 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-128)) (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (by rw [hrbp, qa_80]) (v := v5)
    have hS6 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) (v6 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-240)) (hS5 v1 v2 v3 v4 v5) (Mem.Split.right (Mem.Split.here _ _) _) (Mem.Split.right (Mem.Split.here _ _) _) (by rw [hrbp, qa_f0]) (v := v6)
    have hS7 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) (v6 : Int) (v7 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-120)) (hS6 v1 v2 v3 v4 v5 v6) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (by rw [hrbp, qa_78]) (v := v7)
    have hS8 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) (v6 : Int) (v7 : Int) (v8 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-232)) (hS7 v1 v2 v3 v4 v5 v6 v7) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (by rw [hrbp, qa_e8]) (v := v8)
    clear hS1 hS2 hS3 hS4 hS5 hS6 hS7
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try refine ⟨e7_tbl _ _ _ _ _ _ _ _ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hg8, hg9,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_e7 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.e7" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "e7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hrsp, hrbp, hg0, hg1, hg2, hg3, hg4, hg5, hm⟩, hn⟩ := hs₀
    rw [e7_pre] at hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hB3 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-112)) 8).isSome = true := by
      rw [hrbp, qa_70]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
    have hB0 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-272)) 8).isSome = true := by
      rw [hrbp, qa_110]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.here _ _)
    have hB2 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-224)) 8).isSome = true := by
      rw [hrbp, qa_e0]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
    have hB4 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-104)) 8).isSome = true := by
      rw [hrbp, qa_68]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    have hB1 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + Int64.toBitVec (-264)) 8).isSome = true := by
      rw [hrbp, qa_108]; exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.here _ _) _)
    have hS1 := fun (v1 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-112)) hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (by rw [hrbp, qa_70]) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-272)) (hS1 v1) (Mem.Split.here _ _) (Mem.Split.here _ _) (by rw [hrbp, qa_110]) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-224)) (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (by rw [hrbp, qa_e0]) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-104)) (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (by rw [hrbp, qa_68]) (v := v4)
    have hS5 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) => store_keep_at (b := s₀.regs.get64 .rbp + Int64.toBitVec (-264)) (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.here _ _) _) (Mem.Split.right (Mem.Split.here _ _) _) (by rw [hrbp, qa_108]) (v := v5)
    clear hS1 hS2 hS3 hS4
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    all_goals vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_qmf_synthesis.L9fd2") ⟨by decide, L9fd2_tbl _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [shrCl32, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hg0, hg1, hg2, hg3, hg4, hg5,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceShiftRight,
      BitVec.toNat_ofNat, AddrIndex.offset64, Nat.zero_ne_one, Nat.one_ne_zero] at hm ⊢
    all_goals try dsimp only at hn hm ⊢
    all_goals first | decide | omega | with_reducible assumption | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_L9df0 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.L9df0" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "L9df0"
    qmf_call [T_ld_30] ⟨⟨hd0, hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, hm⟩, hn⟩ using
      MachineWP.call_mem_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀)))) fs.negOdd64
        (Kraken.Executable.ProcSpec.widen (k := k) hNeg (Nat.zero_le k) (by omega))
      carve apply DataW_carve_negodd; grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_c1 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.c1" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "c1"
    qmf_callA [T_ld_38, T_lda_10, T_ld_40] ⟨⟨hd0, hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, hm⟩, hn⟩ using
      MachineWP.call_reg_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀))))))) fs.tx
        (Kraken.Executable.ProcSpec.widen (k := k) hTx (Nat.le_refl k) (by omega))
      carve apply DataW_carve_tx (hi := false) <;> grind_cells'

set_option maxRecDepth 100000 in
theorem blk_c2 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.c2" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "c2"
    qmf_call [T_ld_48] ⟨⟨hd0, hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, h12, h15, hm⟩, hn⟩ using
      MachineWP.call_reg_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀)))) fs.tx
        (Kraken.Executable.ProcSpec.widen (k := k) hTx (Nat.le_refl k) (by omega))
      carve apply DataW_carve_tx (hi := true) <;> grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_c3 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.c3" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "c3"
    qmf_callA [T_lda_10, T_ld_30] ⟨⟨hd0, hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, h12, hm⟩, hn⟩ using
      MachineWP.call_mem_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀))))))) fs.deintBfly
        (Kraken.Executable.ProcSpec.widen (k := k) hDB (Nat.zero_le k) (by omega))
      carve apply DataW_carve_bfly <;> grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9e42 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.L9e42" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "L9e42"
    qmf_eblock hFm fs.fmul [T_ld_110, T_ld_100, T_ld_118]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f1 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f1" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f1"
    qmf_fblock hFma fs.fmulAdd [T_ld_f8, T_ld_90]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f2 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f2" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f2"
    qmf_fblock hFma fs.fmulAdd [T_ld_f0, T_ld_88]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f3 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f3" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f3"
    qmf_fblock hFma fs.fmulAdd [T_ld_e8, T_ld_80]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f4 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f4" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f4"
    qmf_fblock hFma fs.fmulAdd [T_ld_e0, T_ld_78]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f5 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f5" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f5"
    qmf_fblock hFma fs.fmulAdd [T_ld_d8, T_ld_d0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f6 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f6" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f6"
    qmf_fblock hFma fs.fmulAdd [T_ld_c8, T_ld_a8]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f7 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f7" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f7"
    qmf_fblock hFma fs.fmulAdd [T_ld_c0, T_ld_70]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f8 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f8" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f8"
    qmf_fblock hFma fs.fmulAdd [T_ld_b8, T_ld_68]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_f9 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.f9" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "f9"
    qmf_fblock hFma fs.fmulAdd [T_ld_b0, T_ld_a0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_lend (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.lend" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "lend"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, hm⟩, hn⟩ := hs₀
    have hL0 := T_ld_98 hm hrbp
    have hL1 := T_ld_108 hm hrbp
    have hL2 := T_ldc hm hrbp
    have hL3 : Mem.loadInt s₀.dmem (s₀.regs.get64 .rbp - 288#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (K (32 - jOf t₀ s₀ / 256)).toInt)) := by
      rw [hrbp, show t₀.regs.get64 .rsp - 8#64 - 288#64 = t₀.regs.get64 .rsp - 0x128#64 by bv_omega]
      exact T_ctr hm
    have hmH := T_head hm
    have hmX := T_exit (by have := hV.2.2; omega) (by have := hV.1; omega) hm
    have hl : Mem.loadInt s₀.dmem x.vOff 4
        = some (Int.ofBytes (Int.toBytes 4 ((vbOf x s₀ / 4 : Nat) : Int))) :=
      Mem.Val.loadInt hm
        (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
        (Int.toBytes_length _ _) (by decide)
    have h8 : (BitVec.ofInt 32 ((Mem.loadInt s₀.dmem x.vOff 4).getD 0)).toNat % 8 = 0 := by
      rw [hl, Option.getD_some, BitVec.ofInt32_ofBytes_toBytes4,
        BitVec.toNat_ofInt32_natCast _ (by have := hV.2.2; omega)]
      have := hV.1; omega
    have hb : (BitVec.ofInt 32 ((Mem.loadInt s₀.dmem x.vOff 4).getD 0)).toInt ≤ vhi d x.off := by
      rw [hl, Option.getD_some, BitVec.ofInt32_ofBytes_toBytes4,
        BitVec.toInt_ofInt32_natCast _ (by have := hV.2.2; omega)]
      have hF := vfacts d x.off hC.1
      have h2 := hV.2.1
      revert hF h2
      obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
      all_goals
        intro hF h2
        simp -implicitDefEqProofs only [Nat.reducePow, Nat.reduceDiv, Nat.reduceMul] at hF h2
        omega
    clear hl
    clear hNeg hDN hDB hTx hFm hFma hMc
    vcgen
    qmf_norm
    case vc1.inl | vc1.inr | vc2.inl | vc2.inr | vc3.inl | vc3.inr =>
      first | (simp -implicitDefEqProofs only [hL0, hL1, hL2, Option.isSome_some]; done) | (clear hmH hmX; grind_cells')
    case vc4.inl | vc4.inr =>
      left
      refine Table.ofLabels_at (l := "sbr_qmf_synthesis.La125") ?_
      refine ⟨by decide, ⟨hrsp, hrbp, hmX⟩, ?_⟩
      clear hmH hmX
      left
      show 0 < _
      qmf_slots [hL0, hL1, hL2, hL3]
      all_goals grind_cells'
    case vc5.inl | vc5.inr =>
      clear hmX
      and_intros
      all_goals first | with_reducible exact hmH | with_reducible exact h8 | with_reducible exact hb | (clear hmH; qmf_slots [hL0, hL1, hL2, hL3]; all_goals grind_cells')

set_option maxRecDepth 100000 in
theorem blk_L9fd2 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.L9fd2" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "L9fd2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hrax, h13, hVO, hm⟩, hn⟩ := hs₀
    have hI := T_ctr_isSome hm
    have hS := T_store_ctr' hm (s₀.regs.get64 .rax) _ hrax
    have hK := T_ctr hS
    have hA := (T_args hS).2.1
    have hV : Mem.loadInt (Mem.storeInt s₀.dmem (t₀.regs.get64 .rsp - 0x128#64) 8
        (s₀.regs.get64 .rax).toInt) x.vOff 4 = some (Int.ofBytes (Int.toBytes 4 (vo x s₀))) :=
      Mem.Val.loadInt hS (Mem.Split.right (Mem.Split.right (Mem.Split.right
        (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hF := T_forget_vc hS
    clear hS hm
    have hr : (BitVec.setWidth 32 (s₀.regs.get64 .r13)).toInt = ((128 / 2 ^ d : Nat) : Int) := by
      rw [h13]; obtain rfl | rfl : d = 0 ∨ d = 1 := (by have := hC.1; omega) <;> decide
    have ea := fd2_addrs (t₀.regs.get64 .rsp)
    rw [← hrbp] at ea
    obtain ⟨e288, e24, e0⟩ := ea
    have e296 : s₀.regs.get64 .rbp - 288#64 = t₀.regs.get64 .rsp - 0x128#64 := by
      rw [hrbp]; exact (l9ff9_addrs _).2.2.2
    clear hNeg hDN hDB hTx hFm hFma hMc
    vcgen
    qmf_norm
    all_goals simp -implicitDefEqProofs only [e288, e24, e0, hA, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hV, Option.some.injEq,
      Option.isSome_some, Option.getD_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.setWidth_32_64_32,
      CondCode.interp_ge_cmp_toInt32, decide_eq_true_eq, decide_eq_false_iff_not] at *
    case vc4.inl | vc4.inr =>
      left
      refine Table.ofLabels_at (l := "sbr_qmf_synthesis.L9ff9") ?_
      refine ⟨by decide, ?_, ?_⟩
      all_goals try dsimp only
      all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        BitVec.setWidth_32_64_32]
      · exact ⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, h13, by rw [← hr]; assumption, hVO.1, hVO.2, hF⟩
      · right
        refine ⟨?_, by decide⟩
        rw [e296, hK, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hrax]
    case vc5.inl | vc5.inr =>
      refine ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, h13, hF⟩, ?_⟩
      rw [e296, hK, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hrax]
      try exact Nat.le_refl _
    all_goals exact hI

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_mc (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.mc" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "mc"
    qmf_callA [T_ld_50, T_lda_18, T_ld_60] ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, h13, hm⟩, hn⟩ using
      MachineWP.call_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, 4 ?@ x.vOff ⋆ (FnsW fs t₀ ⋆ (Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀))))))) "memcpy"
        (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))
      carve apply DataW_carve_memcpy <;> grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_mc1 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.mc1" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "mc1"
    intro n
    clear hNeg hDN hDB hTx hFm hFma hMc
    have hF := (vfacts d x.off hd).1
    vcgen
    qmf_norm
    all_goals try simp -implicitDefEqProofs only [BlankLW_open] at *
    all_goals grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_L9ff9 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.L9ff9" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "L9ff9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, h13, hlo, hhi, h8, hm⟩, hn⟩ := hs₀
    have hA := (T_args hm).2.1
    have hS := T_store_vc hm
    have hB1 := fun v => (T_args (hS v)).1
    have hB3 := fun v => (T_args (hS v)).2.2
    have hK := fun v => T_ctr (hS v)
    have hK0 := T_ctr hm
    clear hNeg hDN hDB hTx hFm hFma hMc
    have ea := l9ff9_addrs (t₀.regs.get64 .rsp)
    rw [← hrbp] at ea
    obtain ⟨e24, e16, e32, e296⟩ := ea
    have e0 : Int64.toBitVec 0 = 0#64 := rfl
    have hr : (BitVec.setWidth 32 (s₀.regs.get64 .r13)).toInt = ((128 / 2 ^ d : Nat) : Int) := by
      rw [h13]; obtain rfl | rfl : d = 0 ∨ d = 1 := (by have := hC.1; omega) <;> decide
    have hbr := BitVec.cltq_lea_bridge x.v0 (BitVec.setWidth 32 (s₀.regs.get64 .rax))
      (BitVec.setWidth 32 (s₀.regs.get64 .r13)) (by rw [hr]; exact Int.natCast_nonneg _) (by rw [hr]; exact hlo)
    have hc := BitVec.toNat_eq_toInt_of_nonneg (BitVec.setWidth 32 (s₀.regs.get64 .rax))
      (Int.le_trans (Int.natCast_nonneg _) hlo)
    have h8' : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat % 8 = 0 := h8
    have hC' := hC
    obtain ⟨hC0, hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9, hC10⟩ := hC'
    have hF := vfacts d x.off hd
    have hF0 := vfacts0 x.off
    have hF1 := vfacts1 x.off
    vcgen
    qmf_norm
    all_goals simp -implicitDefEqProofs only [e24, e16, e32, e0, BitVec.add_zero, hA, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hB1, hB3, Option.some.injEq,
      Option.isSome_some, Option.getD_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, CondCode.interp_z, zf_div0, zf_div1,
      Bool.true_eq_false, Bool.false_eq_true] at *
    case vc5.inl =>
      left
      refine Table.ofLabels_at (l := "sbr_qmf_synthesis.L9df0") ?_
      refine ⟨by decide, ?_, ?_⟩
      all_goals try dsimp only
      all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e296, hK, hK0,
        Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt,
        show BitVec.ofNat 64 Width.W32.bytes = 4#64 from rfl, BitVec.toNat_ofNat]
      · and_intros
        all_goals first | with_reducible rfl | with_reducible assumption | (simp -implicitDefEqProofs only [hbr.1]; exact hS _) | exact Nat.le_refl _ | (rw [hbr.2.2]; exact vinv_mod32 _ _ h8' (by rw [hr]; decide) (by rw [hr]; exact Int.le_trans (by decide) hlo) (by rw [hr]; decide)) | (rw [hbr.2.2]; omega) | (rw [hbr.2.2]; simp -implicitDefEqProofs only [show (NatCast.natCast (128:Nat) : Int) = 128 from rfl, show (NatCast.natCast (64:Nat) : Int) = 64 from rfl, show (NatCast.natCast (1152:Nat) : Int) = 1152 from rfl, show (NatCast.natCast (576:Nat) : Int) = 576 from rfl] at hr hhi hlo hF; omega)
      · left; omega
    case vc6.inr =>
      try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e296, hK, hK0,
        Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt,
        show BitVec.ofNat 64 Width.W32.bytes = 4#64 from rfl, BitVec.toNat_ofNat]
      and_intros
      all_goals first | with_reducible rfl | trivial | with_reducible assumption | (simp -implicitDefEqProofs only [hbr.1]; exact hS _) | exact Nat.le_refl _ | (rw [hbr.2.2]; exact vinv_mod32 _ _ h8' (by rw [hr]; decide) (by rw [hr]; exact Int.le_trans (by decide) hlo) (by rw [hr]; decide)) | (rw [hbr.2.2]; omega) | (rw [hbr.2.2]; simp -implicitDefEqProofs only [show (NatCast.natCast (128:Nat) : Int) = 128 from rfl, show (NatCast.natCast (64:Nat) : Int) = 64 from rfl, show (NatCast.natCast (1152:Nat) : Int) = 1152 from rfl, show (NatCast.natCast (576:Nat) : Int) = 576 from rfl] at hr hhi hlo hF; omega)
    case vc2.inl | vc2.inr => grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_ds (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.ds" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "ds"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hd1, hC, hL, hV, hm⟩, hn⟩ := hs₀
    clear hNeg hDN hDB hTx hFm hFma hMc
    subst hd1
    have hL' := hL
    obtain ⟨hrsp, hrbp, hj1, hj2, hr14⟩ := hL'
    simp -implicitDefEqProofs only [jOf] at hj1 hj2
    obtain ⟨H, eH⟩ := DataW_carve_ds 1 Ctx x t₀ Std.ExtHashMap.emp (s₀.regs.get64 .rbx)
      (s₀.regs.get64 .rbx + 0x2600#64) (by bv_omega) (by bv_omega)
    simp -implicitDefEqProofs only [T, eH] at hm
    rw [Fr_eq_tail] at hm
    have hm2 := Mem.ac (H₂ := Blocks [(lab "LCPI15_1", 4), (s₀.regs.get64 .rbx, 256),
        (s₀.regs.get64 .rbx + 0x2600#64, 128)] ⋆ (Ctr t₀ s₀
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64)
      ⋆ (H ⋆ (VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW 1 x t₀ ⋆ FrTail 1 x t₀ (Rest x.R ra t₀))))))))) hm
    clear hm
    generalize hG : (8 ?@ (t₀.regs.get64 .rsp - 0x130#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x130#64)
      ⋆ (H ⋆ (VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW 1 x t₀ ⋆ FrTail 1 x t₀ (Rest x.R ra t₀))))))) = G at hm2
    refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs ∧ (s.dmem =⋆ Blocks [(lab "LCPI15_1", 4),
        (s₀.regs.get64 .rbx, 256), (s₀.regs.get64 .rbx + 0x2600#64, 128)] ⋆ (Ctr t₀ s₀ ⋆ G))) ?_ ?_
    · measure_hb "ds-run"
        vcgen
        all_goals call_simp
        all_goals try dsimp only at *
        all_goals opaque_stores
        all_goals try simp -implicitDefEqProofs only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
          BitVec.add_zero] at *
        all_goals grind_cells'
    · measure_hb "ds-post"
        rintro s ⟨hr, hmem⟩
        have e1 : VCell x s = VCell x s₀ := by simp -implicitDefEqProofs only [VCell, vbOf, hr]
        have e2 : Ctr t₀ s = Ctr t₀ s₀ := by simp -implicitDefEqProofs only [Ctr, jOf, hr]
        have hT : s.dmem =⋆ T 1 k Ctx fs x ra t₀ (VCell x s₀) (Fr 1 x t₀ (Ctr t₀ s₀)) := by
          subst hG
          simp -implicitDefEqProofs only [T]
          rw [eH, Fr_eq_tail]
          exact Mem.ac hmem
        refine ⟨⟨rfl, hC, ?_, ?_, ?_⟩, ?_⟩
        · simp -implicitDefEqProofs only [LoopRegs, jOf, hr]; exact hL
        · simp -implicitDefEqProofs only [VInv, vbOf, hr]; exact hV
        · rw [e1, e2]; exact hT
        · show 3 * ctr s ≤ n
          rw [← hn]
          show 3 * ctr s ≤ 3 * ctr s₀
          simp -implicitDefEqProofs only [ctr, hr]
          grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_ds1 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.ds1" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "ds1"
    qmf_callA [T_ld_38, T_lda_10] ⟨⟨hd1, hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, hm⟩, hn⟩ using
      MachineWP.call_mem_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (Int.toBytes 8 x.mdctBuf.toInt =@ (t₀.regs.get64 .rsp + 8#64) ⋆ (Int.toBytes 8 x.v0.toInt =@ (t₀.regs.get64 .rsp + 16#64) ⋆ (Int.toBytes 8 x.vOff.toInt =@ (t₀.regs.get64 .rsp + 24#64) ⋆ (Int.toBytes 4 (d : Int) =@ (t₀.regs.get64 .rsp + 32#64) ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀))))))) fs.tx
        (Kraken.Executable.ProcSpec.widen (k := k) hTx (Nat.le_refl k) (by omega))
      carve apply DataW_carve_tx (hi := false) <;> grind_cells'

set_option maxRecDepth 100000 in
theorem blk_ds2 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.ds2" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "ds2"
    qmf_call [T_ld_30] ⟨⟨hd1, hC, ⟨hrsp, hrbp, hj1, hj2, hr14⟩, hV, h12, hm⟩, hn⟩ using
      MachineWP.call_mem_proc_spec_at (DataW d Ctx x t₀ Std.ExtHashMap.emp, VCell x s₀ ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ Fr d x t₀ (Ctr t₀ s₀) (Rest x.R ra t₀)))) fs.deintNeg
        (Kraken.Executable.ProcSpec.widen (k := k) hDN (Nat.zero_le k) (by omega))
      carve apply DataW_carve_dneg <;> grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_ds3 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.ds3" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "ds3"
    intro n
    clear hNeg hDN hDB hTx hFm hFma hMc
    vcgen
    qmf_norm
    all_goals grind_cells'

set_option maxRecDepth 100000 in
theorem blk_La125 (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.La125" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "La125"
    intro n
    clear hNeg hDN hDB hTx hFm hFma hMc
    vcgen
    all_goals simp -implicitDefEqProofs only [Rest] at *
    all_goals call_simp
    all_goals grind_cells'

set_option maxRecDepth 100000 in
theorem blk_done (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees' k Ctx fs)
    (x : QmfArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb d k Ctx fs x ra t₀ "sbr_qmf_synthesis.done" := by
  obtain ⟨hNeg, hDN, hDB, hTx, hFm, hFma, hMc⟩ := hc
  cfg_block
  measure_hb "done"
    intro n
    clear hNeg hDN hDB hTx hFm hFma hMc
    vcgen
    all_goals simp -implicitDefEqProofs only [Rest] at *
    all_goals call_simp
    all_goals grind_cells'

set_option maxRecDepth 100000 in
theorem spec (hpl : Program.PlacedIn body) (d k : Nat) (hd : d ≤ 1) (hk : k ≤ 2 ^ 32)
    (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) (fs : QmfFns)
    (hc : QmfCallees k Ctx TxTab fs) :
    QmfSynthesisSpec d k Ctx TxTab fs := by
  have hc' : QmfCallees' k (CT Ctx TxTab) fs := hc
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table d k (CT Ctx TxTab) fs)
    (Post' d k (CT Ctx TxTab) fs) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro x ra t₀ _ l blk hblk
    have hmem := Program.isSome_blockAt body l
    cfg_view hblk as hview
    rw [hblk, hview] at hmem
    replace hmem := hmem.symm
    clear hview
    simp -implicitDefEqProofs only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hmem
    · exact blk_entry d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e1 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e2 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e3 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e4 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e5 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e6 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_e7 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_L9df0 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_c1 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_c2 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_c3 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_L9e42 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f1 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f2 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f3 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f4 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f5 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f6 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f7 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f8 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_f9 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_lend d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_L9fd2 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_mc d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_mc1 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_L9ff9 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_ds d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_ds1 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_ds2 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_ds3 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_La125 d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
    · exact blk_done d k hd hk (CT Ctx TxTab) fs hc' x ra t₀ blk hblk
  · -- hpre
    rintro x ra t ⟨hm, hC⟩
    refine ⟨rfl, hC, ?_⟩
    have hw := CallPre.le hm
    rw [show QmfF d Ctx TxTab fs x t ⋆ x.R = DataW d (CT Ctx TxTab) x t Std.ExtHashMap.emp
        ⋆ ((Int.toBytes 4 x.off.toInt =@ x.vOff) ⋆ (FnsW fs t ⋆ (ArgsW d x t ⋆ x.R))) from by
      simp -implicitDefEqProofs only [QmfF]; rw [Std.ExtHashMap.sep_assoc, QmfData_eq]; rfl] at hm
    simp -implicitDefEqProofs only [CallPre, qmfNeed] at hm
    rw [reserve_frame k hw] at hm
    simp -implicitDefEqProofs only [T, Rest]
    rw [← frame_cells]
    exact Mem.ac hm
  · -- hpost
    rintro x ra t₀ s ⟨h0, -⟩ ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hm' := Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Mem.Entails.sep_left (Saved_blank t₀ _))))))) _ hm
    rw [BlankLW_open, ← frame_cells] at hm'
    rw [show QmfFPost d Ctx TxTab fs x t₀ ⋆ x.R = DataW d (CT Ctx TxTab) x t₀ Std.ExtHashMap.emp
        ⋆ (VOffW x.vOff ⋆ (FnsW fs t₀ ⋆ (ArgsW d x t₀ ⋆ x.R))) from by
      simp -implicitDefEqProofs only [QmfFPost]; rw [Std.ExtHashMap.sep_assoc, QmfData_eq]; rfl]
    rw [show qmfNeed k = 0x130 + k from rfl, reserve_frame k (CallPre.le h0)]
    exact Mem.ac hm'

end Kraken.Examples.Sbr.QmfSynthesis
