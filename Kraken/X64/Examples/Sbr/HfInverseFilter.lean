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
import Kraken.X64.Examples.Sbr.HfInverseFilterText

/-!
# `sbr_hf_inverse_filter` as a `ProcSpec`

`sbr_hf_inverse_filter` of `aacsbr.o` (`-c opt`), the C routine
`sbr_hf_inverse_filter(SBRDSPContext *dsp, float (*alpha0)[2],
float (*alpha1)[2], const float X_low[32][40][2], int k0)` of
`libavcodec/aacsbr_template.c`, called through `sbr->c.sbr_hf_inverse_filter`
(`aacsbr_template.c:1727`, slot set at `:1784`) as
`(&sbr->dsp, sbr->alpha0, sbr->alpha1, sbr->X_low, sbr->k[0])`.

## Contract (`HfInverseFilterSpec fa`, in `Spec.lean`)

* Memory (`HfInvF`): `X_low[0..k0)` read (320 bytes a row), `alpha0[0..k0)`,
  `alpha1[0..k0)` written (8 bytes a row), the constants `.LCPI19_0`
  (`-1.000001f`), `.LCPI19_1` (`16.0f`), `.LCPI19_2` (16-byte sign mask) and
  `ps_mask3` (read by the callee), and the slot `dsp->autocorrelate`
  (`0x38(%rdi)`) holding the callee address `fa`.  All given back.
* Conditions (`HfInvC`): `k0 ≤ 32` (low 32 bits of `r8`), `ps_mask3`
  16-aligned, `rsp + 8` 16-aligned at entry.
* Stack: `hfInvNeed = 0xa8` = own 0x78 (six saved registers, three 8-byte
  slots, the 48-byte `LOCAL_ALIGNED_16 phi[3][2][2]`) + the callee's return
  slot + its 0x28 bytes.
* Callee (`HfInvCallees fa`): *assumed* `LeafSpecAt fa 0x28 AutocorrelateF
  AutocorrelateC` (the `autocorrelate` contract of `Spec.lean`), discharged by
  `ProcSpec.widen` at the one call site (footprint carved from the arrays by
  `BW_carve`: row `k` of `X_low`, `phi`, `ps_mask3`).
* The contract is memory safety and frame only: no statement on the float
  values of `alpha0`/`alpha1`.

## Notes

* The extracted text dropped the final `retq`; the object has it at `+0x1eb`
  after `pop %rbp`.  `body` restores it behind `….done`.
* SbrWF clause requested: `k[0] ≤ 32`.  `X_low` has 32 rows and the loop
  runs `k0` of them; also `8 k0` is compared with the 64-bit row offset, so
  `k0` must be small (`k0 ≤ 32` makes the signed and unsigned readings of
  `r8d` agree and nothing wrap).  Reason it holds: `k[0] = f_master[0] ≤
  kx[1] ≤ 32` from the check at `aacsbr_template.c:573` (assuming
  `f_master` nondecreasing).  Negative check: with `k0 ≤ 32` replaced by
  `True` (scratch copy) `blk_Lbf57` (counter step `lbf57_arith`) and
  `blk_Lbf6f` (the callee's row inside `X_low`, `BW_carve`) fail.
* `ps_mask3` 16-aligned and the SysV stack alignment are needed only for the
  callee's `AutocorrelateC` (`phi = rsp₀ - 0x78` and the callee's `rsp + 8`
  are 16-aligned when `rsp₀ + 8` is: `lbf6f_align`).
* `k0 = 0` (and, outside the contract, negative `k0`) leaves through
  `test %r8d,%r8d; jle` without touching the arrays.
* The library had no `inc` rule: `MachineWP.inc_reg_w64_spec`, now in
  `Kraken.Rules.HelperLemmas` with `Mem.Blocks.Inside.of_sub2`.

## Proof

`ProcSpec.of_cfg_post` over the 14 labels; one `blk_<label>` per block, each
with `maxHeartbeats` about twice its measured cost; `spec` dispatches.  All
arrays are one `Blocks` list at the head of the memory (`BW`), loop offsets
are `toNat` facts, frame addresses are folded by closed `bv_omega` lemmas
(never `bv_omega` in a block context).  The entry block puts the seven cells
it writes in front of one `Mem.Hid` atom (`entry_pre`).  Scopes opened:
`Kraken.LeafLemmas.Offset`, `Kraken.HelperLemmas.Offset2`.

Per block (`measure_hb`, heartbeats in units of 1000 / wall ms):
`entry` 151986/15593, `e1` 32331/3511, `Lbf40` 70482/7245, `Lbf57` 7653/848,
`Lbf6f` (the call) 14307/1622, `c1` 54039/6223, `Lbfb5` 52356/6042,
`Lc000` 12561/1501, `Lc010` 52476/5956, `Lc02f` 39805/4769, `c2` 64993/7106,
`Lc0b0` 66106/7150, `Lc0dd` 139128/14778, `done` 17861/2406.
Serial sum ≈ 85 s; the whole file ≈ 37 s wall (blocks in parallel).
-/

open Kraken
open Kraken.SysV
open Mem

/-! ## The proof -/

open Kraken.X64.Parser
open Std.WP
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

-- The `inc` rule (`MachineWP.inc_reg_w64_spec`) and `Mem.Blocks.Inside.of_sub2`
-- (with its scoped `grind` pattern) are in `Kraken.Rules.HelperLemmas`.

open scoped Kraken.LeafLemmas.Offset Kraken.HelperLemmas.Offset2

namespace Kraken.Examples.Sbr.HfInverseFilter

variable [CodeEnv]

abbrev K (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

/-- The caller's memory behind the footprint: the return address and `R`. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The six saved registers (`rbp = rsp₀ - 8`). -/
abbrev Saved (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ Kt)))))

abbrev BlankS (r : BitVec 64) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x30#64)
    ⋆ (8 ?@ (r - 0x28#64)
    ⋆ (8 ?@ (r - 0x20#64)
    ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64)
    ⋆ (8 ?@ (r - 0x8#64) ⋆ Kt)))))

/-- The saved registers behind a name `grind` does not unfold. -/
def SavedW (t₀ : MachineData) : Mem 64 → Prop := Saved t₀ Std.ExtHashMap.emp

omit [CodeEnv] in
theorem SavedW_open (t₀ : MachineData) (Kt : Mem 64 → Prop) :
    SavedW t₀ ⋆ Kt = Saved t₀ Kt := by
  simp only [SavedW, Saved, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.emp_sep]

/-- All the arrays as one list, at the head of the memory (the `Blocks`
rules match `m =⋆ Blocks bs ⋆ F` only): `X_low[0..k0)`, the local `phi`
(48 bytes at `rsp₀ - 0x78`), `ps_mask3`, `alpha0`, `alpha1`, the three
constants. -/
abbrev BW (t₀ : MachineData) : Mem 64 → Prop :=
  Blocks [(arg3 t₀, 320 * hfInvN t₀), (t₀.regs.get64 .rsp - 0x78#64, 48), (lab "ps_mask3", 16),
    (arg1 t₀, 8 * hfInvN t₀), (arg2 t₀, 8 * hfInvN t₀),
    (lab "LCPI19_0", 4), (lab "LCPI19_1", 4), (lab "LCPI19_2", 16)]

/-- The memory at every label: the arrays, the callee's return-address slot,
its reservation, the function-pointer slot, the frame `FR` (applied to the
rest). -/
abbrev T (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  BW t₀ ⋆ (8 ?@ (r - 0x80#64) ⋆ (Reserve 0x28 (r - 0x80#64)
    ⋆ (FnCell (arg0 t₀ + 0x38#64) fa ⋆ FR (Rest R ra t₀))))

/-- The frame at entry: all blank. -/
abbrev Fr0 (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x40#64) ⋆ (8 ?@ (r - 0x38#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ BlankS r Kt))

/-- The frame once `dsp` is spilled (`.e1`, the exit `.Lc0dd`). -/
abbrev Fr1 (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x40#64) (arg0 t₀) ⋆ (8 ?@ (r - 0x38#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (SavedW t₀ ⋆ Kt)))

/-- The frame in the loop: `dsp` and `8 k0` spilled. -/
abbrev FrL (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x40#64) (arg0 t₀) ⋆ (c8 (r - 0x38#64) (K (8 * hfInvN t₀))
    ⋆ (8 ?@ (r - 0x48#64) ⋆ (SavedW t₀ ⋆ Kt)))

/-- The row index `k`, as `r13` holds it. -/
abbrev iOf (s : MachineData) : Nat := (s.regs.get64 .r13).toNat

/-- Registers in the loop. -/
abbrev LoopRegs (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x78#64 ∧ s.regs.get64 .rbp = r - 0x78#64 + 0x70#64
    ∧ iOf s < hfInvN t₀ ∧ (s.regs.get64 .r12).toNat = 8 * iOf s
    ∧ (s.regs.get64 .rbx - arg3 t₀).toNat = 320 * iOf s
    ∧ s.regs.get64 .r14 = arg2 t₀ ∧ s.regs.get64 .r15 = arg1 t₀

/-- The loop's facts at every loop label. -/
abbrev LoopInv (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  HfInvC t₀ ∧ LoopRegs t₀ s ∧ (s.dmem =⋆ T fa R ra t₀ (FrL t₀))

abbrev table (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "sbr_hf_inverse_filter", s => s = t₀ ∧ HfInvC t₀ ∧ (t₀.dmem =⋆ T fa R ra t₀ (Fr0 t₀))
  | "sbr_hf_inverse_filter.e1", s => HfInvC t₀ ∧ 1 ≤ hfInvN t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x78#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀
      ∧ (s.dmem =⋆ T fa R ra t₀ (Fr1 t₀))
  | "sbr_hf_inverse_filter.Lbf40", s => LoopInv fa R ra t₀ s
      ∧ (s.regs.get64 .rax - arg2 t₀).toNat = 8 * iOf s
  | "sbr_hf_inverse_filter.Lbf57", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lbf6f", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.c1", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lbfb5", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lc000", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lc010", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lc02f", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.c2", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lc0b0", s => LoopInv fa R ra t₀ s
  | "sbr_hf_inverse_filter.Lc0dd", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x78#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ (s.dmem =⋆ T fa R ra t₀ (Fr1 t₀))
  | "sbr_hf_inverse_filter.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ T fa R ra t₀ (Fr1 t₀))
  | _, _ => False

/-- The variant: `2 (2^32 - k) + 1` from the call to the bound tests,
`2 (2^32 - k)` at the two blocks behind the backward jumps (`.Lbf40`,
`.Lbf57`), where `k` is `r13` (it rises by one on the back edge
`.Lbf57 → .Lbf6f`); 0 at the exit. -/
abbrev var : Label → MachineData → Nat
  | "sbr_hf_inverse_filter.Lbf40", s => 2 * (2 ^ 32 - iOf s)
  | "sbr_hf_inverse_filter.Lbf57", s => 2 * (2 ^ 32 - iOf s)
  | "sbr_hf_inverse_filter.Lbf6f", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.c1", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.Lbfb5", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.Lc000", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.Lc010", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.Lc02f", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.c2", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.Lc0b0", s => 2 * (2 ^ 32 - iOf s) + 1
  | "sbr_hf_inverse_filter.Lc0dd", _ => 0
  | "sbr_hf_inverse_filter.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the `ret` leaves. -/
abbrev Post' (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
    ∧ SavedRegs t₀ s ∧ (s.dmem =⋆ T fa R ra t₀ (Fr1 t₀))

/-- `grind_cells` without model-based theory combination. -/
macro "grind_cells'" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

/-- The block obligation of `ProcSpec.of_cfg_post` at label `l` of `body`. -/
abbrev BlockOb (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) (l : Label) :
    Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table fa R ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table fa R ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table fa R ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' fa R ra t₀ s) ⦄

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000 in
theorem blk_done (fa : Int64) (hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.done" := by
  cfg_block
  measure_hb "done"
    intro n
    clear hA
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 280000 in
theorem blk_Lc0dd (fa : Int64) (hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lc0dd" := by
  cfg_block
  measure_hb "Lc0dd"
    intro n
    clear hA
    vcgen
    all_goals simp only [SavedW_open] at *
    all_goals call_simp
    all_goals grind_cells'

omit [CodeEnv] in
/-- The two spill slots, addressed from `rbp = (rsp₀ - 0x78) + 0x70`. -/
theorem slot_addrs (r : BitVec 64) :
    r - 0x78#64 + 0x38#64 = r - 0x40#64 ∧ r - 0x78#64 + 0x40#64 = r - 0x38#64 := by
  constructor <;> bv_omega

set_option hygiene false in
/-- The reductions after `vcgen` in a loop block: addresses normalised, the
fixed registers substituted, then `grind`. -/
macro "hf_norm" : tactic => `(tactic| (
  all_goals try subst_vars
  all_goals have hphi : ∀ c : BitVec 64, t₀.regs.get64 .rsp - 0x78#64 + 0x70#64 + c
      = t₀.regs.get64 .rsp - 0x78#64 + (0x70#64 + c) := fun c => BitVec.add_assoc _ _ _
  all_goals simp only [AddrIndex.offset64, Int64.toBitVec_zero, BitVec.add_zero, h14, h15, hrsp,
    Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMod, Nat.reducePow,
    Nat.reduceSub,
    hrbp, hphi, BitVec.reduceAdd, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    (slot_addrs (t₀.regs.get64 .rsp)).1, (slot_addrs (t₀.regs.get64 .rsp)).2] at ⊢))

set_option hygiene false in
macro "hf_close" : tactic => `(tactic| (
  hf_norm
  all_goals grind_cells'))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 150000 in
theorem blk_Lbf40 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lbf40" := by
  cfg_block
  measure_hb "Lbf40"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hax⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

/-- (block-specific: `.Lbf57`) The bound `8 k0` read back from its slot. -/
theorem T_loadK {fa : Int64} {R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ T fa R ra t₀ (FrL t₀)) :
    m.loadInt (t₀.regs.get64 .rsp - 0x38#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (K (8 * hfInvN t₀)).toInt)) :=
  Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
    (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (block-specific: `.Lbf57 → .Lc0dd`) The loop's frame forgets the bound. -/
theorem T_forgetK {fa : Int64} {R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ T fa R ra t₀ (FrL t₀)) : m =⋆ T fa R ra t₀ (Fr1 t₀) :=
  Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.sep_left (Mem.Entails.forget8 _ _ (Mem.Entails.refl _)))))) m h

omit [CodeEnv] in
/-- (block-specific: `.Lbf57`) The frame addresses, from `rbp = rsp₀ - 0x78 + 0x70`. -/
theorem lbf57_addrs (r : BitVec 64) :
    (∀ regs : Reg64s, r - 0x78#64 + 0x70#64 + AddrIndex.offset64 none regs + Int64.toBitVec (-48)
      = r - 0x38#64) ∧ r - 0x78#64 + 0x70#64 = r - 8#64 := by
  refine ⟨fun regs => ?_, by bv_omega⟩
  rw [AddrIndex.offset64_none, show Int64.toBitVec (-48) = 0xffffffffffffffd0#64 from rfl]
  bv_omega

omit [CodeEnv] in
/-- (block-specific: `.Lbf57`) The counter step: `8 (i+1) = 8 k0` iff `i + 1 = k0`, and
the new offsets do not wrap. -/
theorem lbf57_arith (k : Nat) (r12 r13 rbx b : BitVec 64) (hk : k ≤ 32) (hi : r13.toNat < k)
    (h12 : r12.toNat = 8 * r13.toNat) (hbx : (rbx - b).toNat = 320 * r13.toNat) :
    ((BitVec.ofInt 64 (K (8 * k)).toInt - (BitVec.setWidth 64 8#64 + r12) == BitVec.zero 64)
        = true ↔ r13.toNat + 1 = k)
      ∧ (r13 + 1).toNat = r13.toNat + 1
      ∧ (BitVec.setWidth 64 8#64 + r12).toNat = 8 * (r13.toNat + 1)
      ∧ (BitVec.setWidth 64 320#64 + rbx - b).toNat = 320 * (r13.toNat + 1) := by
  rw [BitVec.ofInt_toInt, beq_iff_eq, show BitVec.zero 64 = 0#64 from rfl]
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro h; have := congrArg BitVec.toNat h; simp -implicitDefEqProofs only [BitVec.toNat_sub, BitVec.toNat_add,
        BitVec.toNat_ofNat, BitVec.toNat_setWidth] at this; omega
    · intro h; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_sub, BitVec.toNat_add,
        BitVec.toNat_ofNat, BitVec.toNat_setWidth]; omega
  · bv_omega
  · bv_omega
  · have : BitVec.setWidth 64 320#64 + rbx - b = 320#64 + (rbx - b) := by bv_omega
    rw [this]; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000 in
theorem blk_Lbf57 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lbf57" := by
  cfg_block
  measure_hb "Lbf57"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    have hK := T_loadK hm
    have hF := T_forgetK hm
    have ea := lbf57_addrs (t₀.regs.get64 .rsp)
    rw [← hrbp] at ea
    obtain ⟨ea1, ea2⟩ := ea
    have ar := lbf57_arith (hfInvN t₀) _ _ _ _ hC.1 hi h12 hbx
    vcgen
    all_goals try subst_vars
    case vc1 => simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ea1, hK,
      Option.isSome_some]
    all_goals rename_i x hld hz
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ea1, hK,
      Option.some.injEq] at hld
    all_goals subst hld
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Int64.toBitVec_ofNat_norm, BitVec.ofInt64_ofBytes_toBytes8, CondCode.interp_z,
      StatusFlags.zf_from_result, ar.1] at hz
    case vc2 =>
      left
      refine Table.ofLabels_at (l := "sbr_hf_inverse_filter.Lc0dd") ?_
      refine ⟨by decide, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact hrsp
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; exact ea2
      · exact hF
      · left; show (0 : Nat) < _
        refine Nat.mul_pos (by decide) (Nat.sub_pos_of_lt ?_); omega
    case vc3 =>
      have hne := fun h => Bool.false_ne_true (hz.symm.trans (ar.1.mpr h))
      change ¬ (_ = (t₀.regs.get64 .r8).toNat % 2 ^ 32) at hne
      obtain ⟨hC1, hC2, hC3⟩ := hC
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Int64.toBitVec_ofNat_norm,
        hrsp, hrbp, h14, h15, ar.2.1, ar.2.2.1, ar.2.2.2]
      exact ⟨⟨⟨hC1, hC2, hC3⟩, ⟨trivial, trivial, by omega, trivial, trivial, trivial, trivial⟩, hm⟩,
        by omega⟩

/-- (block-specific: `.Lbf6f`) `autocorrelate`'s footprint (row `b` of
`X_low`, `phi`, `ps_mask3`) inside the arrays. -/
theorem BW_carve (t₀ : MachineData) (b : BitVec 64)
    (hb : (b - arg3 t₀).toNat + 320 ≤ 320 * hfInvN t₀) :
    ∃ H, BW t₀ = Blocks [(b, 320), (t₀.regs.get64 .rsp - 0x78#64, 48), (lab "ps_mask3", 16)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex hb (by unfold hfInvN; omega)
  refine ⟨H1 ⋆ Blocks [(arg1 t₀, 8 * hfInvN t₀), (arg2 t₀, 8 * hfInvN t₀),
    (lab "LCPI19_0", 4), (lab "LCPI19_1", 4), (lab "LCPI19_2", 16)], ?_⟩
  simp only [BW, Blocks]
  rw [e1]
  ac_rfl

/-- (block-specific: `.Lbf6f`) `dsp` read back from its slot. -/
theorem T_loadD {fa : Int64} {R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ T fa R ra t₀ (FrL t₀)) :
    m.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀).toInt)) :=
  Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right
    (Mem.Split.here _ _) _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

/-- (block-specific: `.Lbf6f`) The `autocorrelate` slot read through `dsp`. -/
theorem T_loadF {fa : Int64} {R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ T fa R ra t₀ (FrL t₀)) :
    m.loadInt (arg0 t₀ + 0x38#64) 8 = some (Int.ofBytes (Int.toBytes 8 fa.toBitVec.toInt)) :=
  Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right
    (Mem.Split.here _ _) _) _) _)
    (Int.toBytes_length _ _) (by decide)

omit [CodeEnv] in
/-- (block-specific: `.Lbf6f`) The `dsp` slot, from `rbp = rsp₀ - 0x78 + 0x70`. -/
theorem lbf6f_addr (r : BitVec 64) :
    ∀ regs : Reg64s, r - 0x78#64 + 0x70#64 + AddrIndex.offset64 none regs + Int64.toBitVec (-56)
      = r - 0x40#64 := by
  intro regs
  rw [AddrIndex.offset64_none, show Int64.toBitVec (-56) = 0xffffffffffffffc8#64 from rfl]
  bv_omega

/-- (block-specific: `.Lbf6f`) The memory the callee gives back, as the loop's. -/
theorem T_ret {fa : Int64} {R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (Reserve 0x28 (t₀.regs.get64 .rsp - 0x80#64)
      ⋆ (BW t₀ ⋆ (FnCell (arg0 t₀ + 0x38#64) fa ⋆ FrL t₀ (Rest R ra t₀))))) :
    m =⋆ T fa R ra t₀ (FrL t₀) := by
  unfold T
  exact Mem.ac h

omit [CodeEnv] in
/-- An address with no index register. -/
theorem hf_add0 (a b : BitVec 64) : a + 0 + b = a + b := by simp

omit [CodeEnv] in
/-- (block-specific: `.Lbf6f`) The callee's return-address slot. -/
theorem lbf6f_push (r : BitVec 64) : r - 0x78#64 - 8#64 = r - 0x80#64 := by bv_omega

omit [CodeEnv] in
/-- (block-specific: `.Lbf6f`) `rsp` after the callee returns. -/
theorem lbf6f_ret (r : BitVec 64) : r - 0x80#64 + 8 = r - 0x78#64 := by bv_omega

omit [CodeEnv] in
/-- (block-specific: `.Lbf6f`) The stack alignment `autocorrelate` asks for, from
`rsp₀ + 8` 16-aligned: `phi` and the callee's `rsp + 8`. -/
theorem lbf6f_align (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) :
    isAligned 16 (r - 0x78#64) = true ∧ isAligned 16 (r - 0x78#64 - 8#64 + 8#64) = true := by
  have h1 : isAligned 16 (r - 0x78#64) = true :=
    isAligned_of_sub (by decide) h (by
      rw [show r - 0x78#64 - (r + 8#64) = 0xffffffffffffff80#64 by bv_omega]; rfl)
  exact ⟨h1, by rw [show r - 0x78#64 - 8#64 + 8#64 = r - 0x78#64 by bv_omega]; exact h1⟩

/-- (block-specific: `.Lbf6f`) The loop's memory with the callee's slot and
reservation at the head, for `push_slot_res`. -/
theorem T_call {fa : Int64} {R : Mem 64 → Prop} {ra : Int64} {t₀ : MachineData} {m : Mem 64}
    (h : m =⋆ T fa R ra t₀ (FrL t₀)) :
    m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (Reserve 0x28 (t₀.regs.get64 .rsp - 0x80#64)
      ⋆ (BW t₀ ⋆ (FnCell (arg0 t₀ + 0x38#64) fa ⋆ FrL t₀ (Rest R ra t₀)))) := by
  unfold T at h
  exact Mem.ac h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000 in
theorem blk_Lbf6f (fa : Int64) (hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lbf6f" := by
  cfg_block
  measure_hb "Lbf6f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    have hm' := T_call hm
    have hal := lbf6f_align (t₀.regs.get64 .rsp) hC.2.2
    have hD := T_loadD hm
    have hF := T_loadF hm
    have ea := (lbf6f_addr (t₀.regs.get64 .rsp))
    rw [← hrbp] at ea
    vcgen [MachineWP.call_mem_proc_spec_at
      (BW t₀, FnCell (arg0 t₀ + 0x38#64) fa ⋆ FrL t₀ (Rest R ra t₀)) fa
      (Kraken.Executable.ProcSpec.widen (k := 0x28) hA (Nat.le_refl _) (by decide))]
    clear hA
    all_goals try subst_vars
    case vc1 => simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ea, hD, Option.isSome_some]
    rename_i x hld
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ea, hD, Option.some.injEq] at hld
    subst hld
    hf_norm
    refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    · simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hf_add0, hF,
        Option.map_some, Int64.ofBitVec_toBitVec]
    · refine Mem.push_slot_res hm' ?_ _
      have eb : Width.W64.bytesv = 8#64 := rfl
      simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        hrsp, eb]
      exact lbf6f_push _
    · try simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, hrsp]
      exact ⟨hal.1, hC.2.1, hal.2⟩
    · try simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      exact BW_carve t₀ _ (by
        show (_ - t₀.regs.get64 .rcx).toNat + 320 ≤ 320 * ((t₀.regs.get64 .r8).toNat % 2 ^ 32)
        have := hC.1; omega)
    · obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm2⟩ := hpost
      have eb : Width.W64.bytesv = 8#64 := rfl
      simp only [MachineData.get64_pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        hrsp, eb, lbf6f_push] at hrsp' hrbp' hbx' h12' h13' h14' h15' hm2
      have hm3 := T_ret hm2
      try simp only [hrbp, h14, h15] at hrbp' h14' h15'
      vcgen
      refine ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm3⟩, ?_⟩
      · rw [hrsp']; exact lbf6f_ret _
      · exact hrbp'
      · rw [h13']; exact hi
      · rw [h12', h13']; exact h12
      · rw [hbx', h13']; exact hbx
      · exact h14'
      · exact h15'
      · rw [h13']; exact Nat.le_refl _
    · rw [lbf6f_push]; grind_cells'

omit [CodeEnv] in
/-- (block-specific: `.e1`) The bound's slot, from `rbp = rsp₀ - 8`. -/
theorem e1_addr (r : BitVec 64) : r - 8#64 + 18446744073709551568#64 = r - 0x38#64 := by
  bv_omega

omit [CodeEnv] in
/-- (block-specific: `.e1`) `mov %r8d,%eax; shl $3,%rax` is `8 k0`. -/
theorem e1_shl (x : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x) <<< 3 = K (8 * (x.toNat % 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  simp -implicitDefEqProofs only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
/-- `xor %r32d,%r32d`. -/
theorem e1_xor (a : BitVec 32) : BitVec.setWidth 64 (a ^^^ a) = 0#64 := by simp

omit [CodeEnv] in
theorem e1_rbp (r : BitVec 64) : r - 8#64 = r - 0x78#64 + 0x70#64 := by bv_omega

omit [CodeEnv] in
/-- Stack-address chains (`push`es) folded to one offset. -/
theorem hf_sub_sub (a b c : BitVec 64) : a - b - c = a - (b + c) := by bv_omega

omit [CodeEnv] in
theorem hf_sub_add (a b c : BitVec 64) : a - b + c = a - (b - c) := by bv_omega

omit [CodeEnv] in
/-- (block-specific: entry) `test %r8d,%r8d; jle` not taken: `k0 ≥ 1`. -/
theorem entry_le (x : BitVec 64)
    (h : (((BitVec.setWidth 32 x).msb != false) || (BitVec.setWidth 32 x == BitVec.zero 32))
      = false) : 1 ≤ x.toNat % 2 ^ 32 := by
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  have h2 := h.2
  have : (BitVec.setWidth 32 x).toNat ≠ 0 := fun e =>
    h2 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
  simp -implicitDefEqProofs only [BitVec.toNat_setWidth] at this
  omega

/-- (block-specific: entry) The part of the memory the prologue does not touch. -/
abbrev EntryH (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  BW t₀ ⋆ (8 ?@ (r - 0x80#64) ⋆ (Reserve 0x28 (r - 0x80#64) ⋆ (FnCell (arg0 t₀ + 0x38#64) fa
    ⋆ (8 ?@ (r - 0x38#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ Rest R ra t₀)))))

/-- (block-specific: entry) The cells the prologue writes in front of one `Hid` atom. -/
theorem entry_pre (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    T fa R ra t₀ (Fr0 t₀) =
      8 ?@ (t₀.regs.get64 .rsp - 0x8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x10#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x18#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x20#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x28#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ Mem.Hid (EntryH fa R ra t₀))))))) := by
  simp only [T, Fr0, BlankS, EntryH, Mem.Hid]
  ac_rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 310000 in
theorem blk_entry (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    clear _hA
    rw [entry_pre] at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Int64.toBitVec_neg_ofNat_norm, Nat.reduceSub, hf_sub_sub, hf_sub_add,
      BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceSetWidth] at *
    all_goals try simp only [CondCode.interp_le, StatusFlags.sf_from_result, StatusFlags.zf_from_result,
      StatusFlags.of_from_result, BitVec.and_self] at *
    all_goals try (rename_i hz; have hn1 := entry_le _ hz)
    case vc1 | vc2 | vc3 | vc4 | vc5 | vc6 | vc7 => grind_cells'
    all_goals simp only [Mem.Hid, SavedW_open] at hm ⊢
    all_goals grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 70000 in
theorem blk_e1 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.e1" := by
  cfg_block
  measure_hb "e1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hn1, hrsp, hrbp, hsi, hdx, hcx, h8, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    all_goals try subst_vars
    all_goals simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.succ_ne_zero, hrsp, hrbp, hcx, hdx, hsi, h8, Int64.toBitVec_neg_ofNat_norm, Nat.reduceSub]
    all_goals simp only [e1_addr, e1_shl, e1_xor]
    all_goals try simp only [e1_rbp]
    all_goals grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 110000 in
theorem blk_c1 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.c1" := by
  cfg_block
  measure_hb "c1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 110000 in
theorem blk_Lbfb5 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lbfb5" := by
  cfg_block
  measure_hb "Lbfb5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000 in
theorem blk_Lc000 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lc000" := by
  cfg_block
  measure_hb "Lc000"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 110000 in
theorem blk_Lc010 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lc010" := by
  cfg_block
  measure_hb "Lc010"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000 in
theorem blk_Lc02f (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lc02f" := by
  cfg_block
  measure_hb "Lc02f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 130000 in
theorem blk_c2 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.c2" := by
  cfg_block
  measure_hb "c2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 140000 in
theorem blk_Lc0b0 (fa : Int64) (_hA : HfInvCallees fa) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : BlockOb fa R ra t₀ "sbr_hf_inverse_filter.Lc0b0" := by
  cfg_block
  measure_hb "Lc0b0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, hi, h12, hbx, h14, h15⟩, hm⟩, hn⟩ := hs₀
    clear _hA
    vcgen
    hf_close

/-! ### The frame, and the procedure's obligation -/

omit [CodeEnv] in
/-- The own `0x78` bytes as the cells the code uses: `phi` (48 bytes), the
unused slot, the two spill slots, the six saved registers. -/
theorem frame_cells (r : BitVec 64) :
    (0x78 ?@ (r - 0x78#64) : Mem 64 → Prop) =
      48 ?@ (r - 0x78#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (8 ?@ (r - 0x40#64) ⋆ (8 ?@ (r - 0x38#64)
      ⋆ (8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
      ⋆ (8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64))))))))) := by
  rw [Block.split_at (r - 0x78#64) 0x78 48 (by decide) (by decide),
    show r - 0x78#64 + BitVec.ofNat 64 48 = r - 0x48#64 by bv_omega,
    Block.split_at (r - 0x48#64) (0x78 - 48) 8 (by decide) (by decide),
    show r - 0x48#64 + BitVec.ofNat 64 8 = r - 0x40#64 by bv_omega,
    Block.split_at (r - 0x40#64) (0x78 - 48 - 8) 8 (by decide) (by decide),
    show r - 0x40#64 + BitVec.ofNat 64 8 = r - 0x38#64 by bv_omega,
    Block.split_at (r - 0x38#64) (0x78 - 48 - 8 - 8) 8 (by decide) (by decide),
    show r - 0x38#64 + BitVec.ofNat 64 8 = r - 0x30#64 by bv_omega,
    Block.split_at (r - 0x30#64) (0x78 - 48 - 8 - 8 - 8) 8 (by decide) (by decide),
    show r - 0x30#64 + BitVec.ofNat 64 8 = r - 0x28#64 by bv_omega,
    Block.split_at (r - 0x28#64) (0x78 - 48 - 8 - 8 - 8 - 8) 8 (by decide) (by decide),
    show r - 0x28#64 + BitVec.ofNat 64 8 = r - 0x20#64 by bv_omega,
    Block.split_at (r - 0x20#64) (0x78 - 48 - 8 - 8 - 8 - 8 - 8) 8 (by decide) (by decide),
    show r - 0x20#64 + BitVec.ofNat 64 8 = r - 0x18#64 by bv_omega,
    Block.split_at (r - 0x18#64) (0x78 - 48 - 8 - 8 - 8 - 8 - 8 - 8) 8 (by decide) (by decide),
    show r - 0x18#64 + BitVec.ofNat 64 8 = r - 0x10#64 by bv_omega,
    Block.split_at (r - 0x10#64) (0x78 - 48 - 8 - 8 - 8 - 8 - 8 - 8 - 8) 8 (by decide) (by decide),
    show r - 0x10#64 + BitVec.ofNat 64 8 = r - 0x8#64 by bv_omega]

/-- The memory at the `ret`, its frame contents forgotten: the slots blank,
the return address too. -/
theorem T_post (fa : Int64) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Mem.Entails (T fa R ra t₀ (Fr1 t₀))
      (BW t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x80#64) ⋆ (Reserve 0x28 (t₀.regs.get64 .rsp - 0x80#64)
        ⋆ (FnCell (arg0 t₀ + 0x38#64) fa ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64)
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x48#64)
        ⋆ BlankS (t₀.regs.get64 .rsp) (8 ?@ (t₀.regs.get64 .rsp) ⋆ R)))))))) := by
  unfold T Fr1 Rest
  rw [SavedW_open]
  exact Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.forget8 _ _ (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
      (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
      (Mem.Entails.forget8 _ _ (Mem.Entails.refl _))))))))))))))

set_option maxRecDepth 100000 in
theorem spec (hpl : Program.PlacedIn body) (fa : Int64) (hA : HfInvCallees fa) :
    HfInverseFilterSpec fa := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table fa)
    (Post' fa) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀ _ l blk hblk
    have hmem := Program.isSome_blockAt body l
    cfg_view hblk as hview
    rw [hblk, hview] at hmem
    replace hmem := hmem.symm
    clear hview
    simp only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hmem
    · exact blk_entry fa hA R ra t₀ blk hblk
    · exact blk_e1 fa hA R ra t₀ blk hblk
    · exact blk_Lbf40 fa hA R ra t₀ blk hblk
    · exact blk_Lbf57 fa hA R ra t₀ blk hblk
    · exact blk_Lbf6f fa hA R ra t₀ blk hblk
    · exact blk_c1 fa hA R ra t₀ blk hblk
    · exact blk_Lbfb5 fa hA R ra t₀ blk hblk
    · exact blk_Lc000 fa hA R ra t₀ blk hblk
    · exact blk_Lc010 fa hA R ra t₀ blk hblk
    · exact blk_Lc02f fa hA R ra t₀ blk hblk
    · exact blk_c2 fa hA R ra t₀ blk hblk
    · exact blk_Lc0b0 fa hA R ra t₀ blk hblk
    · exact blk_Lc0dd fa hA R ra t₀ blk hblk
    · exact blk_done fa hA R ra t₀ blk hblk
  · -- hpre
    rintro R ra t ⟨hm, hC⟩
    refine ⟨rfl, hC, ?_⟩
    have hw := CallPre.le hm
    simp only [CallPre, hfInvNeed] at hm
    rw [show (0xa8 : Nat) = 0x80 + 0x28 from rfl,
      Reserve_split_frame 0x80 0x28 (by decide) _ (Nat.le_trans (by decide) hw)] at hm
    simp only [Nat.reduceSub, frame_cells] at hm
    simp only [T, Fr0, BlankS, BW, HfInvF, Blocks, Rest] at hm ⊢
    exact Mem.ac hm
  · -- hpost
    rintro R ra t₀ s ⟨h0, -⟩ ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hm' := T_post fa R ra t₀ _ hm
    rw [show hfInvNeed = 0x80 + 0x28 from rfl,
      Reserve_split_frame 0x80 0x28 (by decide) _ (Nat.le_trans (by decide) (CallPre.le h0))]
    simp only [Nat.reduceSub, frame_cells]
    simp only [BlankS, BW, HfInvF, Blocks] at hm' ⊢
    exact Mem.ac hm'

end Kraken.Examples.Sbr.HfInverseFilter
