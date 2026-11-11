import Kraken.X64.Examples.Sbr.Dsp.FloatDspCommon
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulRevText

/-!
# `ff_vector_fmul_reverse_{sse,avx,avx2}` as `ProcSpec`s

`vector_fmul_reverse(dst, src0, src1, len)` (`libavutil/x86/float_dsp.asm`) sets
`dst[i] = src0[i] * src1[len - 1 - i]` for `i < len`: `rcx = 4 len - c`
(`lea -c(,%ecx,4),%rcx`, `c` the bytes per iteration: 32 for SSE, 64 for AVX and
AVX2) walks `dst` and `src0` from the end down while `rdx` walks `src1` up
(`add $c,%rdx`); the loads of `src1` are reversed in the registers.

The invariant ties the two: `(rdx - src1) + rcx + c = 4 len`.

The texts are those of the object (`float_dsp.o`), the alignment padding after the
`lea` written as a sized `nop`, the final `rep ret` of the SSE variant written
`ret`. Every loop body has its loads before its stores, so it is one block.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open Kraken.Examples.Sbr.FloatDsp
open scoped Kraken.LeafLemmas.Offset Kraken.LeafLemmas.PtrAdd
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.VectorFmulRev

variable [CodeEnv]

/-- The loop invariant: `rcx` the byte offset of the current `c`-byte chunk of
`dst`/`src0`, `rdx` the matching chunk of `src1` from the front. -/
abbrev Inv (c need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let j := (s.regs.get64 .rcx).toNat
  VectorFmulRevC t₀ ∧ j % c = 0 ∧ j + c ≤ 4 * fmulRevN t₀
  ∧ (s.regs.get64 .rdx - arg2 t₀).toNat + j + c = 4 * fmulRevN t₀
  ∧ isAligned 32 (s.regs.get64 .rdx) = true
  ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ VectorFmulRevF t₀ ⋆ Rest need R ra t₀)

abbrev Done (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ VectorFmulRevF t₀ ⋆ Rest need R ra t₀)

abbrev Entry (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s = t₀ ∧ VectorFmulRevC t₀ ∧ (t₀.dmem =⋆ VectorFmulRevF t₀ ⋆ Rest need R ra t₀)

abbrev tableSse (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_reverse_sse", s => Entry need R ra t₀ s
  | "ff_vector_fmul_reverse_sse.loop", s => Inv 32 need R ra t₀ s
  | "ff_vector_fmul_reverse_sse.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varSse : Label → MachineData → Nat
  | "ff_vector_fmul_reverse_sse.loop", s => (s.regs.get64 .rcx).toNat + 1
  | "ff_vector_fmul_reverse_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev tableAvx (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_reverse_avx", s => Entry need R ra t₀ s
  | "ff_vector_fmul_reverse_avx.loop", s => Inv 64 need R ra t₀ s
  | "ff_vector_fmul_reverse_avx.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varAvx : Label → MachineData → Nat
  | "ff_vector_fmul_reverse_avx.loop", s => (s.regs.get64 .rcx).toNat + 1
  | "ff_vector_fmul_reverse_avx.done", _ => 0
  | _, _ => 2 ^ 64

/-- Behind the mask load of the AVX2 routine: the entry state up to the vector
registers. -/
abbrev Entry2 (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs = t₀.regs ∧ s.dmem = t₀.dmem ∧ VectorFmulRevC t₀
    ∧ (t₀.dmem =⋆ VectorFmulRevF t₀ ⋆ Rest need R ra t₀)

abbrev tableAvx2 (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_reverse_avx2", s => Entry need R ra t₀ s
  | "ff_vector_fmul_reverse_avx2.lea", s => Entry2 need R ra t₀ s
  | "ff_vector_fmul_reverse_avx2.loop", s => Inv 64 need R ra t₀ s
  | "ff_vector_fmul_reverse_avx2.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varAvx2 : Label → MachineData → Nat
  | "ff_vector_fmul_reverse_avx2.lea", _ => 2 ^ 64 - 1
  | "ff_vector_fmul_reverse_avx2.loop", s => (s.regs.get64 .rcx).toNat + 1
  | "ff_vector_fmul_reverse_avx2.done", _ => 0
  | _, _ => 2 ^ 64

/-- The entry block (`k` the `lea` displacement, `c` its negation). -/
macro "fmulrev_entry" k:term:max c:term:max : tactic =>
  `(tactic| (
    vcgen
    rename_i n s h
    obtain ⟨⟨hst, hc, hm⟩, hv⟩ := h
    subst hst
    simp only [Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at *
    rw [lea_len_toNat _ (BitVec.setWidth 32 ($k : Int64).toBitVec) $c (by rfl) (by decide)
      (by decide) hc.1 hc.2.1 hc.2.2.1]
    simp at hv
    subst hv
    refine ⟨⟨hc, ?_, ?_, ?_, hc.2.2.2.2.2.1, by simp only [true_and]; exact hm⟩, ?_⟩
    all_goals first
      | omega
      | (simp only [BitVec.sub_self, BitVec.toNat_zero]; omega)))

/-- The `lea` block of the AVX2 routine (from `Entry2`). -/
macro "fmulrev_lea" k:term:max c:term:max : tactic =>
  `(tactic| (
    vcgen
    rename_i n s h
    obtain ⟨⟨hr, hd, hc, hm⟩, hv⟩ := h
    simp only [Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hr, hd] at *
    rw [lea_len_toNat _ (BitVec.setWidth 32 ($k : Int64).toBitVec) $c (by rfl) (by decide)
      (by decide) hc.1 hc.2.1 hc.2.2.1]
    simp at hv
    subst hv
    refine ⟨⟨hc, ?_, ?_, ?_, hc.2.2.2.2.2.1, by simp only [true_and]; exact hm⟩, ?_⟩
    all_goals first
      | omega
      | (simp only [BitVec.sub_self, BitVec.toNat_zero]; omega)))

macro "fmulrev_exit" : tactic =>
  `(tactic| (
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells))

macro "fmulrev_pre" : tactic =>
  `(tactic| (
    rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h))

macro "fmulrev_post" : tactic =>
  `(tactic| (
    rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (VectorFmulRevF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (8 ?@ _)]
    exact hm))

theorem specSse (hpl : Program.PlacedIn bodySse) (need : Nat) :
    VectorFmulRevSpec need (entry "ff_vector_fmul_reverse_sse") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodySse) (tableSse need)
    (Post' VectorFmulRevF need) varSse (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodySse]
    · fmulrev_entry (-32) 32
    · fdsp_block
    · fmulrev_exit
  · fmulrev_pre
  · fmulrev_post

theorem specAvx (hpl : Program.PlacedIn bodyAvx) (need : Nat) :
    VectorFmulRevSpec need (entry "ff_vector_fmul_reverse_avx") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodyAvx) (tableAvx need)
    (Post' VectorFmulRevF need) varAvx (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodyAvx]
    · fmulrev_entry (-64) 64
    · fdsp_block
    · fmulrev_exit
  · fmulrev_pre
  · fmulrev_post

theorem specAvx2 (hpl : Program.PlacedIn bodyAvx2) (need : Nat) :
    VectorFmulRevSpec need (entry "ff_vector_fmul_reverse_avx2") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodyAvx2) (tableAvx2 need)
    (Post' VectorFmulRevF need) varAvx2 (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodyAvx2]
    · vcgen
      all_goals dsimp only at *
      all_goals grind
    · fmulrev_lea (-64) 64
    · fdsp_block
    · fmulrev_exit
  · fmulrev_pre
  · fmulrev_post

end Kraken.Examples.Sbr.VectorFmulRev
