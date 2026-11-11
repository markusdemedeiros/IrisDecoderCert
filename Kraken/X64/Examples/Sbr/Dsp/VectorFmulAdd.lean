import Kraken.X64.Examples.Sbr.Dsp.FloatDspCommon
import Kraken.X64.Examples.Sbr.Dsp.VectorFmulAddText

/-!
# `ff_vector_fmul_add_{sse,avx,fma3}` as `ProcSpec`s

`vector_fmul_add(dst, src0, src1, src2, len)` (`libavutil/x86/float_dsp.asm`)
sets `dst[i] = src0[i] * src1[i] + src2[i]` for `i < len`, from the end down:
`r8 = 4 len - c` (`lea -c(,%r8d,4),%r8`, `c` the bytes per iteration: 32 for SSE,
64 for AVX and FMA3), then `sub $c,%r8; jge`. `VectorFmulAddC` has `src2 = dst`
(the form `sbr_qmf_synthesis` calls), so the reads of `src2` fall in the `dst`
block.

The texts are those of the object (`float_dsp.o`), the alignment padding after the
`lea` written as a sized `nop`, the final `rep ret` of the SSE variant written
`ret`. Every loop body has its loads before its stores, so it is one block.
The FMA3 variant computes `dst := src0 * src1 + src2` with `vfmadd132ps`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open Kraken.Examples.Sbr.FloatDsp
open scoped Kraken.LeafLemmas.Offset
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.VectorFmulAdd

variable [CodeEnv]

/-- The loop invariant: `r8` the byte offset of the current `c`-byte chunk, the
pointers unchanged. -/
abbrev Inv (c need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let j := (s.regs.get64 .r8).toNat
  VectorFmulAddC t₀ ∧ j % c = 0 ∧ j + c ≤ 4 * fmulAddN t₀
  ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
  ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rcx = arg3 t₀
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ VectorFmulAddF t₀ ⋆ Rest need R ra t₀)

abbrev Done (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ VectorFmulAddF t₀ ⋆ Rest need R ra t₀)

abbrev Entry (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s = t₀ ∧ VectorFmulAddC t₀ ∧ (t₀.dmem =⋆ VectorFmulAddF t₀ ⋆ Rest need R ra t₀)

abbrev tableSse (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_add_sse", s => Entry need R ra t₀ s
  | "ff_vector_fmul_add_sse.loop", s => Inv 32 need R ra t₀ s
  | "ff_vector_fmul_add_sse.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varSse : Label → MachineData → Nat
  | "ff_vector_fmul_add_sse.loop", s => (s.regs.get64 .r8).toNat + 1
  | "ff_vector_fmul_add_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev tableAvx (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_add_avx", s => Entry need R ra t₀ s
  | "ff_vector_fmul_add_avx.loop", s => Inv 64 need R ra t₀ s
  | "ff_vector_fmul_add_avx.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varAvx : Label → MachineData → Nat
  | "ff_vector_fmul_add_avx.loop", s => (s.regs.get64 .r8).toNat + 1
  | "ff_vector_fmul_add_avx.done", _ => 0
  | _, _ => 2 ^ 64

abbrev tableFma3 (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_vector_fmul_add_fma3", s => Entry need R ra t₀ s
  | "ff_vector_fmul_add_fma3.loop", s => Inv 64 need R ra t₀ s
  | "ff_vector_fmul_add_fma3.done", s => Done need R ra t₀ s
  | _, _ => False

abbrev varFma3 : Label → MachineData → Nat
  | "ff_vector_fmul_add_fma3.loop", s => (s.regs.get64 .r8).toNat + 1
  | "ff_vector_fmul_add_fma3.done", _ => 0
  | _, _ => 2 ^ 64

/-- The entry block (`k` the `lea` displacement, `c` its negation). -/
macro "fmuladd_entry" k:term:max c:term:max : tactic =>
  `(tactic| (
    vcgen
    rename_i n s h
    obtain ⟨⟨hst, hc, hm⟩, hv⟩ := h
    subst hst
    simp only [Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true] at *
    rw [lea_len_toNat _ (BitVec.setWidth 32 ($k : Int64).toBitVec) $c (by rfl) (by decide)
      (by decide) hc.2.1 hc.2.2.1 hc.2.2.2.1]
    simp at hv
    subst hv
    refine ⟨⟨hc, ?_, ?_, by simp only [true_and]; exact hm⟩, ?_⟩ <;> omega))

macro "fmuladd_exit" : tactic =>
  `(tactic| (
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells))

macro "fmuladd_pre" : tactic =>
  `(tactic| (
    rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h))

macro "fmuladd_post" : tactic =>
  `(tactic| (
    rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (VectorFmulAddF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (8 ?@ _)]
    exact hm))

theorem specSse (hpl : Program.PlacedIn bodySse) (need : Nat) :
    VectorFmulAddSpec need (entry "ff_vector_fmul_add_sse") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodySse) (tableSse need)
    (Post' VectorFmulAddF need) varSse (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodySse]
    · fmuladd_entry (-32) 32
    · fdsp_block
    · fmuladd_exit
  · fmuladd_pre
  · fmuladd_post

theorem specAvx (hpl : Program.PlacedIn bodyAvx) (need : Nat) :
    VectorFmulAddSpec need (entry "ff_vector_fmul_add_avx") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodyAvx) (tableAvx need)
    (Post' VectorFmulAddF need) varAvx (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodyAvx]
    · fmuladd_entry (-64) 64
    · fdsp_block
    · fmuladd_exit
  · fmuladd_pre
  · fmuladd_post

theorem specFma3 (hpl : Program.PlacedIn bodyFma3) (need : Nat) :
    VectorFmulAddSpec need (entry "ff_vector_fmul_add_fma3") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := bodyFma3) (tableFma3 need)
    (Post' VectorFmulAddF need) varFma3 (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [bodyFma3]
    · fmuladd_entry (-64) 64
    · fdsp_block
    · fmuladd_exit
  · fmuladd_pre
  · fmuladd_post

end Kraken.Examples.Sbr.VectorFmulAdd
