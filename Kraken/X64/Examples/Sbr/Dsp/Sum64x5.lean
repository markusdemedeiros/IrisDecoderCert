import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.PackedSse
import Kraken.X64.Examples.Sbr.Dsp.Sum64x5Text

/-!
# `ff_sbr_sum64x5_sse` as a `ProcSpec`

`sbr_sum64x5(z)` adds `z[64k .. 64k+63]` for `k = 1..4` into `z[0..63]`
(`libavcodec/x86/sbrdsp.asm`). `spec` proves `Sum64x5Spec`: a call with `z`
16-byte aligned and the 1280 bytes of `z[320]` owned returns with the SysV
convention restored and only those bytes changed.

## Notes

* The contract matches `tests/checkasm/sbrdsp.c` (`z[64 + 256]`,
  `LOCAL_ALIGNED_16`) and the one call site, `sbr_qmf_analysis` in
  `libavcodec/aacsbr_template.c` (`z[320]` = `qmf_filter_scratch[5][64]`,
  `DECLARE_ALIGNED(32)` in `libavcodec/sbr.h`). The aligned `movaps`
  loads/stores and the `addps` memory operands need `z` 16-aligned; nothing
  beyond checkasm is needed. Dropping the alignment, or shrinking the block to
  1264 bytes, makes the loop block fail (negative checks, scratch).
* The `addps d(%b), %xmm` memory operands use the generic
  `MachineWP.addps_load_mem_spec` (`Kraken/Rules/PackedSse.lean`). (A
  shape-specific `b + d` rule written first for this proof turned out to be
  a duplicate of it and was dropped.) The proof opens
  `Kraken.Rules.GenericMem.Norm` (displacement literals, register
  read-after-write as `grind norm` lemmas): without it the loop block fails
  (12 goals). Under those lemmas the loop's back edge needs the local step
  lemma `add32_toNat` (without it one goal fails), so it stays.
* No stack, no callee-saved register, no constant: the reservation is 0 and
  the footprint is the single block `(z, 1280)`.
* Same proof shape as `NegOdd64.lean` (loop block, `….done` block for `ret`).
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Sum64x5


/-- One loop step: `rdi` advances 32 bytes within the first 256 bytes of `z`. -/
theorem add32_toNat {r z : BitVec 64} (h : (r - z).toNat < 256) :
    (32 + r - z).toNat = (r - z).toNat + 32 := by
  have e : 32 + r - z = (r - z) + 32 := by grind
  rw [e]
  generalize r - z = y at *
  rw [BitVec.toNat_add]
  exact Nat.mod_eq_of_lt (by simp; omega)

grind_pattern add32_toNat => (32 + r - z).toNat, (r - z).toNat

variable [CodeEnv]

/-- The caller's side of memory behind the footprint: the return address,
the empty reservation and `R`. A `def`, so that `grind` moves it whole. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- The assertion at each label: at the loop, `rdi` a multiple of 32 bytes
into the first 256 bytes of `z`, `rsi` the end of those 256 bytes. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_sum64x5_sse", s => s = t₀ ∧ Sum64x5C t₀
      ∧ (t₀.dmem =⋆ Sum64x5F t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum64x5_sse.loop", s =>
      let z := arg0 t₀
      let j := (s.regs.get64 .rdi - z).toNat
      Sum64x5C t₀ ∧ s.regs.get64 .rsi = z + 256#64 ∧ j < 256 ∧ j % 32 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Sum64x5F t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum64x5_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Sum64x5F t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: bytes left at the loop; 0 at `.done` (fall-through edge). -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_sum64x5_sse.loop", s => (s.regs.get64 .rsi - s.regs.get64 .rdi).toNat
  | "ff_sbr_sum64x5_sse.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves: `CallPost` with the footprint in front. -/
abbrev Post' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ Sum64x5F t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : Sum64x5Spec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen with finish
    · vcgen with finish
    · vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (Sum64x5F t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.Sum64x5
