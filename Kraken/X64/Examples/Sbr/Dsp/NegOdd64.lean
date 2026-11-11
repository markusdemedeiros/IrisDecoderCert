import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.Dsp.NegOdd64Text

/-!
# `ff_sbr_neg_odd_64_sse` as a `ProcSpec`

`sbr_neg_odd_64(z)` flips the sign of the odd floats of `z[64]`
(`libavcodec/x86/sbrdsp.asm`). `spec` proves `NegOdd64Spec` (`Spec.lean`): a
call with `z` 16-byte aligned, the 256 bytes of `z` and the 16 of `ps_mask2`
owned, returns with the SysV convention restored and only those bytes
changed. `SbrNegOdd64.lean` proved the same loop as a bare triple; this file
restates it as the `ProcSpec` the parametric proof of `ff_aac_sbr_apply`
assumes of the `neg_odd_64` slot.

## Notes

* The contract matches `tests/checkasm/sbrdsp.c` (`z[64]`, aligned): the
  four aligned loads/stores per iteration need `z` 16-aligned, the `xorps`
  memory operands need `ps_mask2` 16-aligned. Dropping the first alignment
  makes the loop block fail (negative check, scratch), as in
  `SbrNegOdd64.lean`.
* No stack, no callee-saved register touched: the reservation is 0.
* Proof shape, reusable for every leaf: the `ret` gets a block of its own
  (label `….done`, variant 0), so that the loop block is pure SSE/integer
  work closed by `vcgen with finish`, and the `ret` block is
  `vcgen; simp only [Rest]; call_simp; grind_cells`. The caller's memory
  `Rest` (return-address cell, reservation, `R`) is a `def`, so `grind`
  moves it as one opaque cell inside the loop; unfolded, or with `ret` in
  the loop block, `grind` times out at `whnf` even at 2M heartbeats.
* A variant that rises on a fall-through edge (`2^64` at `.done`) makes the
  loop block unprovable; `grind` then searches until the heartbeat limit
  rather than failing fast. Check the variant first when a block times out.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.NegOdd64

variable [CodeEnv]

/-- The caller's side of memory behind the footprint: the return address,
the empty reservation and `R`. A `def`, so that `grind` moves it whole. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- The assertion at each label: at the entry, the entry state; at the loop,
the invariant (`rdi` a multiple of 64 bytes into `z`, `rsi` its end); at
`.done`, the convention's registers and the footprint in place. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_neg_odd_64_sse", s => s = t₀ ∧ NegOdd64C t₀
      ∧ (t₀.dmem =⋆ NegOdd64F t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_neg_odd_64_sse.loop", s =>
      let z := arg0 t₀
      let j := (s.regs.get64 .rdi - z).toNat
      NegOdd64C t₀ ∧ s.regs.get64 .rsi = z + 256#64 ∧ j < 256 ∧ j % 64 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ NegOdd64F t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_neg_odd_64_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ NegOdd64F t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: bytes left at the loop; 0 at `.done` (fall-through edge). -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_neg_odd_64_sse.loop", s => (s.regs.get64 .rsi - s.regs.get64 .rdi).toNat
  | "ff_sbr_neg_odd_64_sse.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves: `CallPost` with the footprint in front. -/
abbrev Post' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ NegOdd64F t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : NegOdd64Spec := by
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
    show (_ ⋆ (_ ⋆ (NegOdd64F t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.NegOdd64
