import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.PackedSse
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintBflyText

/-!
# `ff_sbr_qmf_deint_bfly_sse2` as a `ProcSpec`

`sbr_qmf_deint_bfly(v, src0, src1)` (`libavcodec/x86/sbrdsp.asm`, C reference
`sbr_qmf_deint_bfly_c` in `libavcodec/sbrdsp_template.c`) writes `v[128]`
from the butterflies of `src0[64]` and the reversed `src1[64]`. The loop keeps
a down-counting offset `c` (`r8`, 224 down to 0 by 32, 8 iterations) into
`src0` and the low half of `v`, and two up-counting pointers: `src1` (`rdx`)
and `vrev = v + 256` (`rcx`). `spec` proves `QmfDeintBflySpec`: a call with
the three arrays 16-byte aligned and owned (512 bytes of `v`, 256 of each
source) returns with the SysV convention restored and only those bytes changed.

## Notes

* The contract is the one of `tests/checkasm/sbrdsp.c` (`src0[64]`,
  `src1[64]`, `v[128]`, all `LOCAL_ALIGNED_16`): the `movdqa` loads and
  stores need the three pointers 16-aligned, nothing more. The only call
  site (`sbr_qmf_synthesis` in `libavcodec/aacsbr_template.c`) passes
  `v` inside `synthesis_filterbank_samples` and `mdct_buf[1]`, `mdct_buf[0]`
  (all `DECLARE_ALIGNED(32, …)`), which are pairwise disjoint as the
  footprint's `Blocks` requires.
* The footprint asks the three arrays to be disjoint (one `Blocks` list).
  The prototype has no `restrict`; an in-place call is not covered, but no
  caller makes one.
* No integer argument; no stack; `r8`, `rcx`, `rdx` and `xmm0-7` are
  caller-saved: the reservation is 0.
* `mov $0xe0,%r8d` zero-extends, and the loop's `jge` reads the signed
  result of `sub $0x20,%r8`: from 0 it goes to `-32` and leaves.
* The moving pointers `rdx`, `rcx` are tracked by their offsets
  `(rdx - src1).toNat = j`, `(rcx - v).toNat = 256 + j`, with `r8 = 224 - j`;
  stating them through `c = r8` instead (`(rdx - src1).toNat = 224 - c`) left
  the `(%rdx)` loads unproved. Their operands reach `Blocks.Inside` as
  `p + 0 + c`, which needs `Mem.Blocks.Inside.ptr_add_add`
  (`Kraken/Rules/LeafLemmas.lean`).
* Dropping the alignment of `src1` from `QmfDeintBflyC` makes the loop block
  fail (negative check, scratch).
* Scopes opened: `Kraken.LeafLemmas.PtrAdd`, `Kraken.Rules.GenericMem.Norm`
  (the displacement-literal and register read-after-write `grind norm`
  lemmas; without them the loop block fails after five minutes).
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.LeafLemmas.PtrAdd Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.QmfDeintBfly

variable [CodeEnv]

/-- The caller's side of memory behind the footprint. A `def`, so that
`grind` moves it whole. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- At the loop: `rdx` is `j` bytes into `src1` (`j` a multiple of 32 below
256), `rcx` is `256 + j` bytes into `v`, and `c = r8` is `224 - j`. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_qmf_deint_bfly_sse2", s => s = t₀ ∧ QmfDeintBflyC t₀
      ∧ (t₀.dmem =⋆ QmfDeintBflyF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_deint_bfly_sse2.loop", s =>
      let j := (s.regs.get64 .rdx - arg2 t₀).toNat
      QmfDeintBflyC t₀ ∧ j < 256 ∧ j % 32 = 0
      ∧ (s.regs.get64 .r8).toNat = 224 - j
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ (s.regs.get64 .rcx - arg0 t₀).toNat = 256 + j
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfDeintBflyF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_deint_bfly_sse2.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfDeintBflyF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: `c + 32` at the loop; 0 at `.done`. -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_qmf_deint_bfly_sse2.loop", s => (s.regs.get64 .r8).toNat + 32
  | "ff_sbr_qmf_deint_bfly_sse2.done", _ => 0
  | _, _ => 2 ^ 64

abbrev Post' (R : Mem 64 → Prop) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ QmfDeintBflyF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : QmfDeintBflySpec := by
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
    show (_ ⋆ (_ ⋆ (QmfDeintBflyF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.QmfDeintBfly
