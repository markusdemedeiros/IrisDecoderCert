import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.PackedSse
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.QmfPreShuffleText

/-!
# `ff_sbr_qmf_pre_shuffle_sse2` as a `ProcSpec`

`sbr_qmf_pre_shuffle(z)` (`libavcodec/x86/sbrdsp.asm`, C reference
`sbr_qmf_pre_shuffle_c` in `libavcodec/sbrdsp.c`) reads `z[1..64]` and writes the interleaved
shuffle to `z[64..127]`. `spec` proves `QmfPreShuffleSpec`: a call with `z`
16-byte aligned, the 512 bytes of `z` and the 16 of `ff_ps_neg` owned,
returns with the SysV convention restored and only those bytes changed.

## Notes

* The contract is the one of `tests/checkasm/sbrdsp.c` (`z[128]`,
  `LOCAL_ALIGNED_16`): the four `movdqa` stores per iteration
  (`d(%rdx,%rcx,2)`, `rdx = z + 256`) need `z` 16-aligned, the `movdqa` load of
  `ff_ps_neg` needs the constant 16-aligned (it is `DECLARE_ALIGNED(16, …)` in
  `libavcodec/x86/constants.c`). The four loads per iteration are `movdqu`
  at `z + 4 …` and `z + 132 …`, unaligned by design. Nothing beyond checkasm.
  The only call site (`sbr_qmf_analysis` in `libavcodec/aacsbr_template.c`)
  passes `qmf_filter_scratch`, `DECLARE_ALIGNED(32, …)[5][64]`, 1280 bytes.
* Bytes used: reads `z[1..64]` (bytes 4..260), writes `z[64..127]` (bytes
  256..512, the last iteration's stores and the final `movq` to `z[64..65]`).
  The loop reads `z[61..64]` before the tail overwrites `z[64]`. The footprint
  is the whole 512 bytes (one block), plus the 16 bytes of `ff_ps_neg`.
* No integer argument; no stack; `rcx`, `rsi`, `rdx`, `xmm0-5` are
  caller-saved: the reservation is 0. `mov $0x60,%ecx` zero-extends, and the
  `jge` reads the signed result of `sub $0x20,%rcx`: 96, 64, 32, 0, then
  `-32` leaves (4 iterations).
* `rsi` is tracked by its offset `J = (rsi - z).toNat` (132 … 228) with
  `rcx = 228 - J`; stating `rsi = z + 228 - rcx` instead left the `(%rsi)`
  loads unproved (grind does not get from the subtraction to the offset).
  `rdx` is tracked as `(rdx - z).toNat = 256` rather than `rdx = z + 256`,
  so that the term `rdx - z` that triggers `Blocks.Inside.ptr_add_add` exists.
* The two-store tail after the loop has a label of its own (`….tail`), the
  `ret` another (`….done`); both have variant 0.
* Dropping the alignment of `z` from `QmfPreShuffleC` makes the loop block
  fail (negative check, scratch).
* Rule-file `grind` scopes opened (see `Kraken/Rules/*.lean`):
  `Kraken.Rules.GenericMem.Norm`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.LeafLemmas.PtrAdd
open scoped Kraken.Rules.GenericMem.Norm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.QmfPreShuffle

variable [CodeEnv]

/-- The caller's side of memory behind the footprint. A `def`, so that
`grind` moves it whole. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- The assertion at each label. At the loop `rsi` is `J` bytes into `z`
(`J = 132, 164, 196, 228`), `rcx = 228 - J` (`96, 64, 32, 0`), `rdx` is 256
bytes into `z`, `rdi = z`. The pointers are tracked by their offsets
`p - z`, the form `Blocks.Inside.ptr_add(_add)` match. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_qmf_pre_shuffle_sse2", s => s = t₀ ∧ QmfPreShuffleC t₀
      ∧ (t₀.dmem =⋆ QmfPreShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_pre_shuffle_sse2.loop", s =>
      let z := arg0 t₀
      let J := (s.regs.get64 .rsi - z).toNat
      QmfPreShuffleC t₀ ∧ 132 ≤ J ∧ J ≤ 228 ∧ (J - 132) % 32 = 0
      ∧ (s.regs.get64 .rcx).toNat = 228 - J
      ∧ s.regs.get64 .rdi = z ∧ (s.regs.get64 .rdx - z).toNat = 256
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPreShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_pre_shuffle_sse2.tail", s =>
      let z := arg0 t₀
      QmfPreShuffleC t₀
      ∧ s.regs.get64 .rdi = z ∧ (s.regs.get64 .rdx - z).toNat = 256
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPreShuffleF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_qmf_pre_shuffle_sse2.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ QmfPreShuffleF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: `rcx + 32` at the loop; 0 at the tail and `.done`. -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_qmf_pre_shuffle_sse2.loop", s => (s.regs.get64 .rcx).toNat + 32
  | "ff_sbr_qmf_pre_shuffle_sse2.tail", _ => 0
  | "ff_sbr_qmf_pre_shuffle_sse2.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves. -/
abbrev Post' (R : Mem 64 → Prop) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ QmfPreShuffleF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : QmfPreShuffleSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen with finish
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
    show (_ ⋆ (_ ⋆ (QmfPreShuffleF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.QmfPreShuffle
