import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.GenericMem
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.AutocorrelateText

/-!
# `ff_sbr_autocorrelate_sse` / `_sse3` as `ProcSpec`s

`sbr_autocorrelate(x, phi)` (`libavcodec/x86/sbrdsp.asm`, `cglobal
sbr_autocorrelate, 2,3,8,32`) computes the autocorrelation coefficients of
`x[40][2]` into `phi[3][2][2]` for the SBR inverse filter
(`libavcodec/aacsbr.c`, `sbr_hf_inverse_filter`). The SSE and SSE3 entries
have the same control flow (a prologue, a loop unrolled three times over a
counter `rdx` running from `-288` up to 0 by 8, a tail); SSE3 replaces
`movlps`+`movlhps` by `movddup`, `movlps` by `movsd`, and the shuffle/add
pairs of the tail by `haddps`/`movshdup`. `spec_sse` and `spec_sse3` prove
`AutocorrelateSpec` at the two entries: called with the 320 bytes of `x`, the
48 of `phi` and the 16 of `ps_mask3` owned, 40 bytes of stack reserved, `phi`
and `ps_mask3` 16-aligned and the stack aligned as the SysV convention
requires, the routine returns with the convention restored, having touched
only those bytes and its reservation.

## Notes

* Footprint = the C contract of `libavcodec/sbrdsp.h` and
  `tests/checkasm/sbrdsp.c`: the loads cover exactly `x[0..39]` (the last
  load is the 8 bytes at `x + 312`); `x` needs no alignment (`movlps`/`movsd`/
  `movddup` loads are unaligned). The call site (`X_low[k]`, a `[40][2]` row
  of `X_low[32][40][2]`) meets it.
* `phi` must be 16-aligned (the `movaps` store to `(%rsi)`); `checkasm` and
  `aacsbr.c` (`LOCAL_ALIGNED_16(float, phi, [3], [2][2])`) guarantee it.
  Only `phi[0][*][*]`, `phi[1][0][0]`, `phi[1][1][*]`, `phi[2][1][0]` are
  written (bytes 0-19, 24-31, 40-43); the rest of `phi` is left as it was.
  `aacsbr.c` reads only written entries. (The fixed-point decoder never
  reaches this routine: `ff_sbrdsp_init_x86` is called only `#if !USE_FIXED`,
  `libavcodec/sbrdsp_template.c`.)
* `ps_mask3` must be 16-aligned (`xorps` memory operands).
* Stack: `sub $0x28,%rsp` and two `movaps` to `(%rsp)`/`0x10(%rsp)`: the
  reservation is 40 bytes (x86inc's 32 bytes of `stack_size`, rounded so that
  `rsp` is 16-aligned after the `sub`), and the entry `rsp` must satisfy the
  SysV alignment (`rsp + 8` 16-aligned). Dropping that condition from
  `AutocorrelateC` makes the entry block (the `movaps` stores) and the
  `.tail` block (the aligned `addps (%rsp)` loads) fail (negative check,
  scratch).
  The reservation is carried as one owned block (`Own`) that the code writes
  and reads back; `Reserve 40 r` is that block at entry and exit (`Reserve_eq`,
  with the entry's headroom `CallPre.le`).
* Proof shape: four blocks per entry (entry, `.loop`, `.tail` after the
  `jl`, `.done` with the `ret`). The loop invariant needs `rsi = phi`
  although the loop does not touch `rsi`: the tail writes through it.
  Two rules were missing (now in `Kraken/Rules/LeafLemmas.lean`): `jl` after `add`
  (`CondCode.interp_l_add`; the library had only `jl` after `cmp`), and
  `Blocks.Inside` for an address `p + i + d` whose terms do not line up with
  the block base (`Mem.Blocks.Inside.of_sub3`), e.g. `rdi' + (rdx + 8) + 16`
  with `rdi' = x + 296` known only as an equation. Its `grind` pattern is
  scoped (`open scoped Kraken.LeafLemmas.Offset`), with a `check` guard.
* Rule-file `grind` scopes opened (see `Kraken/Rules/*.lean`):
  `Kraken.Rules.GenericMem.Norm`, `Kraken.Rules.IntMisc.SubReg`,
  `Kraken.Rules.ScalarFloat.FCmp`, `Kraken.Rules.ScalarFloat.Xmm`.
-/

open Kraken.X64.Parser
open Kraken
open Kraken.SysV
open Std.WP
open Mem
open MachineWP
open scoped Kraken.LeafLemmas.Offset Kraken.LeafLemmas.AddFlags Kraken.LeafLemmas.NegIdx
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg
open scoped Kraken.Rules.ScalarFloat.FCmp Kraken.Rules.ScalarFloat.Xmm

set_option mvcgen.warning false
set_option grind.warning false


namespace Kraken.Examples.Sbr.Autocorrelate

variable [CodeEnv]

/-- The caller's side of memory behind the footprint and the frame: the
return address and `R`. A `def`, so that `grind` moves it whole. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The frame (the 40 reserved bytes, as one block the code writes) in front
of the footprint. -/
abbrev Own (t₀ : MachineData) : Mem 64 → Prop :=
  Blocks [(t₀.regs.get64 .rsp - 0x28#64, 0x28), (arg0 t₀, 320), (arg1 t₀, 48),
    (lab "ps_mask3", 16)]

abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_autocorrelate_sse", s => s = t₀ ∧ AutocorrelateC t₀
      ∧ (t₀.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_autocorrelate_sse.loop", s =>
      let k := (s.regs.get64 .rdx + 0x120#64).toNat
      AutocorrelateC t₀ ∧ s.regs.get64 .rdi = arg0 t₀ + 0x128#64
      ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ k < 288 ∧ k % 24 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_autocorrelate_sse.tail", s =>
      AutocorrelateC t₀ ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_autocorrelate_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | _, _ => False

abbrev var : Label → MachineData → Nat
  | "ff_sbr_autocorrelate_sse.loop", s => 288 - (s.regs.get64 .rdx + 0x120#64).toNat
  | "ff_sbr_autocorrelate_sse.tail", _ => 1
  | "ff_sbr_autocorrelate_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev Post' (R : Mem 64 → Prop) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ Own t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp) ⋆ R))

theorem spec_sse (hpl : Program.PlacedIn body) :
    AutocorrelateSpec "ff_sbr_autocorrelate_sse" := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀ _
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
    simp only [Own, Blocks, Rest, CallPre, Reserve_eq _ _ (CallPre.le hcall)] at h ⊢
    exact Mem.ac h
  · rintro R ra t₀ s ⟨hcall, -⟩ ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    simp only [Own, Blocks, Reserve_eq _ _ (CallPre.le hcall)] at hm ⊢
    exact Mem.ac hm

/-! ## The SSE3 variant: same CFG, `movddup`/`movsd` loads and `haddps` in the tail -/

abbrev table3 (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_autocorrelate_sse3", s => s = t₀ ∧ AutocorrelateC t₀
      ∧ (t₀.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_autocorrelate_sse3.loop", s =>
      let k := (s.regs.get64 .rdx + 0x120#64).toNat
      AutocorrelateC t₀ ∧ s.regs.get64 .rdi = arg0 t₀ + 0x128#64
      ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ k < 288 ∧ k % 24 = 0
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_autocorrelate_sse3.tail", s =>
      AutocorrelateC t₀ ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_autocorrelate_sse3.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ Own t₀ ⋆ Rest R ra t₀)
  | _, _ => False

abbrev var3 : Label → MachineData → Nat
  | "ff_sbr_autocorrelate_sse3.loop", s => 288 - (s.regs.get64 .rdx + 0x120#64).toNat
  | "ff_sbr_autocorrelate_sse3.tail", _ => 1
  | "ff_sbr_autocorrelate_sse3.done", _ => 0
  | _, _ => 2 ^ 64

theorem spec_sse3 (hpl : Program.PlacedIn body3) :
    AutocorrelateSpec "ff_sbr_autocorrelate_sse3" := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body3) table3 Post' var3
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀ _
    cfg_cases [body3]
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
    simp only [Own, Blocks, Rest, CallPre, Reserve_eq _ _ (CallPre.le hcall)] at h ⊢
    exact Mem.ac h
  · rintro R ra t₀ s ⟨hcall, -⟩ ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    simp only [Own, Blocks, Reserve_eq _ _ (CallPre.le hcall)] at hm ⊢
    exact Mem.ac hm

end Kraken.Examples.Sbr.Autocorrelate
