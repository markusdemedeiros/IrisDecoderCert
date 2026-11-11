import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.GenericMem
import Kraken.Rules.IntMisc
import Kraken.Rules.PackedSse
import Kraken.Rules.ScalarFloat
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.HfGFiltText

/-!
# `ff_sbr_hf_g_filt_sse` as a `ProcSpec`

`sbr_hf_g_filt(Y, X_high, g_filt, m_max, ixh)` sets
`Y[m] = X_high[m][ixh] * g_filt[m]` (two floats each) for `m < m_max`
(`libavcodec/x86/sbrdsp.asm`). `spec` proves `HfGFiltSpec`: a call with
`ixh < 40`, a row count `m` (below) of at least 1, and the `8 * m` bytes of
`Y`, the `320 * m` bytes of `X_high` and the `4 * m` bytes of `g_filt` owned,
returns with the SysV convention restored and only those bytes changed.

The code does `m_max & 0xfc` rows four at a time (`.loop4`, a negative index
`rcx` counting up to 0 against `g_filt`/`Y` pointers advanced to row
`m_max & 0xfc`), then `m_max & 3` single rows (`.loop1`, counted down in `r9`).

## Notes

* The row count is the low 8 bits of `rcx`, not `m_max`: both masks are
  applied to the full register (`and $0xfc,%rcx`, `and $0x3,%r9`), so
  `m_max ≥ 256` would silently do `m_max % 256` rows. The footprint is stated
  for `m = rcx % 256`; at the call site (`libavcodec/aacsbr.c`,
  `sbr_hf_assemble`: `m_max = sbr->m[1]`, ≤ 48 by `SbrWF`) this is `m_max`.
* `m_max = 0` is **not** handled: `.loop1` is entered with `r9 = 0` and
  `dec %r9; jne` runs about `2^64` iterations, writing far past `Y`. Hence
  `1 ≤ m` in `HfGFiltC`. `tests/checkasm/sbrdsp.c` only calls with 128; the C
  reference is fine with 0. Whether `sbr->m[1]` can be 0 at the call is for
  `SbrWF` (M4): `sbr_turnoff` (`libavcodec/aacsbr_template.c`) sets it to 0
  for pure upsampling mode, together with `start = 0`.
* When `m_max < 4`, `.loop1` counts down the *whole* `rcx` copied into `r9`
  (`mov %rcx,%r9`, no `and` on that path), and the upper 32 bits of an `int`
  argument are unspecified under SysV. Hence `m < 4 → rcx < 4` (all 64 bits)
  in `HfGFiltC`. When `m ≥ 4`, the upper bits do not matter. A caller that
  zero-extends `m_max` (a 32-bit `mov`, as compilers do) meets it.
* `ixh < 40` (PLAN table) is what the reads need: the last read of row `i` is
  `X_high + 320 i + 8 ixh`, 8 bytes. `ixh` is `intptr_t`, used as a full
  64-bit value. Owning all of `X_high[m][40][2]` is the C contract; only
  column `ixh` is read.
* No alignment is needed (`movlps`/`movhps`/`movss`/`movups`); no constant
  is read; no stack, no callee-saved register: the reservation is 0.
* Rules added (now in `Kraken/Rules/LeafLemmas.lean`, patterns opened by
  `open scoped Kraken.LeafLemmas.NegIdx`): `Blocks.Inside` for a
  negative index (`neg_idx`, `neg_idx_disp`: address `p + i * c (+ d)` with
  `0 - i` elements left before `p`), for a bare pointer (`ptr`: `(%rsi)`
  leaves the address `rsi`), and for `p + 0 + d` (`ptr_add_add`: the generic
  memory rules leave `AddrIndex.offset64 none = 0` in the middle of
  `rsi + 0 + 0x280`, where `ptr_add` does not match). Also a local
  `grind norm` on `BitVec.zero_eq`.
* Proof shape: as `NegOdd64.lean`, with the `.end` label of the routine as
  the `ret` block. The work blocks are `vcgen; all_goals grind (splits := 40)`:
  the default 9 case splits are not enough for the 13-conjunct invariants
  (each negated conjunct is a split), and `vcgen with finish (splits := 40)`
  did not raise the limit. A first invariant that stated the row as the
  bit-vector `rcx + K` timed out at `whnf` (`grind` expanding `toNat` of
  sums of unknowns); the invariant over `(0 - rcx).toNat`, with
  `neg_idx_disp`, closes the whole loop block without splitting it.
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
open scoped Kraken.LeafLemmas.NegIdx Kraken.LeafLemmas.PtrAdd
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg
open scoped Kraken.Rules.ScalarFloat.FCmp Kraken.Rules.ScalarFloat.Xmm

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.HfGFilt

/-- `m_max & 0xfc` and `m_max & 3` as numbers. -/
theorem and_252 (x : BitVec 64) : (x &&& 252#64).toNat = x.toNat % 256 / 4 * 4 := by
  rw [BitVec.toNat_and]
  have h1 : (252#64).toNat = 255 &&& 252 := by decide
  rw [h1, ← Nat.and_assoc]
  have h2 : x.toNat &&& 255 = x.toNat % 256 := by
    have := Nat.and_two_pow_sub_one_eq_mod x.toNat 8
    simpa using this
  rw [h2]
  have : ∀ r < 256, r &&& 252 = r / 4 * 4 := by decide +kernel
  exact this _ (Nat.mod_lt _ (by decide))

theorem and_3 (x : BitVec 64) : (x &&& 3#64).toNat = x.toNat % 256 % 4 := by
  rw [BitVec.toNat_and]
  have := Nat.and_two_pow_sub_one_eq_mod x.toNat 2
  simp at this
  simp [this]

variable [CodeEnv]

/-- The two masks of `m_max`, as facts the blocks carry. -/
abbrev Masks (t₀ : MachineData) : Prop :=
  (arg3 t₀ &&& 252#64).toNat = hfGFiltM t₀ / 4 * 4
  ∧ (arg3 t₀ &&& 3#64).toNat = hfGFiltM t₀ % 4

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

/-- At `.loop4`, `rdx`/`rdi` point at row `K = m & 0xfc` of `g_filt`/`Y` and
`0 - rcx = j` rows (a multiple of 4) are left before them, so the row is
`K - j`; `rsi` points at row `K - j` of `X_high`, column `ixh`. At `.loop1`,
`r9 = r` rows are left and the three pointers are at row `m - r`. -/
abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_hf_g_filt_sse", s => s = t₀ ∧ HfGFiltC t₀ ∧ Masks t₀
      ∧ (t₀.dmem =⋆ HfGFiltF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_hf_g_filt_sse.loop4", s =>
      let K := (arg3 t₀ &&& 252#64).toNat
      let j := (0 - s.regs.get64 .rcx).toNat
      HfGFiltC t₀ ∧ Masks t₀
      ∧ j % 4 = 0 ∧ 4 ≤ j ∧ j ≤ K
      ∧ (s.regs.get64 .rdx - arg2 t₀).toNat = K * 4
      ∧ (s.regs.get64 .rdi - arg0 t₀).toNat = K * 8
      ∧ (s.regs.get64 .rsi - arg1 t₀).toNat = (arg4 t₀).toNat * 8 + (K - j) * 320
      ∧ s.regs.get64 .r9 = arg3 t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ HfGFiltF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_hf_g_filt_sse.loop1", s =>
      let m := hfGFiltM t₀
      let r := (s.regs.get64 .r9).toNat
      HfGFiltC t₀ ∧ 1 ≤ r ∧ r ≤ 3 ∧ r ≤ m
      ∧ (s.regs.get64 .rdx - arg2 t₀).toNat = (m - r) * 4
      ∧ (s.regs.get64 .rdi - arg0 t₀).toNat = (m - r) * 8
      ∧ (s.regs.get64 .rsi - arg1 t₀).toNat = (arg4 t₀).toNat * 8 + (m - r) * 320
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ HfGFiltF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_hf_g_filt_sse.end", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ HfGFiltF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

/-- The variant: rows left (four per row at `.loop4`, plus a margin above the
at most 3 single rows); 0 at `.end`. -/
abbrev var : Label → MachineData → Nat
  | "ff_sbr_hf_g_filt_sse.loop4", s => 4 * (0 - s.regs.get64 .rcx).toNat + 10
  | "ff_sbr_hf_g_filt_sse.loop1", s => (s.regs.get64 .r9).toNat + 1
  | "ff_sbr_hf_g_filt_sse.end", _ => 0
  | _, _ => 2 ^ 64

abbrev Post' (R : Mem 64 → Prop) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ HfGFiltF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

/- `zf` of a result is `v == BitVec.zero w` (`StatusFlags.zf_from_result`);
normalising `BitVec.zero` to `0` lets `grind` read `neg`'s `zf` arithmetically
instead of splitting the disequality into bits. -/
attribute [local grind norm] BitVec.zero_eq

set_option maxHeartbeats 300000 in
theorem spec (hpl : Program.PlacedIn body) : HfGFiltSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen
      all_goals grind (splits := 40)
    · vcgen
      all_goals grind (splits := 40)
    · vcgen
      all_goals grind (splits := 40)
    · vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · rintro R ra t ⟨hcall, hc⟩
    refine ⟨rfl, hc, ⟨by rw [and_252], by rw [and_3]⟩, ?_⟩
    have h := hcall
    simp only [Rest, CallPre] at h ⊢
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
    exact h
  · rintro R ra t₀ s ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    show (_ ⋆ (_ ⋆ (HfGFiltF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.HfGFilt
