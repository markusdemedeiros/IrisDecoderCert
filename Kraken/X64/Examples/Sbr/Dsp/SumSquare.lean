import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.GenericMem
import Kraken.Rules.PackedSse
import Kraken.Rules.IntMisc
import Kraken.Rules.ScalarFloat
import Kraken.X64.Examples.Sbr.Spec
import Kraken.Rules.LeafLemmas
import Kraken.X64.Examples.Sbr.Dsp.SumSquareText

/-!
# `ff_sbr_sum_square_sse` as a `ProcSpec`

`sbr_sum_square(x, n)` returns the sum of the squares of the floats of
`x[n][2]` (`libavcodec/x86/sbrdsp.asm`). `spec` proves `SumSquareSpec`: a call
with the `8 * n` bytes of `x` owned returns with the SysV convention restored
and the footprint still owned; nothing else is assumed.

## Notes

* Footprint: `x[n][2]` read, `8 * n` bytes, with `n` the low 32 bits of `rsi`
  read unsigned (`mov %esi,%edx` zero-extends). The main loop reads
  `64 * (n / 8)` bytes, the tail loop `16 * (n % 8 / 2)` (`and $7,%rsi` reads
  the full `rsi`, but its low three bits are those of `n`): in all
  `8 * (n - n % 2)` bytes. So an odd `n` drops the last pair, and no shape of
  `n` is needed for memory safety (`.endloop`'s comment "len is a multiple of
  2" concerns the result only). `tests/checkasm/sbrdsp.c` passes `n = 256`;
  the call sites in `libavcodec/aacsbr_template.c` (`sbr_env_estimate`) pass
  `iub - ilb = 2 * (t_env[e + 1] - t_env[e]) ≥ 0`, even.
* No side condition `C`: the loads are `movups`, so `x` needs no alignment,
  and no constant is read. A negative `int n` would be read as `n + 2^32`, so
  the footprint would be (up to) 32 GiB: the contract, read in C, is `n ≥ 0`.
* No stack, no callee-saved register: the reservation is 0.
* Negative check (scratch): with the footprint shrunk to `8 * n - 1` bytes, the
  main-loop and tail-loop blocks fail (their loads leave the block). Without
  the `sar` result flags, the entry and `.prepare` blocks fail: the
  generated `sar` rule used to leave `zf` arbitrary, so the `je` after it can go
  either way and the loop invariants (`1 ≤` count) cannot be established.
* Rules found missing: the generated shift rules (`Rules/IntMisc.lean`) dropped
  the result flags, although `Operation.interp` defines `zf`/`sf`/`pf` by
  `from_result`; the generator now states them. In
  `Kraken/Rules/LeafLemmas.lean`: two
  `toNat` facts for `sar` of a value with a clear top bit; and
  `Blocks.Inside.ptr_add_add`, the moving-pointer rule for the address shape
  `p + 0 + c` of `c(%p)` through the `movups` rules (`ptr_add` only matches
  `p + x`).
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
open scoped Kraken.LeafLemmas.PtrAdd Kraken.LeafLemmas.Shift
open scoped Kraken.Rules.GenericMem.Norm Kraken.Rules.IntMisc.SubReg
open scoped Kraken.Rules.ScalarFloat.FCmp Kraken.Rules.ScalarFloat.Xmm

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.SumSquare

variable [CodeEnv]

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)

abbrev table (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_sbr_sum_square_sse", s => s = t₀ ∧ SumSquareC t₀
      ∧ (t₀.dmem =⋆ SumSquareF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum_square_sse.loop", s =>
      let x := arg0 t₀
      let n := sumSquareN t₀
      let k := (s.regs.get64 .rdx).toNat
      s.regs.get64 .rsi = arg1 t₀ ∧ 1 ≤ k
      ∧ (s.regs.get64 .rdi - x).toNat + 64 * k = 64 * (n / 8)
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ SumSquareF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum_square_sse.prepare", s =>
      let x := arg0 t₀
      let n := sumSquareN t₀
      s.regs.get64 .rsi = arg1 t₀
      ∧ (s.regs.get64 .rdi - x).toNat = 64 * (n / 8)
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ SumSquareF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum_square_sse.endloop", s =>
      let x := arg0 t₀
      let n := sumSquareN t₀
      let k := (s.regs.get64 .rsi).toNat
      1 ≤ k ∧ k ≤ 3
      ∧ (s.regs.get64 .rdi - x).toNat + 16 * k = 64 * (n / 8) + 16 * (n % 8 / 2)
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ SumSquareF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum_square_sse.end", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ SumSquareF t₀ ⋆ Rest R ra t₀)
  | "ff_sbr_sum_square_sse.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ SumSquareF t₀ ⋆ Rest R ra t₀)
  | _, _ => False

abbrev var : Label → MachineData → Nat
  | "ff_sbr_sum_square_sse.loop", s => (s.regs.get64 .rdx).toNat + 10
  | "ff_sbr_sum_square_sse.prepare", _ => 9
  | "ff_sbr_sum_square_sse.endloop", s => (s.regs.get64 .rsi).toNat + 2
  | "ff_sbr_sum_square_sse.end", _ => 1
  | "ff_sbr_sum_square_sse.done", _ => 0
  | _, _ => 2 ^ 64

abbrev Post' (R : Mem 64 → Prop) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ SumSquareF t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp)
      ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ R)))

set_option maxHeartbeats 1000000 in
theorem spec (hpl : Program.PlacedIn body) : SumSquareSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) table Post' var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [body]
    · vcgen with finish
    · vcgen with finish
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
    show (_ ⋆ (_ ⋆ (SumSquareF t₀ ⋆ R))) s.dmem
    rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
    exact hm

end Kraken.Examples.Sbr.SumSquare
