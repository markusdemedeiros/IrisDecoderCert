import Kraken.X64.Examples.Sbr.Parse.TlimText
import Kraken.MachineWP
import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.LibCall

/-!
# `sbr_make_f_tablelim`: the specification

`sbr_make_f_tablelim(sbr)` (`libavcodec/aacsbr_template.c` l.137-186, FFmpeg n8.1) builds the
limiter band table `f_tablelim[0..n_lim]` from `f_tablelow[0..n[0]]` and the patch borders
(`kx[1]` plus the partial sums of `patch_num_subbands`), sorts it with `AV_QSORT` and compacts
it.

* Logical variables `TArgs`: the caller's memory `R`, the decoder values `a : Args`
  (`ApplySpec.lean`; the routine reads `kx[1]`, `n[0]`, `num_patches`, `patch_num_subbands`,
  `f_tablelow`, and writes `f_tablelim`, `n_lim`), and `bs_limiter_bands`.
* Postcondition: the values the routine leaves are a successor of `a` in the model's
  `Tablelim` (`ParseModel.lean`), with the footprint given back cell by cell. The model's
  `tablelim_spec` turns this into `n_lim ≤ 29` and `f_tablelim` inside `[kx[1], kx[1] + m[1]]`
  and nondecreasing up to `n_lim`, so `tabwf_lim` keeps `TabWF`.
* The callee `memcpy` is `MemcpyValSpec` (`LibCall.lean`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

/-! ## `sbr_make_f_tablelim` -/

structure TArgs where
  R : Mem 64 → Prop
  a : Args
  lb : BitVec 32

/-- `bands_warped[3]` (`.rodata+0x70` of `aacsbr.o`, no symbol): read only. -/
abbrev BW : BitVec 64 := lab "sbr_make_f_tablelim_bw"

/-- The fields of `*sbr` (`s = sbr`, the first argument): `bs_limiter_bands` (+0x2c), `kx[1]`
(+0x58), `n[0]`, `n_lim`, `f_tablelow`, `f_tablelim`, `num_patches`, `patch_num_subbands`
(the layout of `ScW`/`TabW`), and `bands_warped`. -/
def TlimF (lb : BitVec 32) (a : Args) (t : MachineData) : Mem 64 → Prop :=
  let s := arg0 t
  cell4 (s + 0x2c#64) lb ⋆ (c4 (s + 0x58#64) a.kx1 ⋆ (c4 (s + 0x4c1e0#64) a.n0
    ⋆ (c4 (s + 0x4c1ec#64) a.nlim ⋆ (a.ftLow =@ (s + 0x4c252#64) ⋆ (a.ftLim =@ (s + 0x4c2f2#64)
    ⋆ (c4 (s + 0x4c330#64) a.npatch ⋆ (a.pnum =@ (s + 0x4c334#64) ⋆ Blocks [(BW, 12)])))))))

/-- The side conditions: `bs_limiter_bands ≤ 3`; the sizes `n[0] ≤ 24`, `num_patches ≤ 6`
and, for a nonzero `bs_limiter_bands`, `n[0] + num_patches ≥ 1` (`n_lim ≥ 0`, `Inv2` in the
model); the array lengths; `f_tablelow[0..n[0]]` and the patch borders inside
`[kx[1], kx[1] + m[1]] ⊆ [0, 64]` (the hypotheses of `tablelim_spec`; the code compares the
entries as `int16_t`); `*sbr` does not wrap around the address space. -/
def TlimC (lb : BitVec 32) (a : Args) (t : MachineData) : Prop :=
  lb.toNat ≤ 3 ∧ a.n0 ≤ 24 ∧ a.npatch ≤ 6 ∧ (0 < lb.toNat → 1 ≤ a.n0 + a.npatch)
  ∧ a.ftLow.length = 50 ∧ a.ftLim.length = 60 ∧ a.pnum.length = 6
  ∧ TabIn a.ftLow a.n0 a.kx1 (a.kx1 + a.m1) ∧ psum a.pnum a.npatch ≤ a.m1 ∧ a.kx1 + a.m1 ≤ 64
  ∧ a.nlim < 2 ^ 32 ∧ (arg0 t).toNat + 0x4c340 < 2 ^ 64

/-- The stack: five pushes, `0x420` bytes of locals (the `AV_QSORT` stack `void *[64][2]`,
`patch_borders`, a spill), the return slot of a call, the callee's `k`. -/
abbrev tlimNeed (k : Nat) : Nat := 0x450 + k

abbrev TlimPre (k : Nat) (x : TArgs) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (tlimNeed k) (TlimF x.lb x.a t ⋆ x.R) ra t ∧ TlimC x.lb x.a t

/-- On return: `f_tablelim` and `n_lim` are the model's (`Tablelim`), nothing else changed. -/
abbrev TlimPost (k : Nat) (x : TArgs) (ra : Int64) (t s : MachineData) : Prop :=
  ∃ y, Tablelim x.lb.toNat x.a y ∧ CallPost (tlimNeed k) (TlimF x.lb y t ⋆ x.R) ra t s

/-- The contract `sbr_reset` and the header use. -/
abbrev TlimSpec (k : Nat) : Prop :=
  cenv.ProcSpec (entry "sbr_make_f_tablelim") (TlimPre k) (TlimPost k)

end Kraken.Examples.Sbr.Tlim
