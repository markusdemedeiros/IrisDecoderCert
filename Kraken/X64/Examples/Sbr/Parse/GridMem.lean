import Kraken.X64.Examples.Sbr.Parse.GridEntry

/-!
# `read_sbr_grid`: footprint access lemmas

Each block touches a few bytes of a footprint of about fifty cells. Instead of letting
`grind` search the whole separating conjunction, a block brings the part it touches to the
front (`T_fr`, `T_te`, `T_blocks`) and uses one of the lemmas below, each proved once.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- A load from the bitstream buffer. -/
theorem T_buf_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (off : BitVec 64) (n : Nat) (hin : off.toNat + n ≤ x.L) :
    (m.loadInt (x.buf + off) n).isSome = true := by
  obtain ⟨F, hB⟩ := T_blocks h
  exact blocks_load hB hin

theorem sinv_st1 (x : GArgs) (hC : GridC x) : SInv x (st1 x) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, hnn, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2, -⟩,
    hten, hi, hp, -⟩ := hC
  have e1 : (BitVec.ofNat 32 x.v.nenv).toNat = x.v.nenv := by
    rw [BitVec.toNat_ofNat]; omega
  have e2 : (BitVec.ofNat 32 x.v.nnoise).toNat = x.v.nnoise := by
    rw [BitVec.toNat_ofNat]; omega
  refine ⟨⟨?_, hil, ?_, hql, ?_, ?_, ?_, hinv, hy, ?_, ?_, hidx1, hidx2, hv1, hv2, fun h => h.elim⟩,
    ?_, ?_⟩
  all_goals simp only [st1, st1a, GSt.dv, GArgs.st, e1, e2, List.length_set, u8]
  all_goals try omega
  · intro e he
    rw [getD_set_if _ _ _ _ (by omega)]
    split
    · exact hfr _ (Nat.le_refl _)
    · exact hfr e he
  · rw [getD_set_eq _ _ _ (by omega)]; exact hten
  · rw [getD_set_ne _ _ _ _ (by omega)]; exact hten


end Kraken.Examples.Sbr.Grid
