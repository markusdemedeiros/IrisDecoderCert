import Kraken.X64.Examples.Sbr.Parse.UsacBlk10

/-!
# `ff_aac_sbr_decode_usac_data`: the inlined `copy_sbr_grid`, the bound check (`L3724`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- `mov` of a 4-byte cell holding `n ≤ 8` into `eax`. -/
theorem usC_zx (n : Nat) (h : n ≤ 8) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int))))
      = BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl]
  revert n; decide

omit [CodeEnv] in
theorem usC_nc_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, hf]
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.unsigned_eq]
  by_cases h : b.toNat ≤ a.toNat
  · rw [h₁ h]; simp [h]; omega
  · rw [h₂ (by omega)]; simp [h]; omega

omit [CodeEnv] in
theorem usC_w9 : (BitVec.setWidth 64 (Int64.toBitVec 9)).toNat = 9 := by decide

/-- `L3724`: `bs_num_env` of channel 1 below 9 (the `jae` to the trap is dead). -/
theorem blk_L3724 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3724" := by
  cfg_block
  measure_hb "L3724"
    intro n
    simp only [tbl_L3724, var_L3724, tbl_L3734, var_L3734]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, h15⟩, rfl⟩ := hs₀
    have hn8 : st.x.d1.nenv ≤ 8 := hP.1.1.1.1.2.2.2.1.2.2.2.2.1
    have hm2 := hm
    simp only [UM, UF, DSc, dAc, sA, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc, BitVec.reduceAdd] at hm2
    have l1 : s₀.dmem.loadInt (A.1.c + 255080#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.d1.nenv : Int))) := by sep_mem hm2 <;> rfl
    clear hm2
    have l1' : s₀.dmem.loadInt (s₀.regs.get64 .rbx + Int64.toBitVec 255080) 4
        = some (Int.ofBytes (Int.toBytes 4 (st.x.d1.nenv : Int))) := by
      simp only [BitVec.ofNat_eq_ofNat, Int64.toBitVec_ofNat_norm, hbx]
      exact l1
    clear l1
    vcgen
    all_goals try subst_vars
    all_goals simp only [l1', Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    case vc2 =>
      rename_i c
      simp only [Reg64s.get64_set64, ite_true, usC_zx _ hn8] at c
      rw [usC_nc_sub _ _ _ rfl, usC_w9, BitVec.toNat_ofNat] at c
      simp only [decide_eq_true_eq] at c
      exact absurd c (by omega)
    case vc3 =>
      refine ⟨?_, Nat.le_refl _⟩
      simp only [T_L3734, AtCp, AtD, AtI, At, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false]
      exact ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, trivial, hm⟩, h15⟩, st, hI, hP.1,
        hP.2, by omega, usC_zx _ hn8, hm⟩

end Kraken.Examples.Sbr.Usac
