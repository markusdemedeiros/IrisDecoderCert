import Kraken.X64.Examples.Sbr.Parse.TlimQsLib

/-!
# `sbr_make_f_tablelim`: `AV_QSORT`, the pop (`L4060`, `L4068`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L4060 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4060" := by
  cfg_block
  measure_hb "L4060"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hQ, hn⟩ := hs₀
    rw [var_L4060] at hn
    subst hn
    obtain ⟨hR, S, hcx, hD, hM⟩ := hQ
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by have := NN_le hR.1; omega)
    have hH : Hide _ := hM
    clear hM
    vcgen
    all_goals try subst_vars
    · rename_i hz
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, hcx] at hz
      have h0 : S.length = 0 := by simp at hz; bv_omega
      obtain rfl : S = [] := List.eq_nil_of_length_eq_zero h0
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by rw [var_L429d]; omega)⟩
      rw [tab_L429d]
      unfold Hide at hH
      obtain ⟨fl, stk, pb, hL, hP, ⟨-, hQI⟩, hm⟩ := hH
      exact ⟨hR, fl, stk, pb, hL, hP, qi_Sorted hQI, hm⟩
    · rename_i hz
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, hcx] at hz
      have h0 : BitVec.ofNat 64 S.length ≠ 0#64 := by simp at hz; bv_omega
      rw [tab_L4068, var_L4068]
      exact ⟨⟨⟨hR, S, hcx, hD, hH⟩, by rw [hcx]; exact h0⟩, Nat.le_refl _⟩

end Kraken.Examples.Sbr.Tlim

namespace Kraken.Examples.Sbr.Tlim
variable [CodeEnv]
open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L4068 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4068" := by
  cfg_block
  measure_hb "L4068"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hR, S, hcx, hD, fl, stk, pb, hL, hP, ⟨hSR, hQI⟩, hm⟩, hne⟩, hn⟩ := hs₀
    rw [var_L4068] at hn
    subst hn
    have hS6 : S.length ≤ 6 := depth_len (m := 6) hD (by have := NN_le hR.1; omega)
    have hS1 : S ≠ [] := by rintro rfl; exact hne (by rw [hcx]; rfl)
    obtain ⟨S', I, rfl⟩ : ∃ S' I, S = S' ++ [I] :=
      ⟨S.dropLast, S.getLast hS1, (List.dropLast_concat_getLast hS1).symm⟩
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hS6 hcx hne
    obtain ⟨hSR', r1, r2⟩ := stkRel_pop hSR
    obtain ⟨hD', hDc⟩ := depth_pop hD
    have hbp : s₀.regs.get64 .rbp = rS t₀ - 8#64 := hR.2.1.1.2.1
    obtain ⟨hl1, hl2, hl3⟩ := id hL
    simp only at hl1 hl2 hl3
    have hpn := pA_nat hR.1
    have hN := NN_le hR.1
    have hWc := qi_cur hQI
    have hW := hQI.2.2.1
    have hphi := stkPhi_eq hm hl2 hbp (p := pA t₀) (N := NN x) (by omega) (by omega) hSR hW
      (by simp; omega)
    have hphi' := stkPhi_eq hm hl2 hbp (p := pA t₀) (N := NN x) (by omega) (by omega) hSR'
      (fun J hJ => hW J (by simp [hJ])) (by omega)
    have hst := focus (T_stk k x ra t₀ (Saved t₀) _) hm
    obtain ⟨v1, hv1, e1⟩ := ld64 hst (2 * S'.length) (addr := s₀.regs.get64 .rbp
      + BitVec.ofNat 64 (16 * S'.length) + 18446744073709550528#64)
      (by rw [hbp]; exact addr_pop0 _ _ (by omega)) (by simp only; omega) (by simp only; omega)
    obtain ⟨v2, hv2, e2⟩ := ld64 hst (2 * S'.length + 1) (addr := s₀.regs.get64 .rbp
      + BitVec.ofNat 64 (16 * S'.length) + 18446744073709550536#64)
      (by rw [hbp]; exact addr_pop1 _ _ (by omega)) (by simp only; omega) (by simp only; omega)
    have hwB := wB_iv (p := pA t₀) (by omega) hWc.1 (hi1 := I.2) (lo := I.1) (by omega)
    rw [show wt (I.1, I.2) = wt I from rfl] at hwB
    have hmT : Hide _ := hm
    clear hm hst
    have ed := dec32 (S'.length + 1) (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at ed
    have es := shl4 S'.length (by omega)
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceSub, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.ofNat_eq_ofNat, hcx, ed, es, hv1, hv2,
      Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · exfalso; rename_i hc
      rw [nc32_cmp _ _ (by omega) (by omega)] at hc
      simp at hc; omega
    · rw [tab_L4090, var_L4090]
      refine ⟨⟨hR, S', I.1, I.2, fl, stk, pb, hL, hP, ⟨hSR', ⟨by simp, hD', hDc, ?_, ?_, hQI⟩,
        trivial⟩, hmT⟩, ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e1, r1]; try rfl
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e2, r2]; try rfl
      · simp only [phiC, rN, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, e1, e2, r1, r2]
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hphi
        rw [stkPhi_mk _ _ _ _ (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), hphi',
          hphi, hwB, phi_append, phi_one, QV]
        omega

end Kraken.Examples.Sbr.Tlim
