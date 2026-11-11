set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_y11 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y11" := by
  clear hc
  cfg_block
  measure_hb "y11"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hte9 : x.te 9 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.2.1
    rw [T_eq_TR] at hm
    refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs
      ∧ s.zmms.get (.xmm .mm4) = s₀.zmms.get (.xmm .mm4)
      ∧ (s.dmem =⋆ DataW x t₀ ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀))) ?_ ?_
    · by_cases heq : x.te 0 = x.te 9
      · rw [heq] at h8
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x240#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y11-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x240#64)
          (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) + 0x240#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y11-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y12" s ∧ var "sbr_hf_assemble.y12" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)
