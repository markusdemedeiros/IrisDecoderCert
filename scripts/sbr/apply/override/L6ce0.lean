theorem blk_L6ce0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ce0" ⟨"ff_aac_sbr_apply.L6ce0", B.L6ce0, some "ff_aac_sbr_apply.L6cea"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6ce0.mp hs).2.2.2.2
  have h9 := (T.L6ce0.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6ce0]
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨jj, hjj, hrdx, hrsi, hrax, hx0⟩, -⟩ := T.L6ce0.mp hs
  all_goals obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals try sep_vals hm
  all_goals try simp only [dq_ofb4 _ (show x.nq < 2^31 by omega), dq_ofb4 _ (show x.d0.nnoise < 2^31 by omega), Nat.reducePow, Nat.reduceMod, Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_true_eq, Bool.or_eq_true] at *
  all_goals have edx := congrArg BitVec.toNat hrdx
  all_goals have esi := congrArg BitVec.toNat hrsi
  all_goals have eax := congrArg BitVec.toNat hrax
  all_goals simp only [dq_ofNat_toNat _ (show x.d0.nnoise + 1 < 2 ^ 64 by omega)] at eax
  all_goals simp only [dq_ofNat_toNat _ (show jj + 1 < 2 ^ 64 by omega), dq_ofNat_toNat _ (show 5 * jj < 2 ^ 64 by omega)] at edx esi
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    hrsp, hrbp, hrdx, hrsi, hrax]
  all_goals try simp only [dq_a_3e3f5, dq_a_3e3f6, dq_a_3e3f7, dq_a_3e3f8, dq_a_3e3f9,
    dq_a_53eb5, dq_a_53eb6, dq_a_53eb7, dq_a_53eb8, dq_a_53eb9, dq_a_3e414, dq_a_3e418, dq_a_3e41c,
    dq_a_3e420, dq_a_3e424, dq_a_53ed4, dq_a_53ed8, dq_a_53edc, dq_a_53ee0, dq_a_53ee4]
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_mul, Nat.reduceMod, Nat.mod_eq_of_lt (show 5 * jj < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 5 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 6 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 7 < 2^64 by omega), Nat.mod_eq_of_lt (show 5 * jj + 8 < 2^64 by omega),
    Nat.mod_eq_of_lt (show 5 * jj + 9 < 2^64 by omega)]; omega))
  all_goals try (sep_mem hm; all_goals (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide))
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b02") ?_; refine ⟨isSome_at L.L6b02, ?_, ?_⟩; rw [T.L6b02])
  all_goals try dq_edge
  all_goals try dq_var
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨jj, hjj, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals (first
      | (rw [Mem.sub_base_add]; (obtain rfl | rfl : jj = 0 ∨ jj = 1 := (by omega)) <;> decide)
      | sep_close hm))
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrdx, hrsi, hrax, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrdx, hrsi, hrax]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm2 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm0), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm3 ≠ RegMm.mm2), RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm4 ≠ RegMm.mm2), hx0]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get_low32, Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264, dq_sw32128]; simp only [BitVec.toNat_setWidth,
        BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
        BitVec.toNat_ofInt, Nat.reduceMod, Nat.reducePow]; omega)
  all_goals try (simp only [RegZmms.get_set_xmm_same, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals try (simp only [RegZmms.get_set_xmm_same, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      dq_sw3264, dq_sw32128]; refine dq_shl1 _ ?_; simp only [BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]; omega)
