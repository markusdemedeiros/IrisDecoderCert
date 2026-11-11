theorem blk_L6a30 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6a30" ⟨"ff_aac_sbr_apply.L6a30", B.L6a30, some "ff_aac_sbr_apply.L6a30_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  have hm := (T.L6a30.mp hs).2.2.2.2
  have h9 := (T.L6a30.mp hs).2.2.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  clear h9
  dsimp only
  simp only [B.L6a30]
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64] at *
  all_goals obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ⟨ee, kk, he1, he2, hrbx, hr12, hr13, hra, hkk, hr14⟩, -⟩ := T.L6a30.mp hs
  all_goals obtain ⟨hne, hfr, hfl, hnn, hn0, hn1, hnq⟩ := dq_facts hC.1
  all_goals simp only [arg1] at h9
  all_goals simp only [arg1, ← h9] at hr12 hr13
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hu := hfr ee he2
  all_goals clear hee
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hE8 : ee ≤ 8 := by omega
  all_goals try sep_vals hm
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals have e14 := congrArg BitVec.toNat hr14
  all_goals simp only [dq_ofNat_toNat _ (show kk < 2 ^ 64 by omega)] at e14
  all_goals obtain hr0 | hr0 := dq_le1 _ hra
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1] at *
  all_goals try (dq_revert_loads; (try simp only [hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, dq_a_289ac, dq_a_15ac0_d, dq_a_15ac0_q, BitVec.add_zero, dq_add0, dq_fr30, dq_fr38, dq_n0, dq_n1]); sep_mem hm; all_goals (first | (intro hv; simp only [Option.some.injEq] at hv; subst hv) | (simp only [hrbx, Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega) | (simp only [hfl, Nat.reducePow]; omega) | (rw [Mem.sub_base_add_add]; simp only [hrbx, hr14, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega) | skip))
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero, Reg64s.get_low8, Reg64s.get_low32,
    hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]
  all_goals try simp only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl] at *
  all_goals clear hee hfl
  all_goals have hee : ee % 2 ^ 64 = ee := Nat.mod_eq_of_lt (by omega)
  all_goals have hfl := (dq_facts hC.1).2.2.1
  all_goals try simp only [dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast] at *
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
    Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.add_zero,
    CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c,
    CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not, dq_subz, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false,
    BitVec.toNat_add, dq_one64, BitVec.toNat_ofNat, Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (rw [Mem.sub_base_add]; simp only [BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (rw [hfl]; omega)
  all_goals try (simp only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, hfl, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]; omega)
  all_goals try sep_mem hm
  all_goals try (rw [Mem.sub_base_add_add]; simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals try (rw [Mem.sub_base_add]; simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod]; omega)
  all_goals try (simp only [Mem.sub_base_add, BitVec.toNat_ofNat, hee, hfl]; omega)
  all_goals try (simp only [hfl, Nat.reducePow]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega), BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega)
  all_goals try simp only [BitVec.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ee < 2^64 by omega)]
  all_goals try simp only [BitVec.setWidth_replaceLow8, BitVec.toNat_replaceLow8_mod, Reg64s.get_low8, Reg64s.get_low32, dq_sw32, dq_sw3264, dq_b64, dq_b32]
  all_goals try simp only [Nat.reduceMod, Nat.reducePow]
  all_goals try split
  all_goals try (simp only [not_false_eq_true]; done)
  all_goals try (exfalso; omega)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L68d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L68d0") ?_; refine ⟨isSome_at L.L68d0, ?_, ?_⟩; rw [T.L68d0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6a30_1])
  all_goals try dq_var
  all_goals try (left; dq_var)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ⟨ee, kk, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try omega
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, DArrW, TabW, CstW, dA, sbrA, arg1, dq_aal,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; (try sep_mem hm); all_goals sep_close hm)
  all_goals try (simp only [BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0, h9, arg1]; done)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, dq_one64, hrsp, hrbp, hrbx, hr12, hr13, hr14, hr0]; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_b64, dq_b32, dq_7, dq_sw32, dq_sw3264]; done)
  all_goals try (simp only [BitVec.isLt]; done)
  all_goals try (simp only [BitVec.toNat_ofInt]; omega)
  all_goals try (simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_setWidth, BitVec.toNat_zero,
      Nat.zero_mod, Nat.zero_le]; done)
  all_goals have hnv : (Int.ofBytes (Int.toBytes 4 (x.d0.nenv : Int)) % ((4294967296 : Nat) : Int)).toNat = x.d0.nenv := dq_ofb4 _ (by omega)
  all_goals have hn0v : (Int.ofBytes (Int.toBytes 4 (x.n0 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n0 := dq_ofb4 _ (by omega)
  all_goals have hn1v : (Int.ofBytes (Int.toBytes 4 (x.n1 : Int)) % ((4294967296 : Nat) : Int)).toNat = x.n1 := dq_ofb4 _ (by omega)
  all_goals try simp only [ebx, hnv, hn0v, hn1v] at *
  all_goals have ebx := congrArg BitVec.toNat hrbx
  all_goals simp only [dq_ofNat_toNat _ (show ee < 2 ^ 64 by omega)] at ebx
  all_goals try (exfalso; omega)
  all_goals try (exfalso; simp only [ebx, dq_u8 _ _ (show ee < x.d0.freqRes.length by omega)] at *; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reducePow]; omega)
  all_goals try (apply BitVec.eq_of_toNat_eq; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, h9, arg1]; ac_rfl)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofNat_add]; done)
  all_goals try omega
