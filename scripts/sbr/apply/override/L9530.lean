theorem blk_L9530 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9530" ⟨"ff_aac_sbr_apply.L9530", B.L9530, some "ff_aac_sbr_apply.L9530_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, hm⟩ := T.L9530.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9530]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have l1 : some (Int.ofBytes (Int.toBytes 4 (↑y.limGains : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 166224#64) 4 := by
      sep_mem hm; rfl
    have lg : (loadInt s₀.dmem (lab "limgain" + BitVec.ofNat 64 y.limGains * 4#64) 4).isSome = true := by
      simp only [lab]
      rcases (by omega : y.limGains = 0 ∨ y.limGains = 1 ∨ y.limGains = 2 ∨ y.limGains = 3) with h | h | h | h <;> simp only [h, BitVec.ofNat_eq_ofNat, BitVec.reduceMul, BitVec.add_zero] <;> sep_mem hm <;> (simp only [lab, ga_subL, ga_offL, BitVec.toNat_ofNat]; omega)
    simp only [lab] at lg
    obtain ⟨vlg, hvlg⟩ := Option.isSome_iff_exists.mp lg
    try simp only [lab] at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try simp (disch := omega) only [ga_c4]
    all_goals try (dq_revert_loads; simp (disch := omega) only [ga_c4]; intros)
    all_goals try (dq_revert_loads; simp only [hvlg, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); simp only [← l0, ← l1, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp (disch := omega) only [ga_c4]
    all_goals try (simp (disch := omega) only [ga_c4, lg]; done)
    all_goals try (simp only [lg]; done)
    all_goals try (ga_revert_conds; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, ga_add8, hr12, hr13, hrcx, hrdx, hrsi, dq_sw3264]); (try simp (disch := omega) only [ga_mz, ga_mz32, ga_sub32b, ga_sub32d, ga_sub32e, ga_sub32c, ga_sub32n, dq_sw32, ga_zx32, ga_sx32, ga_c4, ga_dec]); (try simp only [ga_and7, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow, Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, Nat.reduceMod]); intros)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try simp (disch := omega) only [ga_c4]
    all_goals try (simp (disch := omega) only [ga_c4, lg]; done)
    all_goals try (simp only [lg]; done)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9617"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9617") ?_; refine ⟨isSome_at L.L9617, ?_, ?_⟩; rw [T.L9617]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9530_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9530_1") ?_; refine ⟨isSome_at L.L9530_1, ?_, ?_⟩; rw [T.L9530_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9530_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
    all_goals try (ga_is_lex; first | done | exact Nat.le_refl _ | ga_var | (dq_guard_or; left; ga_var) | (dq_guard_or; right; exact ⟨rfl, by decide⟩) | (dq_guard_or; right; exact ⟨trivial, by decide⟩) | (simp (disch := omega) only [Nat.mod_eq_of_lt]; apply Nat.le_of_eq; congr 1; simp only [List.cons.injEq, and_true, true_and]; omega))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9b72"; exfalso; (try simp only [u16, u8] at *); (try simp only [hr12, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9b81"; exfalso; (try simp only [u16, u8] at *); (try simp only [hr12, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (intro; exfalso; simp only [u16, u8] at *; omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)
