theorem blk_L9934 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9934" ⟨"ff_aac_sbr_apply.L9934", B.L9934, some "ff_aac_sbr_apply.L9934_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, hr12, y, hK, hCy, hrax, hm⟩ := T.L9934.mp hs
  clear hs
  have dqs_sete1 : ∀ r d : BitVec 64, (r.replaceLow (BitVec.ofNat 8 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (BitVec.setWidth 32 d).toInt)) - 1#32 == BitVec.zero 32).toNat)).toNat % 256 = if BitVec.setWidth 32 d = 1#32 then 1 else 0 := by
    intro r d
    rw [BitVec.toNat_replaceLow8_mod, BitVec.toNat_ofNat, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    generalize BitVec.setWidth 32 d = a
    by_cases h1 : a = 1#32
    · subst h1; decide
    · rw [if_neg h1, show (a - 1#32 == BitVec.zero 32) = false from by simp only [beq_eq_false_iff_ne, ne_eq]; intro h2; apply h1; have h3 := congrArg (· + 1#32) h2; simp only [BitVec.sub_add_cancel, BitVec.zero_eq, BitVec.zero_add] at h3; exact h3]; rfl
  have hyp := gq_yp hCy ch
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9934]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    all_goals vcgen
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrax]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9934_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9934_1") ?_; refine ⟨isSome_at L.L9934_1, ?_, ?_⟩; rw [T.L9934_1])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9934_1])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hrax] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hrax] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hrax] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sbrA, arg1, dA, BitVec.reduceMul, BitVec.reduceAdd, BitVec.zero_add, BitVec.add_zero, BitVec.reduceOfNat]; first | (with_reducible rfl) | ac_rfl)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr12]); (try simp (disch := omega) only [ga_inc, gq_add2]); apply BitVec.eq_of_toNat_eq; clear hm; (try simp only [u16, u8] at *); (try simp (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (clear hm; (try simp only [u16, u8] at *); (try simp (disch := omega) only [gq_nz, dq_cf32, dq_cf64, dq_zf, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, AddrIndex.offset64_scale4, Nat.mod_eq_of_lt, BitVec.toNat_and, Nat.and_one_is_mod, Bool.not_eq_true', Bool.not_eq_false', Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not, Nat.reducePow] at *); omega)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr12, hrax, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (exfalso; rename_i hcc; simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Nat.not_lt, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.reduceToNat, BitVec.reduceSetWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, ite_true, ite_false, Nat.one_ne_zero, reduceIte] at hcc hrax; omega)
    all_goals try (dsimp only; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false])
    all_goals try (simp only [sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, BitVec.zero_mul, BitVec.one_mul, BitVec.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try (rw [BitVec.add_comm (31024#64)]; simp only [dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try (simp only [Args.d, ite_true, ite_false, Nat.one_ne_zero, reduceIte] at hrax ⊢; exact hrax)
    all_goals try (apply BitVec.eq_of_toNat_eq; simp only [Args.d, ite_true, ite_false, Nat.one_ne_zero, reduceIte, BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod] at hrax ⊢; omega)
    all_goals try (with_reducible exact dqs_sete1 _ (t₀.regs.get64 .rdx))
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); simp only [BitVec.toNat_replaceLow8_mod, BitVec.toNat_ofNat]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.lt_succ_of_le (Bool.toNat_le _)))
