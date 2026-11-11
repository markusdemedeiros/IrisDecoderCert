theorem blk_L929e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L929e" ⟨"ff_aac_sbr_apply.L929e", B.L929e, some "ff_aac_sbr_apply.L929e_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, hm⟩ := T.L929e.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGk, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L929e]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    vcgen
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L929e_1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L929e_1") ?_; refine ⟨isSome_at L.L929e_1, ?_, ?_⟩; rw [T.L929e_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L929e_1]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try var_step
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (goal_has_str "ff_aac_sbr_apply.L99fd"; exfalso; (try simp only [u16, u8] at *); (try simp only [hrdx, CondCode.interp_z, CondCode.interp_nz, CondCode.interp_a, CondCode.interp_be, CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result, StatusFlags.zf_from_result, StatusFlags.from_result.Remaining.cf_mk, dq_cf8, dq_cf32, dq_cf64, dq_zf, BitVec.and_self, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *); (try simp (disch := omega) only [ga_subz, ga_c4, BitVec.ofNat_eq_ofNat] at *); (try simp only [Bool.and_eq_false_iff, Bool.not_eq_false', BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceMod, decide_eq_true_eq] at *); omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); first | (rw [ga_inc _ (by omega)]) | (simp only [dq_sw3264]; rw [ga_sub32b _ _ (by omega) (by omega)]))
    all_goals try (simp only [hrdx, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; ga_var)
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr12, hrdx, hrsi, hrcx, hr10, hr11, hr9, hr8, hrdi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, FrGk, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
