theorem blk_L96d3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L96d3" ⟨"ff_aac_sbr_apply.L96d3", B.L96d3, some "ff_aac_sbr_apply.L96e1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hlt, hrax, hrbx, hr12, hr13, hrsi, hm⟩ := T.L96d3.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne1
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hyp
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at he
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L96d3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    all_goals vcgen
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L97b7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L97b7") ?_; refine ⟨isSome_at L.L97b7, ?_, ?_⟩; rw [T.L97b7])
    all_goals try (goal_has_str "ff_aac_sbr_apply.L96e1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L96e1") ?_; refine ⟨isSome_at L.L96e1, ?_, ?_⟩; rw [T.L96e1])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L96e1])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega)) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; first | omega | (simp only [BitVec.reduceToNat]; omega) | (rw [BitVec.toNat_ofNat]; simp only [Nat.reduceMod, Nat.reducePow]; omega) | (erw [gq_two]; omega) | (simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.reduceAdd] at *; omega))
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, ((u16 y.ftLim kk - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim kk - y.kx1)) % 2), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, ((u16 y.ftLim kk - y.kx1) + ((u16 y.ftLim (kk + 1) - y.kx1) - (u16 y.ftLim kk - y.kx1)) % 2), hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (gq_natg; clear hm; (try simp only [u16, u8] at hLk hLk1 hlt ⊢); omega)
    all_goals try (gq_natg; clear hm; have h1 := gq_ne1 _ _ (by assumption) (by omega) (by omega); (try simp only [u16, u8] at hLk hLk1 hlt ⊢); omega)
    all_goals try (gq_nomm; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hrax, hrbx, hr12, hr13, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try simp only [MachineData.dmem_mk, MachineData.regs_mk]); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
