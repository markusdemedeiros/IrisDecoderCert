theorem blk_L9600 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9600" ⟨"ff_aac_sbr_apply.L9600", B.L9600, some "ff_aac_sbr_apply.L9617"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, hm⟩ := T.L9600.mp hs
  clear hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9600]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have l0 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
      sep_mem hm; rfl
    have l1 : some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 kk).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 88#64) 8 := by
      sep_mem hm; rfl
    have l2 : some (((u16 y.ftLim (kk) : Nat) : Int)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + (BitVec.ofNat 64 (kk) * 2#64 + 478226#64)) 2 := by
      sep_mem hm
      all_goals simp only [gq_off2 _ _ _ (show 2 * (kk) < 2 ^ 64 by omega), hfl]
      all_goals first | omega | exact gq_u16 _ _ (by omega)
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    vcgen
    all_goals try subst s₀
    all_goals try (rename_i hx1 hx2 hx3; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2 hx3); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2 hx3)
    all_goals try (rename_i hx1 hx2; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1 hx2); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1 hx2)
    all_goals try (rename_i hx1; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8] at hx1); simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub] at hx1)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l0, ← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9617"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9617") ?_; refine ⟨isSome_at L.L9617, ?_, ?_⟩; rw [T.L9617])
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L9617])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [gq_sub16 y.ftLim (kk) y.kx1 (by (try simp only [u16, u8]); omega) (by (try simp only [u16, u8]); omega)])
    all_goals try (intro; (try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [gq_z16 y.ftLim (kk) (by (try simp only [u16, u8]); omega)])
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); rw [gq_z16 y.ftLim (kk) (by (try simp only [u16, u8]); omega)])
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hlt, hrbx, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
