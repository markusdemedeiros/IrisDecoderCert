theorem blk_L95a0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L95a0_1" ⟨"ff_aac_sbr_apply.L95a0_1", B.L95a0_1, some "ff_aac_sbr_apply.L95a0_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hlt, hml, hmh, hr14, hrax, hrsi, hm⟩ := T.L95a0_1.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L95a0_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hLk := hlim kk (by omega)
    have hLk1 := hlim (kk + 1) (by omega)
    revert hn
    simp only [lex_var, slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
    intro hn
    vcgen
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]
    all_goals try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow])
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]); (try simp only [ga_fr, ga_add0, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); (try simp (disch := decide) only [ga_foldn, ga_fold1n]); (try simp only [Nat.reduceAdd, Nat.reduceMod, Nat.reducePow]); sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try simp only [BitVec.add_zero, BitVec.zero_add]
    all_goals try simp (disch := omega) only [ga_lea192, ga_lea192c]
    all_goals try (goal_has_str "ff_aac_sbr_apply.L95a0_2"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L95a0_2") ?_; refine ⟨isSome_at L.L95a0_2, ?_, ?_⟩; rw [T.L95a0_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L95a0_2]; (try (first | refine ⟨hC, ⟨?_, ?_⟩, y, 0, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ | refine ⟨hC, ⟨?_, ?_⟩, y, 1, c0, ee, kk, mm, hK, hCy, hc0, hst, hch, he, hnl1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)))
    all_goals try (dq_guard_or; edge_step)
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (ga_is_lex; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]); sep_mem hm; simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; (try simp (disch := omega) only [ga_inc]); (try simp only [hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi, BitVec.toNat_zero, Nat.sub_zero, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]))
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
    all_goals try (simp only [u16, u8]; omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]); first | (rw [ga_inc _ (by omega)]) | (simp only [dq_sw3264]; rw [ga_sub32b _ _ (by omega) (by omega)]))
    all_goals try (simp only [hrax, BitVec.toNat_ofNat]; simp (disch := omega) only [Nat.mod_eq_of_lt]; ga_var)
    all_goals try ((try dsimp only); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_add8])
    all_goals try simp only [dq_sw3264]
    all_goals try simp (disch := omega) only [ga_sx, ga_mz, ga_sub32c, ga_sub32b, ga_sub32d, ga_zx32, ga_sx32, ga_zx16, ga_and7w, ga_inc, ga_dec]
    all_goals try ((try simp only [BitVec.toNat_ofNat]); split <;> first | rfl | (exfalso; omega))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrdx, hrcx, hr10, hr11, hr9, hr8, hrdi, hr12, hr13, hr14, hrax, hrsi, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGb, DScW, DArrW, ArrW, Blocks, CstW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
    all_goals try (simp only [dq_sw3264]; done)
