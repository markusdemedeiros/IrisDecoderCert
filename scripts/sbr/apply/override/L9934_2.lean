theorem blk_L9934_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9934_2" ⟨"ff_aac_sbr_apply.L9934_2", B.L9934_2, some "ff_aac_sbr_apply.L99c6"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, hr12, hr14, hbl, y, hK, hCy, hm⟩ := T.L9934_2.mp hs
  clear hs
  have hbl2 : (s₀.regs.get64 Reg64.rbx).toNat % 256 < 2 := by rw [hbl]; split <;> decide
  have ga_arg : ∀ (c : BitVec 8) (r : BitVec 64), r.toNat % 256 = (if BitVec.setWidth 32 (arg2 t₀) = 1#32 then 1 else 0) →
      (!(c &&& BitVec.setWidth 8 r == BitVec.zero 8)) = true → BitVec.setWidth 32 (arg2 t₀) = 1#32 := by
    intro c r h hx
    by_cases hP : BitVec.setWidth 32 (arg2 t₀) = 1#32
    · exact hP
    rw [if_neg hP] at h
    have h0 : BitVec.setWidth 8 r = 0#8 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      omega
    rw [h0, show BitVec.zero 8 = 0#8 from rfl, BitVec.and_zero] at hx
    simp at hx
  have hyp := gq_yp hCy ch
  obtain ⟨chv, hchv1, hchv2⟩ : ∃ v, ch ≤ v ∧ v ≤ ch := ⟨ch, Nat.le_refl _, Nat.le_refl _⟩
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    all_goals try simp only [Args.d, reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, if_true, if_false] at hne hne1 hyp he ⊢
    simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try dsimp only
    simp only [B.L9934_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have ga_byte0 : ∀ c0 : BitVec 32, BitVec.ofInt 8 (Int.ofBytes (List.take 1 (Int.toBytes 4 c0.toInt))) = c0.setWidth 8 := by
      intro c0
      rw [← BitVec.ofInt_ofBytes_take 8 1 rfl]
      have h := congrArg (BitVec.setWidth 8) (BitVec.ofInt_ofBytes_toBytes 32 4 rfl c0)
      rw [← h]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
      omega
    have ga_test0 : ∀ (c0 : BitVec 32) (r : BitVec 64), c0.getLsbD 0 = false → r.toNat % 256 < 2 →
        (BitVec.ofInt 8 (Int.ofBytes (List.take 1 (List.drop 0 (Int.toBytes 4 c0.toInt)))) &&& BitVec.setWidth 8 r
          == BitVec.zero 8) = true := by
      intro c0 r h0 hr
      rw [List.drop_zero, ga_byte0]
      simp only [beq_iff_eq]
      have hc : c0.toNat % 2 = 0 := by
        simp only [BitVec.getLsbD, Nat.testBit_zero, decide_eq_false_iff_not] at h0
        omega
      rw [show BitVec.zero 8 = 0#8 from rfl]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod]
      rcases (by omega : r.toNat % 2 ^ 8 = 0 ∨ r.toNat % 2 ^ 8 = 1) with h | h <;> rw [h]
      · simp
      · rw [Nat.and_one_is_mod]; omega
    all_goals vcgen
    all_goals try subst s₀
    all_goals try (ga_revert_conds; (try simp (disch := rfl) only [CondCode.interp_a_sub, CondCode.interp_be_sub, CondCode.interp_nc_sub64, CondCode.interp_nc_sub8]); (try simp only [CondCode.interp_z, CondCode.interp_nz, CondCode.interp_c, CondCode.interp_nc, CondCode.interp_a, CondCode.interp_be, StatusFlags.zf_from_result, StatusFlags.cf_from_result, dq_cf32, dq_cf64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceSub]); intros)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]
    all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); skip; skip; sep_mem hm; intros; (try simp only [Option.some.injEq] at *); subst_vars)
    all_goals try (simp (disch := decide) only [ga_off]; decide)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff, reduceIte, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, dA, sbrA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, hr12, hr14]
    all_goals try (sep_mem hm; done)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (sep_mem hm; all_goals (simp (disch := decide) only [ga_off]; decide))
    all_goals try (exfalso; have hx := ‹(!(_ &&& _ == BitVec.zero 8)) = true›; simp only [BitVec.sub_self, BitVec.toNat_zero, ga_test0 c0 _ (by simpa using hc0) hbl2, Bool.not_true, Bool.false_eq_true] at hx)
    all_goals try (sep_mem hm <;> simp [Int.toBytes_length]; done)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L7682"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7682") ?_; refine ⟨isSome_at L.L7682, ?_, ?_⟩; rw [T.L7682]; first | (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩) | (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩))
    all_goals try (goal_has_str "ff_aac_sbr_apply.L9a02"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a02") ?_; refine ⟨isSome_at L.L9a02, ?_, ?_⟩; rw [T.L9a02]; first | (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩) | (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩))
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L99c6])
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hr14] at hn ⊢); subst n; first | (left; ga_var; done) | (right; constructor; ga_var; decide))
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
    all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd])
    all_goals try (gq_le_lex; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hr14] at hn ⊢); (try subst n); first | (apply Nat.le_of_lt; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega) | exact Nat.le_refl _)
    all_goals try (dq_guard_or; clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd, hr12, hr14] at hn ⊢); (try subst n); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try simp only [u16, u8] at *); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); have h2 := gq_two; have h2' := gq_two'; omega)
    all_goals try (simp (disch := decide) only [Mem.loadInt_storeInt, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.xor_self, BitVec.reduceSetWidth, BitVec.toNat_zero, Nat.sub_zero])
    all_goals try simp only [hr12, BitVec.ofInt_toInt]
    all_goals try exact Nat.le_refl _
    all_goals try (dq_guard_or; left; ga_var)
    all_goals try (dq_guard_or; right; constructor; ga_var; simp only [lex_var]; decide)
    all_goals try (dq_guard_or; right; exact ⟨trivial, by decide⟩)
    all_goals try (clear hm; (try simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢); subst n; ga_var; done)
    all_goals try (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩)
    all_goals try (refine ⟨1, hC, ⟨?_, ?_⟩, (by decide), ?_, ?_, ?_, ?_, y, ⟨hK.1, ChLive.one hK.2.1 (ga_arg _ _ hbl ‹_›)⟩, hCy, ?_⟩)
    all_goals try (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩)
    all_goals try (refine ⟨chv, c0, hC, ⟨?_, ?_⟩, ?_, ?_, y, hK.1, hCy, ?_⟩)
    all_goals try (simp only [Args.d] at hne1 he ⊢; omega)
    all_goals try exact hnl1
    all_goals try (obtain rfl := Nat.le_antisymm hchv2 hchv1)
    all_goals try (sep_mem hm; (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 64 8 rfl, BitVec.ofInt_toInt, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub, BitVec.ofNat_eq_ofNat, BitVec.reduceToNat]); left; (repeat (refine Kraken.lex_cons_lt_cons (by rfl) ?_)); refine Kraken.lex_cons_lt_of_lt (by rfl) ?_; omega)
    all_goals try ((try dsimp only); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr14, hr12, arg1, sbrA]); first | rfl | (simp only [BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceGetLsbD, BitVec.getLsbD_zero, BitVec.reduceOfNat]; done) | (simp; done))
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr12, hr14, arg1, sbrA, dA, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; done)
    all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrCs, FrL, DScW, DArrW, dA, sbrA, arg1, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
