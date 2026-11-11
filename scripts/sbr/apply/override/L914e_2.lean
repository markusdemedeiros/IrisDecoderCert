theorem blk_L914e_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L914e_2" ⟨"ff_aac_sbr_apply.L914e_2", B.L914e_2, some "ff_aac_sbr_apply.L914e_3"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hnl1, hr10, hrcx, hm⟩ := T.L914e_2.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa2, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
  dsimp only
  simp only [B.L914e_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l1 : some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 (88768 * ch)).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 160#64) 8 := by
    sep_mem hm; rfl
  have l2 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi + 252416#64).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 360#64) 8 := by
    sep_mem hm; rfl
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr10, hrcx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_c4 _ (show y.kx1 < 2 ^ 32 by omega)]
  all_goals try (sep_mem hm; done)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_c4 _ (show y.kx1 < 2 ^ 32 by omega),
    CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, dq_zf, BitVec.and_self,
    BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show y.nlim < 2 ^ 64 by omega)] at *)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try simp only [dq_sw32, dq_sw3264]
  all_goals try simp only [ga_s98_0]
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e_3])
  all_goals try edge_step
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [ga_ld_st])
  all_goals try (left; ga_var)
  all_goals try (right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, hnl1, ?_, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp, hr10, hrcx, arg1]; done)
  all_goals ((try dsimp only); simp only [Mm, ApplyF, TabW, ScW, FrX, FrGa2, FrGe0, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
