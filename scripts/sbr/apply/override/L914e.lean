theorem blk_L914e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L914e" ⟨"ff_aac_sbr_apply.L914e", B.L914e, some "ff_aac_sbr_apply.L914e_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hm⟩ := T.L914e.mp hs
  obtain ⟨hnl, hk1, hm1, hlg, hne, hne1, hfl, hlim, hlimm, hyp⟩ := ga_facts hCy hst ch (hK.2.live hst)
  simp only [Mm, ApplyF, TabW, FrX, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
  dsimp only
  simp only [B.L914e]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have l1 : some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 Reg64.rsi).toInt)) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsp - 64#64) 8 := by
    sep_mem hm; rfl
  have l2 : some (Int.ofBytes (Int.toBytes 4 (y.nlim : Int))) = loadInt s₀.dmem (t₀.regs.get64 Reg64.rsi + 477964#64) 4 := by
    sep_mem hm; rfl
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try (dq_revert_loads; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]); (try simp only [ga_fr, BitVec.reduceSub, BitVec.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd]); simp only [← l1, ← l2, Option.some.injEq]; intros; (try simp only [Option.some.injEq] at *); subst_vars)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [ga_c4 _ (show y.nlim < 2 ^ 32 by omega)]
  all_goals try (sep_mem hm; done)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ga_c4 _ (show y.nlim < 2 ^ 32 by omega),
    CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, dq_zf, BitVec.and_self,
    BitVec.toNat_ofNat, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Nat.reducePow] at *
  all_goals try (exfalso; omega)
  all_goals try (simp only [Nat.mod_eq_of_lt (show y.nlim < 2 ^ 64 by omega)] at *)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L98e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L98e0") ?_; refine ⟨isSome_at L.L98e0, ?_, ?_⟩; rw [T.L98e0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e_1])
  all_goals try edge_step
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]; simp (disch := omega) only [loadInt_storeInt_sub_lo, loadInt_storeInt_sub_hi])
  all_goals try (left; ga_var)
  all_goals try (right; constructor; ga_var; simp only [lex_var]; decide)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, (?_ : 1 ≤ _), ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, hrsp, hrbp]; done)
  all_goals try omega
  all_goals try ((try dsimp only); simp only [Mm, ApplyF, TabW, FrX, FrGA, FrGa1, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; (try sep_mem hm); all_goals sep_close hm)
