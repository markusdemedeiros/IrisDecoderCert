theorem blk_L7682_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_3" ⟨"ff_aac_sbr_apply.L7682_3", B.L7682_3, some "ff_aac_sbr_apply.L7682_4"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h9, h14, hdx, hzf, y, hK, hCy, hm⟩ := T.L7682_3.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA3, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    dsimp only
    simp only [B.L7682_3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_4]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h14, hdx, hzf,
        sbrA, arg1, BitVec.add_assoc, decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true,
        Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64, CondCode.interp, Bool.not_false, Bool.not_true,
        BitVec.setWidth_eq, BitVec.zero_mul, BitVec.one_mul] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_mem hm
    all_goals try (simp only [Mm, ApplyF, FrA4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat]; sep_close hm)
    all_goals try var_step
  all_goals try (simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod]; exact Nat.le_refl _)
