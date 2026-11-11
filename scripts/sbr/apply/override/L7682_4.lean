theorem blk_L7682_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_4" ⟨"ff_aac_sbr_apply.L7682_4", B.L7682_4, some "ff_aac_sbr_apply.L7682_5"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h9, h14, h13, y, hK, hCy, hm⟩ := T.L7682_4.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
  simp only [lex_var, hsl] at hn
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    dsimp only
    simp only [B.L7682_4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_5]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h14, h13, dA, ↓reduceIte,
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
    all_goals try (simp only [Mm, ApplyF, FrA5, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢)
    all_goals try sep_close hm
    all_goals try (rw [← BitVec.add_assoc, BitVec.add_comm (9344#64), BitVec.add_assoc]; simp only [BitVec.reduceAdd]; done)
    all_goals try var_step
  all_goals try (simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod]; exact Nat.le_refl _)
