theorem blk_L7b00 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b00" ⟨"ff_aac_sbr_apply.L7b00", B.L7b00, some "ff_aac_sbr_apply.L7b00_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hm⟩ := T.L7b00.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, DScW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hD : DWF True (y.d ch) := by
    rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
    · exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => hst
    · exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => ⟨hst, hK.2.live hst Nat.one_ne_zero⟩
  obtain ⟨-, -, -, -, hne8, -, -, -, -, -, -, -, -, -, -, hlv⟩ := hD
  have hne := (hlv trivial).1
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
      Nat.one_ne_zero] at hm hbx hne8 hne
    simp only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
    have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7b00]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      Int64.ofBitVec_toBitVec] at *
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (simp only [CondCode.interp_z, StatusFlags.zf_from_result, sext_n _ hne8, flag_ne _ hne8 hne,
      Bool.false_eq_true] at *; done)
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7b00_1]
        refine ⟨_, c0, _, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, rfl, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx]; done)
        simp only [Mm, ApplyF, FrH, DScW, c4, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
          BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, sext_n _ hne8]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        try simp only [sext_n _ hne8] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
