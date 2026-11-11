theorem blk_L7750_8 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_8" ⟨"ff_aac_sbr_apply.L7750_8", B.L7750_8, some "ff_aac_sbr_apply.L7866"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, y, hK, hCy, hst, hm⟩ := T.L7750_8.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  · have hD := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨-, hlen, -, -, -, -, -, hinv3, -⟩ := hD
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hl⟩ := list10 _ hlen
    have hb0 : b0.toNat ≤ 3 := by simpa [u8, hl] using hinv3 0 (by omega)
    have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
    rw [hl, split10] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have hv0 : (BitVec.ofInt 8 (Int.ofBytes [b0])).toNat ≤ 3 := by rw [byte_toNat]; exact hb0
    simp only [dA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
      Nat.one_ne_zero] at hm
    simp only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
    have hR := PLift.up (⟨hrsp, hrbp, hsl, hn⟩ : _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_8]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      Int64.ofBitVec_toBitVec] at *
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (simp only [CondCode.interp_nc, StatusFlags.cf_from_result, cf_lt4 _ hv0, Bool.not_true,
      Bool.false_eq_true] at *; done)
    all_goals try exact bw_off _ _ hb0
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc8 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7866") ?_
      refine ⟨isSome_at L.L7866, ?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc11 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
  · have hD := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨-, hlen, -, -, -, -, -, hinv3, -⟩ := hD
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hl⟩ := list10 _ hlen
    have hb0 : b0.toNat ≤ 3 := by simpa [u8, hl] using hinv3 0 (by omega)
    have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
    rw [hl, split10] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have hv0 : (BitVec.ofInt 8 (Int.ofBytes [b0])).toNat ≤ 3 := by rw [byte_toNat]; exact hb0
    simp only [dA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
      Nat.one_ne_zero] at hm
    simp only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
    have hR := PLift.up (⟨hrsp, hrbp, hsl, hn⟩ : _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_8]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      Int64.ofBitVec_toBitVec] at *
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (simp only [CondCode.interp_nc, StatusFlags.cf_from_result, cf_lt4 _ hv0, Bool.not_true,
      Bool.false_eq_true] at *; done)
    all_goals try exact bw_off _ _ hb0
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc8 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7866") ?_
      refine ⟨isSome_at L.L7866, ?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc11 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
