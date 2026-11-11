theorem blk_L7a28_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7a28_1" ⟨"ff_aac_sbr_apply.L7a28_1", B.L7a28_1, some "ff_aac_sbr_apply.L7a96"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, h5, hm⟩ := T.L7a28_1.mp hs
  clear hs
  have hd0 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 : y.d0.invf.length = 10 := hd0.2.1
  have hl1 : y.d1.invf.length = 10 := hd1.2.1
  have hb0 : u8 y.d0.invf 4 ≤ 3 := hd0.2.2.2.2.2.2.2.1 4 (by omega)
  have hb1 : u8 y.d1.invf 4 ≤ 3 := hd1.2.2.2.2.2.2.2.1 4 (by omega)
  have e0 : (y.d0.invf.take 9).getD 4 0 = y.d0.invf.getD 4 0 := take_getD' _ _ _ (by decide)
  have e1 : (y.d1.invf.take 9).getD 4 0 = y.d1.invf.getD 4 0 := take_getD' _ _ _ (by decide)
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [byte_split y.d0.invf _ 9 (by omega) (by omega), byte_split y.d1.invf _ 9 (by omega) (by omega),
    byte_split (y.d0.invf.take 9) _ 4 (by simp only [List.length_take, hl0]; omega)
      (by simp only [List.length_take, hl0]; omega),
    byte_split (y.d1.invf.take 9) _ 4 (by simp only [List.length_take, hl1]; omega)
      (by simp only [List.length_take, hl1]; omega), e0, e1] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR2 := PLift.up (⟨hl0, hl1, e0, e1⟩ : _ ∧ _ ∧ _ ∧ _)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7a28_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4, zx_byte,
        add_sub_self']
      first | exact bw_off8 _ hb0 | exact bw_off8 _ hb1
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4]
      first | exact bw_off _ _ hb0 | exact bw_off _ _ hb1
    case vc5 =>
      rename_i h1 h2 h3 h4
      exfalso
      simp only [sw8b, sw8_3, CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
        cf_sub8 _ 3 (UInt8.toNat_lt _) (by decide), zf_sub8 _ 3 (UInt8.toNat_lt _) (by decide),
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2 h3 h4
      try simp only [u8] at hb0 hb1
      omega
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7a96") ?_
      refine ⟨isSome_at L.L7a96, ?_, ?_⟩
      · rw [T.L7a96]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, h5, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 9 (by omega) (by omega), byte_split y.d1.invf _ 9 (by omega) (by omega),
          byte_split (y.d0.invf.take 9) _ 4 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 9) _ 4 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc7 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7a96]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, h5, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 9 (by omega) (by omega), byte_split y.d1.invf _ 9 (by omega) (by omega),
          byte_split (y.d0.invf.take 9) _ 4 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 9) _ 4 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step
