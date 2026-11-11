theorem blk_L7bb3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb3" ⟨"ff_aac_sbr_apply.L7bb3", B.L7bb3, some "ff_aac_sbr_apply.L7bb3_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hax, hg, hm⟩ := T.L7bb3.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13, hax⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hP : u8 y.pstart j + u8 y.pnum j ≤ 32 := hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  have hle := le_test6 g (by omega)
  have hadd := add32 xx (u8 y.pstart j) (by omega)
  have hzP := zx_ofNat (u8 y.pstart j + xx) (by omega)
  have hshP := shl320 (u8 y.pstart j + xx) (by omega)
  have hshK := shl320 kk (by omega)
  have hfix : ∀ r a X : BitVec 64, 16#64 + (r + (a + X)) = r + (a + (X + 16#64)) := by
    intro r a X; rw [BitVec.add_comm 16#64, BitVec.add_assoc, BitVec.add_assoc]
  dsimp only
  simp only [B.L7bb3]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, h13, hax,
      BitVec.add_assoc, BitVec.setWidth_eq, AddrIndex.offset64_scale4, BitVec.toNat_ofNat, Nat.reduceEqDiff, ↓reduceIte,
      hle, hadd, hzP, hshP, hshK, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc1 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13, hax⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7c80") ?_
    refine ⟨isSome_at L.L7c80, ?_, ?_⟩
    · rw [T.L7c80]
      refine ⟨_, c0, _, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, hst, hne, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13, hax⟩ := hR.down
    rename_i hg0 _ _
    have hdec := dec32 g (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [T.L7bb3_1]
      refine ⟨_, c0, _, j, kk, g - 1, xx, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx,
        hkk, by omega, ?_, ?_, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, h13, hax, hdec, hfix]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
