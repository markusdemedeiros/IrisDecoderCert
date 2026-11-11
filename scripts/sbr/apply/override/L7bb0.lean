theorem blk_L7bb0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb0" ⟨"ff_aac_sbr_apply.L7bb0", B.L7bb0, some "ff_aac_sbr_apply.L7bb3"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, xx, gg, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, hdx, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hax, hgg, hm⟩ := T.L7bb0.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hzx := zx_ofNat gg (by omega)
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hax⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7bb0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, hdx, hax, hzx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hax⟩ := hR.down
  refine ⟨?_, ?_⟩
  · rw [T.L7bb3]
    refine ⟨_, c0, _, j, kk, gg, xx, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx, hkk, ?_,
      by omega, ?_⟩
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
        Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
        h15, h12, h14, hdx, hax]
      done
    simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
    sep_close hm
  · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
    rw [← hn]
    var_step
