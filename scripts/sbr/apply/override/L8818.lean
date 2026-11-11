theorem blk_L8818 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L8818" ⟨"ff_aac_sbr_apply.L8818", B.L8818, some "ff_aac_sbr_apply.L881c"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hr8, hrax, hm⟩ := T.L8818.mp hs
  clear hs
  simp only [Mm, FrO8] at hm
  dsimp only
  simp only [B.L8818]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try dsimp only
  all_goals try sep_mem hm
  case vc2 =>
    rename_i v hv
    simp only [hrbp, AddrIndex.offset64_none, z, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod] at hv
    simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hv
    revert hv; sep_mem hm; intro hv; simp only [Option.some.injEq] at hv; subst hv
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
    refine ⟨?_, ?_⟩
    · rw [T.L881c]
      refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, ?_, ?_, ?_, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrbx, hr8, hrax]; done)
      simp only [Mm, FrO]; sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      exact Nat.le_refl _
