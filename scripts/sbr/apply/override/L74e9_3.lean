theorem blk_L74e9_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_3" ⟨"ff_aac_sbr_apply.L74e9_3", B.L74e9_3, some "ff_aac_sbr_apply.L74e9_4"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, h12, h13, h15, hax, y, hK, hCy, hm⟩ := T.L74e9_3.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9 h12 h13 hax
  simp only [B.L74e9_3]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      and_self, h9, h12, h13, h15, hax]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_4])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    h12, h13, h15, hax, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, lab,
    BitVec.sub_add_cancel]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS3, FrS4, FrL, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done
