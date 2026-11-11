theorem blk_L6838 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6838" ⟨"ff_aac_sbr_apply.L6838", B.L6838, some "ff_aac_sbr_apply.L6838_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hst, hm⟩ := T.L6838.mp hs
  clear hs
  simp only [Mm, ApplyF, FrD, FrRaw] at hm
  have e1 : BitVec.setWidth 64 (BitVec.setWidth 32 1#64) = 1#64 := by decide
  simp only [B.L6838]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6838_1])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, hst, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, FrE, FrRaw, Args.push, e1] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done
