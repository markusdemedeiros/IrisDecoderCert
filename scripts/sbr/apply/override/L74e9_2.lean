theorem blk_L74e9_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_2" ⟨"ff_aac_sbr_apply.L74e9_2", B.L74e9_2, some "ff_aac_sbr_apply.L74e9_3"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hax, h12, h13, y, hK, hCy, hm⟩ := T.L74e9_2.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9 h12 h13
  simp only [B.L74e9_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hr15 : ∀ a c : BitVec 64, a + BitVec.setWidth 64 (c - a) = c := by
    intro a c; rw [BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have ez : BitVec.setWidth 64 0#32 = 0#64 := by decide
  have hlsb : ∀ v : BitVec 64, (v.replaceLow (BitVec.setWidth 8 1#64)).getLsbD 0 = true := by
    intro v
    have h := congrArg (fun u : BitVec 8 => u.getLsbD 0) (BitVec.setWidth_replaceLow8 v (BitVec.setWidth 8 1#64))
    simp only [BitVec.getLsbD_setWidth] at h
    simpa using h
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      and_self, h9, hax, h12, h13]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_3])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    hax, h12, h13, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, lab,
    Int64.toBitVec_sub, hr15]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self,
    BitVec.setWidth_eq, ez, BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hlsb, decide_true]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS2, FrS3, FrL, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done
