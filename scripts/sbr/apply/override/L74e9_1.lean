theorem blk_L74e9_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_1" ⟨"ff_aac_sbr_apply.L74e9_1", B.L74e9_1, some "ff_aac_sbr_apply.L74e9_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp, h14⟩, h9, hax, y, hK, hCy, hm⟩ := T.L74e9_1.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  simp only [B.L74e9_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hds : (0#64).replaceLow (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (((if x.extRate.toInt < x.sampleRate.toInt then 1 else 0 : Nat)) : Int)))))
      = BitVec.ofNat 64 (if x.extRate.toInt < x.sampleRate.toInt then 1 else 0) := by
    split <;> decide
  vcgen
  all_goals try subst_vars
  all_goals try (rename_i v hv; simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
    Width.bytes, hrbp, z, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv)
  all_goals try (simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at hv)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14,
      and_self, h9, hax]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9, h14, z]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, hds]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_2])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    hax, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS1, FrS2, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done
