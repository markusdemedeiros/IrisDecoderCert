theorem blk_L9a85 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85" ⟨"ff_aac_sbr_apply.L9a85", B.L9a85, some "ff_aac_sbr_apply.L9a85_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, h9, hbx, h12, h14, y, hK, hCy, hm⟩ := T.L9a85.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  have hR := PLift.up (⟨hrsp, hrbp, h9, hbx, h12, h14⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [Mm] at hm
  rw [res_args k hSt] at hm
  simp only [ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [B.L9a85]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hsp : ∀ a : BitVec 64, BitVec.setWidth 64 32#64 + (a - 488#64) = a - 456#64 := by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrs : ∀ a : BitVec 64, BitVec.setWidth 64 269664#64 + a = a + 269664#64 := by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]
  vcgen
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      h9, hbx, h12, h14, Width.bytes, Width.bytesv, BitVec.add_assoc, arg0, arg1, sbrA] at *
  all_goals try simp only [hsp, hrs] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  all_goals (
    obtain ⟨hrsp, hrbp, h9, hbx, h12, h14⟩ := hR.down
    refine ⟨?_, by var_step⟩
    rw [T.L9a85_1]
    refine ⟨ch, c0, hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, hbx, h12, h14,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, sbrA, arg0, arg1, arg3, arg4,
        BitVec.add_assoc, BitVec.reduceAdd, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]; done)
    simp only [MmS, SynArgs, c8, Mm, ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, dsN,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] at hm ⊢
    sep_close hm)
