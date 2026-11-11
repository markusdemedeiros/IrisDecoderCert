theorem blk_L9a85_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_2" ⟨"ff_aac_sbr_apply.L9a85_2", B.L9a85_2, some "ff_aac_sbr_apply.L9a85_3"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, hbx, h15, h13, h12, h14, y, hK, hCy, v, hw1, hw2, hm⟩ := T.L9a85_2.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  have hW := PLift.up (⟨hw1, hw2⟩ : _ ∧ _); clear hw1 hw2
  have hR := PLift.up (⟨hrsp, hrbp, hbx, h15, h13, h12, h14⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [Mm] at hm
  rw [res_args k hSt] at hm
  simp only [ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [B.L9a85_2]
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
      hbx, h15, h13, h12, h14, Width.bytes, Width.bytesv, BitVec.add_assoc, arg0, arg1, sbrA] at *
  all_goals try simp only [hsp, hrs] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  case vc11 =>
    obtain ⟨hrsp, hrbp, hbx, h15, h13, h12, h14⟩ := hR.down
    refine ⟨?_, by var_step⟩
    rw [T.L9a85_3]
    refine ⟨ch, c0, hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_, ?_, ?_, ?_, ?_, ?_, v, hW.down.1, hW.down.2, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hbx, h15, h13, h12, h14,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, sbrA, arg0, arg1, arg3, arg4,
        BitVec.add_assoc, BitVec.reduceAdd, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]; done)
    simp only [MmS, SynArgs, c8, Mm, ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, dsN,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] at hm ⊢
    sep_close hm
  case vc2 =>
    obtain ⟨hrsp, hrbp, hbx, h15, h13, h12, h14⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9b24") ?_
    refine ⟨isSome_at L.L9b24, ?_, Or.inr ⟨?_, ?_⟩⟩
    rotate_left
    · simp only [lex_var] at hn ⊢; exact hn
    · simp only [lex_var]; decide
    rw [T.L9b24]
    refine ⟨ch, c0, hC, ⟨?_, ?_⟩, y.setV0 v, hK'.down, applyc_setV0 hCy'.down hW.down.1 hW.down.2, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hbx, h15, h13, h12, h14,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, sbrA, arg0, arg1, arg3, arg4,
        BitVec.add_assoc, BitVec.reduceAdd, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]; done)
    simp only [Mm]
    rw [res_args k hSt]
    simp only [MmS, SynArgs, c8, Mm, ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, dsN,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] at hm ⊢
    sep_close hm
