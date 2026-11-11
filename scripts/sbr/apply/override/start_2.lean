theorem blk_start_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.start_2" ⟨"ff_aac_sbr_apply.start_2", B.start_2, some "ff_aac_sbr_apply.start_3"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ⟨h0, h1, h2, h3, h4⟩, hm⟩ := T.start_2.mp hs
  clear hs
  -- open the groups the block reads
  simp only [Mm, ApplyF, ScW, AcW, FrA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h0 h1 h2 h3 h4
  dsimp only
  have hq0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.start
  have hq1 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.ready
  have hq2 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.pushed
  have e0 : BitVec.setWidth 32 0#64 = 0#32 := by decide
  simp only [B.start_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hzf : (x.pushed == 0#32) = decide (x.pushed = 0#32) := rfl
  have e8 : BitVec.setWidth 8 1#64 = 1#8 := by decide
  have e8' : BitVec.setWidth 8 (BitVec.setWidth 64 0#32) = 0#8 := by decide
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h1, hrbp, hrsp, z,
    Int64.toBitVec_neg_ofNat_norm, Nat.reduceSub, Nat.reduceAdd]
  all_goals try simp_loads [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp_conds [CondCode.interp, StatusFlags.from_result, hq0, hq1, hq2, Int64.toBitVec_ofNat_norm,
    BitVec.setWidth_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
    BitVec.zero_eq, beq_eq_false_iff_ne, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6797") ?_; refine ⟨isSome_at L.L6797, ?_, ?_⟩; rw [T.L6797])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6817") ?_; refine ⟨isSome_at L.L6817, ?_, ?_⟩; rw [T.L6817])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6f32") ?_; refine ⟨isSome_at L.L6f32, ?_, ?_⟩; rw [T.L6f32])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.start_3])
  all_goals try (refine ⟨hC, ?_⟩; and_intros)
  all_goals try (refine ⟨⟨hC, ?_⟩, ?_⟩; and_intros)
  all_goals try (refine ⟨x, Or.inl rfl, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; exact IdLive.of_start0 ‹_›)
  all_goals try (refine IdLive.of_eq ?_; have hq3 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.idAac; have hcmp := ‹BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.setWidth 64 _) = 0#32›; rw [h2, hq3, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at hcmp; have hcmp' := congrArg (· + x.idAac) hcmp; simp only [BitVec.sub_add_cancel, BitVec.zero_add] at hcmp'; exact hcmp'.symm)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, setWidth8_replaceLow,
    BitVec.xor_self, e8, e8']; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, StatusFlags.from_result,
    hq2, e0, Int64.toBitVec_ofNat_norm, BitVec.sub_zero, BitVec.ofNat_eq_ofNat]; rfl)
  all_goals try (simp only [ne_eq, BitVec.ofNat_eq_ofNat]; assumption)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, arg0, arg1, arg2, arg3, arg4, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, AcW, FrA, FrD, FrRaw, sbrA, arg0, arg1, arg2, arg3, arg4,
    BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done
