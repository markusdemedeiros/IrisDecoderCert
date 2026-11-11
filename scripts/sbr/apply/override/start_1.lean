theorem blk_start_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.start_1" ⟨"ff_aac_sbr_apply.start_1", B.start_1, some "ff_aac_sbr_apply.start_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ⟨h0, h1, h2, h3, h4⟩, hm⟩ := T.start_1.mp hs
  clear hs
  -- open the groups the block reads
  simp only [Mm, ApplyF, ScW, AcW, FrA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h0 h1 h2 h3 h4
  -- the `setl -0xf0(%rbp)` byte: cut slot sf0 into its low byte and the rest
  have hsp : (8 ?@ (t₀.regs.get64 .rsp - 248#64)) = 1 ?@ (t₀.regs.get64 .rsp - 248#64)
      ⋆ 7 ?@ (t₀.regs.get64 .rsp - 247#64) := by
    rw [show (8 : Nat) = 1 + 7 from rfl, Mem.Block.split _ 1 7 (by decide)]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [hsp] at hm
  simp only [B.start_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h0, h1, arg0, arg1, z]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc4 =>
    have ez : BitVec.setWidth 64 0#32 = 0#64 := by decide
    rw [T.start_2]
    refine ⟨⟨hC, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      BitVec.xor_self, ez, true_and,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, arg0, arg1, arg2, arg3, arg4, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]
    case refine_8 =>
      have hq0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.extRate
      have hq1 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.sampleRate
      simp only [BitVec.setWidth_setWidth_of_le, Nat.reduceLeDiff, BitVec.setWidth_eq, hq0, hq1] at hm ⊢
      simp (disch := rfl) only [setl_byte] at hm ⊢
      simp only [Mm, ApplyF, ScW, AcW, FrA1, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
        BitVec.reduceAdd, dsN]
      sep_close hm
    case refine_9 => var_step
