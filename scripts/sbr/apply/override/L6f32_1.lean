theorem blk_L6f32_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6f32_1" ⟨"ff_aac_sbr_apply.L6f32_1", B.L6f32_1, some "ff_aac_sbr_apply.L6f32_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, hb, hm⟩ := T.L6f32_1.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, DScW, FrA, sbrA, dA, Args.d, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd] at hm
  -- the 8-byte store covers `start` and `ready`: merge the two cells
  sep_pull hm [cell4 (t₀.regs.get64 .rsi + 0x28924#64) x.start,
    cell4 (t₀.regs.get64 .rsi + 0x28928#64) x.ready] as R hR
  rw [← Std.ExtHashMap.sep_assoc, ← Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  dsimp only
  simp only [B.L6f32_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  -- the load of the `che` slot: name its result, normalise its address, read the frame
  all_goals try (rename_i v hv; simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
    Width.bytes, hrbp, z, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv)
  all_goals try (simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at hv)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  refine ⟨?_, ?_⟩
  rotate_left
  · var_step
  rw [T.L6f32_2]
  refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, arg1]; done)
  all_goals try (simpa only [Reg64s.get64_set64, reduceCtorEq, ite_false] using hb)
  have h8 : Int.toBytes 8 (BitVec.setWidth 64 0#64).toInt
      = Int.toBytes 4 (0#32).toInt ++ Int.toBytes 4 (0#32).toInt := by decide
  have e0 : (BitVec.setWidth 32 0#64).toInt = ((0 : Nat) : Int) := by decide
  have e32 : (BitVec.setWidth 32 32#64).toInt = ((32 : Nat) : Int) := by decide
  rw [h8, Val.append_eq _ _ _ (t₀.regs.get64 .rsi + 166184#64) (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  have es32 : BitVec.setWidth 32 4294967295#64 = BitVec.allOnes 32 := by decide
  have es16 : BitVec.setWidth 16 65535#64 = BitVec.allOnes 16 := by decide
  simp only [e0, e32, es32, es16] at hm
  have hT : TabW x.turnoff.spSet t₀ = TabW x t₀ := rfl
  have hF : FnW e x.turnoff.spSet t₀ = FnW e x t₀ := rfl
  have hA : AcW x.turnoff.spSet t₀ = AcW x t₀ := rfl
  have hO : OutW x.turnoff.spSet t₀ = OutW x t₀ := rfl
  have hP : PsW x.turnoff.spSet t₀ = PsW x t₀ := rfl
  simp only [Mm, ApplyF, hT, hF, hA, hO, hP]
  simp only [ScW, DScW, FrD, sbrA, dA, Args.d, Args.turnoff, Args.spSet, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd]
  sep_close hm
