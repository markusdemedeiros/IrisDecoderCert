theorem blk_L6797 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6797" ⟨"ff_aac_sbr_apply.L6797", B.L6797, some "ff_aac_sbr_apply.L6797_1"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h0, h2, hm⟩ := T.L6797.mp hs
  clear hs
  simp only [Mm, ApplyF, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h0 h2
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  dsimp only
  simp only [B.L6797]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have zc : ∀ (a : BitVec 64) (c d : Nat), d ≤ c → a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c - d) := by
    intro a c d h; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h0, h2]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  case vc2 => decide
  case vc3 =>
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, h0, h2, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, h0, h2, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, h0, h2, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L6797_1]
      have h14' : s'.regs.get64 .r14 = 0#64 := by
        rw [hsv.2.2.2.1]
        all_goals first
        | (simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hrbp]; done)
        | exact hrbp.2
      refine ⟨hC, ⟨hrsp', hrbp', h14'⟩, ?_⟩
      simp only [Mm, ApplyF, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
        BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm'
