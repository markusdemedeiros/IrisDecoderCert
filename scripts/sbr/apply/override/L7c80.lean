theorem blk_L7c80 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7c80" ⟨"ff_aac_sbr_apply.L7c80", B.L7c80, some "ff_aac_sbr_apply.L7c80_1"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, y, hK, hCy, hst, hne, hm⟩ := T.L7c80.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, FnW, AcW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hbx, hn⟩ : _ ∧ _ ∧ _ ∧ _)
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hm0 := hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  dsimp only
  simp only [B.L7c80]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm0
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, BitVec.add_assoc,
    BitVec.reduceAdd] at *
  all_goals try sep_vals hm0
  all_goals try sep_mem hm0
  case vc3 =>
    obtain ⟨hrsp, hrbp, hbx, hn⟩ := hR.down
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7c80_1]
        refine ⟨ch, c0, _, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, y, hK, hCy, hst, rfl, ?_⟩
        · rw [hsv.1, hbx]
        simp only [Mm, ApplyF, FrH, ScW, TabW, FnW, AcW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
          BitVec.reduceAdd]
        rw [call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        try rw [← hn]
        var_step
