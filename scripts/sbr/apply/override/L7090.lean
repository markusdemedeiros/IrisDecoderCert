set_option maxRecDepth 8000 in
theorem blk_L7090 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7090" ⟨"ff_aac_sbr_apply.L7090", B.L7090, some "ff_aac_sbr_apply.L7090_1"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hk48, hm⟩ := T.L7090.mp hs
  clear hs
  have pj : PLift _ := ⟨hj⟩
  have pn : PLift _ := ⟨hn⟩
  clear hj hn
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, FnW, FrDq, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  dsimp only
  simp only [B.L7090]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  case vc1 =>
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      have h38 : slot64 s' 0x38 = arg1 t₀ := by
        simp only [slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, arg1]
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7090_1]
        refine ⟨hC, ⟨hrsp', hrbp'⟩, ch, nch, hch, hnch, ?_, j, ?_, hj1, hj2, ?_, ?_, ?_, ?_⟩
        · rw [h13', hd]
        · rw [h15', pj.down]
        · rw [h14', h14]
        · rw [h12', h12]
        · rw [hbx']; exact hk48
        · simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, FnW, FrDq, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
          rw [call_res k hSt]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_close hm'
      · have hn := pn.down
        simp only [lex_var, arg1] at hn ⊢
        rw [h38, h13', h15', hbx', ← hn, h9]; try simp only [arg1]
        first | exact le_refl _ | exact Nat.le_refl _ | dq_lexE
