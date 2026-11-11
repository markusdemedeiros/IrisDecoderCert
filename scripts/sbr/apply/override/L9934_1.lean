theorem blk_L9934_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9934_1" ⟨"ff_aac_sbr_apply.L9934_1", B.L9934_1, some "ff_aac_sbr_apply.L9934_2"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hxe, hXG, -⟩ := hc
  have hXG' := PLift.up hXG
  clear hXG
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h12, h9, hsi, hdi, hrb, y, hK, hCy, hax, hcx, hm⟩ := T.L9934_1.mp hs
  clear hs
  have hdc : (y.d ch).ypos ≤ 1 ∧ (y.d ch).te.length = 10 ∧ u8 (y.d ch).te 9 ≤ 19 := by
    unfold Args.d; split
    · obtain ⟨-, -, h3, -, -, -, -, -, h9, h10, -⟩ := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h10⟩
    · obtain ⟨-, -, h3, -, -, -, -, -, h9, h10, -⟩ := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h10⟩
  have hyp : (y.d ch).ypos ≤ 1 := hdc.1
  have htl : (y.d ch).te.length = 10 := hdc.2.1
  have hte9 : u8 (y.d ch).te 9 ≤ 19 := hdc.2.2
  have hkx0 : y.kx0 ≤ 32 := hCy.1.1
  have hkx1 : y.kx1 ≤ 32 := hCy.1.2.1
  have hm0 : y.kx0 + y.m0 ≤ 64 := hCy.1.2.2.1
  have hm1 : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [DArrW, Blocks] at hm
  rw [gn_y3 (dA t₀ ch + 0x7930#64) (y.d ch).ypos hyp] at hm
  simp only [DScW] at hm
  rw [gn_byte_split (y.d ch).te _ 9 (by omega) (by omega)] at hm
  simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, DspW, FnW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
    arg4, lab, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rw [gn_x2 (t₀.regs.get64 .rsi) ch (by omega), gn_call_res_n k (0x60 + k) hSt (by omega)] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h12, h9, hsi, hdi, hax, hcx, hrb⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L9934_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  -- the call
  obtain ⟨hrsp, hrbp, hsl, hn, h12, h9, hsi, hdi, hax, hcx, hrb⟩ := hR.down
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Args.d]
    at hsi hdi hax hcx
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (96 + k) (t₀.regs.get64 .rsp - 464#64),
      19456 ?@ (t₀.regs.get64 .rsi + (509024#64 + BitVec.ofNat 64 (19456 * ch))),
      10240 ?@ (t₀.regs.get64 .rsi + 478304#64),
      19456 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + BitVec.ofNat 64 (19456 * (1 - (if ch = 0 then y.d0 else y.d1).ypos)))))),
      19456 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + BitVec.ofNat 64 (19456 * (if ch = 0 then y.d0 else y.d1).ypos))))),
      Int.toBytes 4 (y.kx0 : Int) =@ (t₀.regs.get64 .rsi + 166260#64),
      Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64),
      Int.toBytes 4 (y.m0 : Int) =@ (t₀.regs.get64 .rsi + 166268#64),
      Int.toBytes 4 (y.m1 : Int) =@ (t₀.regs.get64 .rsi + 166272#64),
      [(if ch = 0 then y.d0 else y.d1).te.getD 9 0] =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88741#64)))] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  rw [hxe]
  refine MachineWP.CallsTo.of_procSpec
    (⟨Rc, BitVec.ofNat 32 y.kx0, BitVec.ofNat 32 y.kx1, BitVec.ofNat 32 y.m0, BitVec.ofNat 32 y.m1,
      BitVec.ofNat 8 ((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat⟩ : XGenArgs) hXG'.down
    (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      gn_rax _ _ hax, gn_m19, gn_r9 ch hch, BitVec.add_assoc, BitVec.setWidth_eq, Blocks]
    simp only [gn_te, gn_c4 _ (show y.kx0 < 2 ^ 31 by omega), gn_c4 _ (show y.kx1 < 2 ^ 31 by omega),
      gn_c4 _ (show y.m0 < 2 ^ 31 by omega), gn_c4 _ (show y.m1 < 2 ^ 31 by omega),
      gn_tb1 _ (show ((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat < 128 by omega)]
    sep_mem hm
    sep_close hm
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      gn_rax _ _ hax, gn_m19, gn_r9 ch hch, BitVec.add_assoc, BitVec.setWidth_eq, Blocks]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, MachineData.pushRa, h9,
    BitVec.toNat_ofNat]; omega)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h9, hsi, hdi, hcx,
      gn_rax _ _ hax, gn_m19, gn_r9 ch hch, BitVec.add_assoc, BitVec.setWidth_eq, Blocks] at hpost
    simp only [gn_te, gn_c4 _ (show y.kx0 < 2 ^ 31 by omega), gn_c4 _ (show y.kx1 < 2 ^ 31 by omega),
      gn_c4 _ (show y.m0 < 2 ^ 31 by omega), gn_c4 _ (show y.m1 < 2 ^ 31 by omega),
      gn_tb1 _ (show ((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat < 128 by omega)] at hpost
    obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
    have hsp : ∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64 := fun a => by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsp] at hrsp'
    have e := hRc'.down
    subst e
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    · rw [T.L9934_2]
      refine ⟨ch, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_⟩
      all_goals try (simp only [h12', h14', h12, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
      all_goals try (rw [hbx']; exact hrb)
      have hyp' : (y.d ch).ypos ≤ 1 := hyp
      have htl' : (y.d ch).te.length = 10 := htl
      simp only [Mm, ApplyF]
      rw [applyF_dpair y t₀ ch hch]
      simp only [DArrW, Blocks]
      rw [gn_y3 (dA t₀ ch + 0x7930#64) (y.d ch).ypos hyp']
      simp only [DScW]
      rw [gn_byte_split (y.d ch).te _ 9 (by omega) (by omega)]
      simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, DspW, FnW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
        arg4, lab, BitVec.add_assoc, BitVec.reduceAdd]
      rw [gn_x2 (t₀.regs.get64 .rsi) ch (by omega), gn_call_res_n k (0x60 + k) hSt (by omega)]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, dA, Args.d, Nat.reducePow, Nat.reduceSub, Nat.reduceMod,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] at hm' ⊢
      sep_close hm'
    · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢
      sep_mem hm'
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      try rw [← hn]
      var_step
