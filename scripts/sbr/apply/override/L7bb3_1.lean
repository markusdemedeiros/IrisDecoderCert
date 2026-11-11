theorem blk_L7bb3_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb3_1" ⟨"ff_aac_sbr_apply.L7bb3_1", B.L7bb3_1, some "ff_aac_sbr_apply.L7bb3_2"⟩ := by
  obtain ⟨-, -, -, -, hHG, -⟩ := hc
  have hHG' := PLift.up hHG
  clear hHG
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne,
    hj, hxx, hkk, hg, hax, hdi, hsi, hm⟩ := T.L7bb3_1.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  subst hne
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hTW : TabWF y := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hpj : u8 y.pstart j + u8 y.pnum j ≤ 32 := hTW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  have hdc : DWF True (y.d ch) := by
    unfold Args.d; split
    · exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => hst
    · rename_i hc0'; exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => ⟨hst, hK.2.live hst hc0'⟩
  have hlv := hdc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 trivial
  have hteN : u8 (y.d ch).te (y.d ch).nenv ≤ 19 := hlv.2.1 _ (Nat.le_refl _)
  have hte0 : u8 (y.d ch).te 0 < u8 (y.d ch).te (y.d ch).nenv :=
    lt_of_mono (fun e => u8 (y.d ch).te e) _ hlv.2.2 hlv.1
  have htl : (y.d ch).te.length = 10 := hdc.2.2.1
  have hn8 : (y.d ch).nenv ≤ 8 := hdc.2.2.2.2.1
  have hn1 : 0 < (y.d ch).nenv := hlv.1
  clear hlv
  have hal1 : isAligned 32 (arg1 t₀) = true := hC.2.1
  have halps : isAligned 16 (lab "ps_mask") = true := hC.2.2.2.2.2.2.2.2.2.2.2.1.1
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [DArrW, Blocks] at hm
  -- M4-F1 closed: the entry has `g < n_q ≤ 5` (TabWF F2/F5 through the HfGen loop), so `bw_array[g]`
  -- is inside its own 20-byte Block.
  simp only [DScW] at hm
  rw [te_split (y.d ch).te _ (y.d ch).nenv hn1 (by omega) (by omega)] at hm
  simp only [Mm, ApplyF, FrH, ScW, TabW, DScW, DArrW, ArrW, DspW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4,
    lab, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hXh := carve_at (t₀.regs.get64 .rsi + 488544#64) 20480 (320 * kk + 16 + 16 * u8 (y.d ch).te 0)
    (16 * (u8 (y.d ch).te (y.d ch).nenv - u8 (y.d ch).te 0)) (by omega) (by decide)
  have hXl := carve_at (t₀.regs.get64 .rsi + 478304#64) 10240 (320 * (u8 y.pstart j + xx) + 16 * u8 (y.d ch).te 0)
    (16 * (u8 (y.d ch).te (y.d ch).nenv - u8 (y.d ch).te 0) + 16) (by omega) (by decide)
  have hA0 := carve_at (t₀.regs.get64 .rsi + 547936#64) 512 (8 * (u8 y.pstart j + xx)) 8 (by omega) (by decide)
  have hA1 := carve_at (t₀.regs.get64 .rsi + 548448#64) 512 (8 * (u8 y.pstart j + xx)) 8 (by omega) (by decide)
  rw [hXh, hXl, hA0, hA1, call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  rw [res_k0 hSt] at hm
  simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hbx
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax, h15, h12, h14, h13, hdi, hsi⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7bb3_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow,
      Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, h15, h12, h14, h13,
      hdi, hsi, BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, BitVec.add_assoc,
    BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try (guard_target =ₛ 0 + g * 4 + 4 ≤ 20; omega)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  -- the call
  obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax, h15, h12, h14, h13, hdi, hsi⟩ := hR.down
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hbx hdi hsi
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
    (16 * (((if ch = 0 then y.d0 else y.d1).te.getD (if ch = 0 then y.d0 else y.d1).nenv 0).toNat - ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat)) ?@ (t₀.regs.get64 .rsi + (488544#64 + BitVec.ofNat 64 (320 * kk + 16 + 16 * ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat))),
    (16 * (((if ch = 0 then y.d0 else y.d1).te.getD (if ch = 0 then y.d0 else y.d1).nenv 0).toNat - ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat) + 16) ?@ (t₀.regs.get64 .rsi + (478304#64 + BitVec.ofNat 64 (320 * ((y.pstart.getD j 0).toNat + xx) + 16 * ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat))),
    8 ?@ (t₀.regs.get64 .rsi + (547936#64 + BitVec.ofNat 64 (8 * ((y.pstart.getD j 0).toNat + xx)))),
    8 ?@ (t₀.regs.get64 .rsi + (548448#64 + BitVec.ofNat 64 (8 * ((y.pstart.getD j 0).toNat + xx)))), 16 ?@ lab "ps_mask"] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
  refine MachineWP.CallsTo.of_procSpec Rc hHG'.down
    (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hdi, hsi, te2x, h12, h13, h14, h15,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  all_goals try simp (disch := omega) only [sx2, hg_sz, hg_xh, hg_xl]
  all_goals try simp only [hg_m8]
  · sep_mem hm
    sep_close hm
  · exact hg_lt _ _ hte0 (by omega)
  · exact hg_even _ _
  · refine hg_al _ _ _ hal1 ?_ ?_
    · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    · omega
  · refine hg_al _ _ _ hal1 ?_ ?_
    · simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    · omega
  · exact halps
  · try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hdi, hsi, te2x, h12, h13, h14, h15,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
    try simp (disch := omega) only [sx2, hg_sz, hg_xh, hg_xl] at hpost
    try simp only [hg_m8] at hpost
    obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
    have hsp : ∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64 := fun a => by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsp] at hrsp'
    have e := hRc'.down
    subst e
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    · rw [T.L7bb3_2]
      refine ⟨_, c0, _, j, kk, g, xx, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, rfl, hj, hxx,
        hkk, hg, ?_⟩
      all_goals try (simp only [arg1, hbx', h12', h13', h14', h15', h12, h13, h14, h15]; done)
      have hn1' : 0 < (y.d ch).nenv := hn1
      have htl' : (y.d ch).te.length = 10 := htl
      have hn8' : (y.d ch).nenv ≤ 8 := hn8
      simp only [Mm, ApplyF]
      rw [applyF_dpair y t₀ ch hch]
      simp only [DArrW, Blocks]
      simp only [DScW]
      rw [te_split (y.d ch).te _ (y.d ch).nenv hn1' (by omega) (by omega)]
      simp only [Mm, ApplyF, FrH, ScW, TabW, DScW, DArrW, ArrW, DspW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
        arg4, lab, BitVec.add_assoc, BitVec.reduceAdd]
      rw [hXh, hXl, hA0, hA1, call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      rw [res_k0 hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        dA, Args.d] at hm' ⊢
      sep_close hm'
    · simp only [lex_var, slot64, hrbp', h15', h14', h15, h14, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢
      sep_mem hm'
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      try rw [← hn]
      var_step
