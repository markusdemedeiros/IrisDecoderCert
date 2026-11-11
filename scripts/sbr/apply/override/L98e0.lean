theorem blk_L98e0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L98e0" ⟨"ff_aac_sbr_apply.L98e0", B.L98e0, some "ff_aac_sbr_apply.L9927"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hae, hHA, -⟩ := hc
  have hHA' := PLift.up hHA
  clear hHA
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hbx, hm⟩ := T.L98e0.mp hs
  clear hs
  have hlv : ch ≠ 0 → y.idAac = 1#32 := hK.2.live hst
  have hdc : (y.d ch).ypos ≤ 1 ∧ (y.d ch).te.length = 10 ∧ (y.d ch).nenv ≤ 8
      ∧ (∀ e, e ≤ (y.d ch).nenv → u8 (y.d ch).te e ≤ 19) ∧ u8 (y.d ch).te 9 ≤ 19
      ∧ (y.d ch).idx.toNat % 2 ^ 32 ≤ 515 ∧ (y.d ch).idx.toNat / 2 ^ 32 < 4 := by
    unfold Args.d; split
    · obtain ⟨-, -, h3, -, h5, -, -, -, h9, h10, -, h12, h13, -, -, h16⟩ :=
        hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h5, (h16 hst).2.1, h10, h12, h13⟩
    · obtain ⟨-, -, h3, -, h5, -, -, -, h9, h10, -, h12, h13, -, -, h16⟩ :=
        hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      exact ⟨h9, h3, h5, (h16 ⟨hst, hlv (by assumption)⟩).2.1, h10, h12, h13⟩
  clear hlv
  have hyp : (y.d ch).ypos ≤ 1 := hdc.1
  have htl : (y.d ch).te.length = 10 := hdc.2.1
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [DArrW, Blocks] at hm
  rw [gn_hfY (dA t₀ ch) (y.d ch).ypos hyp] at hm
  simp only [DScW] at hm
  rw [gn_te10 (y.d ch).te htl] at hm
  simp only [Mm, ApplyF, FrGA, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
    arg4, lab, FnCell, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rw [gn_call_res_n k (0x290 + k) hSt (by omega)] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.sub_self] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 14596#64)))] as Re hRe
  obtain ⟨v0, v1, hm⟩ := gn_ea hm
  subst hRe
  simp only [BitVec.add_assoc, BitVec.reduceAdd, cell4] at hm
  simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hbx
  have hsw := gn_sw _ (show (y.d ch).ypos < 2 ^ 31 by omega)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L98e0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  all_goals try simp only [hsw, gn_m19, gn_rdi] at *
  -- the `jae` trap branch: ypos ≤ 1 < 3
  all_goals try (
    rename_i hnc
    rw [CondCode.interp_nc_sub64 _ _ _ rfl] at hnc
    simp only [BitVec.toNat_ofNat, decide_eq_true_eq, Nat.reducePow, Nat.reduceMod] at hnc
    omega)
  -- the call
  obtain ⟨hrsp, hrbp, hsl, hn, hbx⟩ := hR.down
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (656 + k) (t₀.regs.get64 .rsp - 464#64),
      19456 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + BitVec.ofNat 64 (19456 * (if ch = 0 then y.d0 else y.d1).ypos))))),
      24 ?@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) +
        (31024#64 + (BitVec.ofNat 64 (19456 * (if ch = 0 then y.d0 else y.d1).ypos) + 19456#64))))),
      (16128 - 24 * (if ch = 0 then y.d0 else y.d1).ypos) ?@ (t₀.regs.get64 .rsi + (166176#64 +
        (BitVec.ofNat 64 (128 + 88768 * ch) + (69936#64 + BitVec.ofNat 64 (24 * (if ch = 0 then y.d0 else y.d1).ypos))))),
      20480 ?@ (t₀.regs.get64 .rsi + 488544#64),
      1536 ?@ (t₀.regs.get64 .rsi + 553952#64), 1536 ?@ (t₀.regs.get64 .rsi + 555488#64),
      1536 ?@ (t₀.regs.get64 .rsi + 557024#64),
      4160 ?@ ((_root_.Executable.labels cenv).label "ff_sbr_noise_table").toBitVec, 16 ?@ ((_root_.Executable.labels cenv).label "ps_noise0").toBitVec,
      48 ?@ ((_root_.Executable.labels cenv).label "ps_noise13").toBitVec, 16 ?@ ((_root_.Executable.labels cenv).label "ps_noise2").toBitVec,
      4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_6").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_7").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_8").toBitVec,
      4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_9").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_10").toBitVec, 4 ?@ ((_root_.Executable.labels cenv).label "LCPI17_12").toBitVec,
      Int.toBytes 16 0x3000001ff =@ ((_root_.Executable.labels cenv).label "LCPI17_11").toBitVec,
      Int.toBytes 4 y.reset.toInt =@ (t₀.regs.get64 .rsi + 166200#64),
      Int.toBytes 4 y.smooth.toInt =@ (t₀.regs.get64 .rsi + 166232#64),
      Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64),
      Int.toBytes 4 (y.m1 : Int) =@ (t₀.regs.get64 .rsi + 166272#64),
      Int.toBytes 8 e.fs.hfs.gfilt.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559944#64),
      Int.toBytes 8 e.fs.hfs.noise0.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559952#64),
      Int.toBytes 8 e.fs.hfs.noise1.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559960#64),
      Int.toBytes 8 e.fs.hfs.noise2.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559968#64),
      Int.toBytes 8 e.fs.hfs.noise3.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559976#64),
      Int.toBytes 4 ((if ch = 0 then y.d0 else y.d1).nenv : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 8#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88732#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 1 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88733#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 2 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88734#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 3 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88735#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 4 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88736#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 5 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88737#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 6 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88738#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 7 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88739#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 8 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88740#64))),
      Int.toBytes 1 (((if ch = 0 then y.d0 else y.d1).te.getD 9 0).toNat : Int) =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88741#64))),
      Int.toBytes 4 v0.toInt =@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 14596#64))),
      Int.toBytes 4 v1.toInt =@ (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 14600#64))),
      Int.toBytes 8 (if ch = 0 then y.d0 else y.d1).idx.toInt =@
        (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88748#64)))] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  rw [hae]
  refine MachineWP.CallsTo.of_procSpec
    (⟨Rc, y.reset, y.smooth, y.kx1, y.m1, (if ch = 0 then y.d0 else y.d1).nenv,
      fun i => ((if ch = 0 then y.d0 else y.d1).te.getD i 0).toNat, v0, v1,
      (if ch = 0 then y.d0 else y.d1).idx, (if ch = 0 then y.d0 else y.d1).ypos⟩ : HfArgs) hHA'.down
    (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, hsw, gn_m19, gn_rdi,
      BitVec.add_assoc, BitVec.setWidth_eq, Blocks]
    sep_mem hm
    sep_close hm
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, hsw, gn_m19, gn_rdi,
      BitVec.add_assoc, BitVec.setWidth_eq, Blocks])
  · exact gn_al_rsp _ hCy.2.2.2.2.2.1
  · exact gn_al16 hCy.2.2.1
  · exact gn_alD _ ch hCy.2.2.1
  · exact hCy.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  · exact hCy.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.1
  · exact hCy.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2
  · exact (hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst).2.2.2.2.2.2.1
  · exact hCy.1.2.2.2.2.1
  · exact hCy.1.2.2.2.1
  · exact hdc.2.2.1
  · exact hdc.2.2.2.1
  · exact hdc.2.2.2.2.1
  · exact hdc.2.2.2.2.2.1
  · exact hdc.2.2.2.2.2.2
  · exact hyp
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, hsw, gn_m19, gn_rdi,
      BitVec.add_assoc, BitVec.setWidth_eq, Blocks, gn_hio, arg3] at hpost
    obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
    have hsp : ∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64 := fun a => by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsp] at hrsp'
    have e := hRc'.down
    subst e
    -- G1: the post's `f_indexnoise`/`f_indexsine` cell comes back bounded (`HfIdxOut`)
    sep_pull hm' [gnIdx (t₀.regs.get64 .rsi + (166176#64 + (BitVec.ofNat 64 (128 + 88768 * ch) + 88748#64)))] as Ri hRi
    obtain ⟨i, hi1, hi2, hm'⟩ := gn_idx hm'
    subst hRi
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    · rw [T.L9927]
      refine ⟨hC, ⟨hrsp', hrbp'⟩, ch, c0, hch, hc0, ?_, ?_⟩
      · rw [hbx']
        simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      · obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
        · have hyp0 : y.d0.ypos ≤ 1 := by simpa using hyp
          have htl0 : y.d0.te.length = 10 := by simpa using htl
          refine ⟨{ y with d0 := { y.d0 with idx := i } }, hK, gn_applyC_idx0 hCy i hi1 hi2, ?_⟩
          simp only [Mm, ApplyF, DArrW, Blocks]
          rw [gn_hfY (dA t₀ 0) y.d0.ypos hyp0]
          simp only [DScW]
          rw [gn_te10 _ htl0]
          simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, CstW, Blocks, c4, cell4, sbrA, arg0,
            arg1, arg3, arg4, lab, FnCell, BitVec.add_assoc, BitVec.reduceAdd]
          rw [gn_call_res_n k (0x290 + k) hSt (by omega)]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.sub_self, dA, Args.d, Nat.reducePow, Nat.reduceSub,
            Nat.reduceMod, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte,
            Nat.one_ne_zero] at hm' ⊢
          simp only [AcW, OutW, dsN] at hm' ⊢
          rw [gn_m38, gn_split44 (t₀.regs.get64 .rsi + 180900#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          sep_close hm'
        · have hyp0 : y.d1.ypos ≤ 1 := by simpa using hyp
          have htl0 : y.d1.te.length = 10 := by simpa using htl
          refine ⟨{ y with d1 := { y.d1 with idx := i } }, hK, gn_applyC_idx1 hCy i hi1 hi2, ?_⟩
          simp only [Mm, ApplyF, DArrW, Blocks]
          rw [gn_hfY (dA t₀ 1) y.d1.ypos hyp0]
          simp only [DScW]
          rw [gn_te10 _ htl0]
          simp only [Mm, ApplyF, FrCs, ScW, TabW, DScW, DArrW, ArrW, PsW, DspW, FnW, CstW, Blocks, c4, cell4, sbrA, arg0,
            arg1, arg3, arg4, lab, FnCell, BitVec.add_assoc, BitVec.reduceAdd]
          rw [gn_call_res_n k (0x290 + k) hSt (by omega)]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.sub_self, dA, Args.d, Nat.reducePow, Nat.reduceSub,
            Nat.reduceMod, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, ↓reduceIte,
            Nat.one_ne_zero] at hm' ⊢
          simp only [AcW, OutW, dsN] at hm' ⊢
          rw [gn_m38, gn_split44 (t₀.regs.get64 .rsi + 269668#64)]
          simp only [BitVec.add_assoc, BitVec.reduceAdd]
          sep_close hm'
    · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢
      sep_mem hm'
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      try rw [← hn]
      var_step
