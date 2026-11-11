theorem blk_L7750_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_4" ⟨"ff_aac_sbr_apply.L7750_4", B.L7750_4, some "ff_aac_sbr_apply.L7750_5"⟩ := by
  obtain ⟨-, -, -, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_4.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.2.1
  have hlast := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2   -- G2: LayoutC has the ps_noise group and `pd_reverse` before the last conjunct
  have hyp := ApplyC_ypos_le hCy ch
  simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal hlast
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  have hZ := carve_at (sbrA t₀ + 0x5fcc0#64) 1280 0 256 (by omega) (by decide)
  simp only [sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.sub_zero, Nat.reduceSub] at hZ
  have hZ' := PLift.up hZ
  clear hZ
  have hX := carve_at (dA t₀ ch + 0x3920#64) 16384 (8192 * (y.d ch).ypos + 256 * i) 256 (by omega) (by decide)
  have hax : isAligned 32 (dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i)) = true :=
    isAligned_add (by decide) (isAligned_add (by decide) (isAligned_add (by decide) hC.2.2.1
      (by simp only [BitVec.toNat_ofNat]; omega)) (by decide)) (by simp only [BitVec.toNat_ofNat]; omega)
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, Args.d,
      ↓reduceIte, Nat.one_ne_zero] at hX hm hax
    rw [hX, hZ'.down, call_res k hSt] at hm
    have hX' := PLift.up hX
    clear hX
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    rw [res_k0 hSt] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    -- the call
    obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
    simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Args.d,
      ↓reduceIte, Nat.one_ne_zero] at h12 h14 h15
    first
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
          256 ?@ (t₀.regs.get64 .rsi + (180928#64 + BitVec.ofNat 64 (8192 * y.d0.ypos + 256 * i))),
          256 ?@ (t₀.regs.get64 .rsi + 558560#64), 16 ?@ lab "ff_ps_neg"] as Rc hRc
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
          256 ?@ (t₀.regs.get64 .rsi + (269696#64 + BitVec.ofNat 64 (8192 * y.d1.ypos + 256 * i))),
          256 ?@ (t₀.regs.get64 .rsi + 558560#64), 16 ?@ lab "ff_ps_neg"] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hFR'.down
      (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      try simp only [BitVec.ofNat_eq_ofNat] at hax
      exact al16_of_32 hax
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, MachineData.pushRa, h14]
      exact al16_of_32 (al32_add1 _ 558560 hal (by decide))
    · exact halw
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, MachineData.pushRa, h14]
      omega
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_5]
        refine ⟨_, c0, i, hC, ⟨hrsp', hrbp'⟩, hch, hc0, hi, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx', h12', h13', h14', h15', dA, sbrA, arg1, Args.d, ↓reduceIte]; done)
        simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero]
        rw [hX'.down, hZ'.down, call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        rw [res_k0 hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', hrbp, h13', h13, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        var_step
