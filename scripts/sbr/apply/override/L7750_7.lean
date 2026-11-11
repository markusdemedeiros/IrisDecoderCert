theorem blk_L7750_7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_7" ⟨"ff_aac_sbr_apply.L7750_7", B.L7750_7, some "ff_aac_sbr_apply.L7750_8"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, hhie, hHI, -⟩ := hc
  have hHI' := PLift.up hHI
  clear hHI
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h15, hbx, y, hK, hCy, hrax, hm⟩ := T.L7750_7.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hk0 : y.k0 ≤ 32 := hCy.1.2.2.2.2.2.1
  have hpm := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst := hC.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, DScW, c4, ScW, FnW, Blocks, sbrA, arg0, arg1, arg3, arg4,
    BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [hfd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  have hX := carve_at (t₀.regs.get64 .rsi + 478304#64) 10240 0 (320 * y.k0) (by omega) (by decide)
  have hA0 := carve_at (t₀.regs.get64 .rsi + 547936#64) 512 0 (8 * y.k0) (by omega) (by decide)
  have hA1 := carve_at (t₀.regs.get64 .rsi + 548448#64) 512 0 (8 * y.k0) (by omega) (by decide)
  simp only [BitVec.add_zero, BitVec.ofNat_eq_ofNat, Nat.sub_zero] at hX hA0 hA1
  rw [hX, hA0, hA1, call_res_n k 0xa8 hSt (by omega)] at hm
  have hC' := PLift.up (⟨hX, hA0, hA1⟩ : _ ∧ _ ∧ _)
  clear hX hA0 hA1
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  simp only [dA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
    Nat.one_ne_zero] at hm hrax
  simp only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
  have hR := PLift.up (⟨hrsp, hrbp, h14, h15, hbx, hsl, hrax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7750_7]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
      BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc3 =>
    obtain ⟨hrsp, hrbp, h14, h15, hbx, hsl, hrax⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9934") ?_
    refine ⟨isSome_at L.L9934, ?_, ?_⟩
    · rw [T.L9934]
      refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, ?_, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero]; done)
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
                     first | exact hrax | (simp only [Nat.reducePow] at hrax ⊢; exact hrax))
      simp only [Mm, ApplyF, FrC, FrCs, ArrW, DspW, CstW, DArrW, DScW, c4, ScW, FnW, FnCell, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
      rw [hC'.down.1, hC'.down.2.1, hC'.down.2.2, call_res_n k 0xa8 hSt (by omega)]
      try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] at hm ⊢
      sep_close hm
    · first
        | (left; var_step)
        | (left
           simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
             BitVec.sub_sub_ofNat, Nat.reduceAdd]
           sep_mem hm
           simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat]
           try simp only [BitVec.toNat_ofNat] at hn
           var_step)
        | (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
             BitVec.sub_sub_ofNat, Nat.reduceAdd]
           sep_mem hm
           simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat]
           try simp only [BitVec.toNat_ofNat] at hn
           var_step)
  case vc11 =>
    obtain ⟨hrsp, hrbp, h14, h15, hbx, hsl, hrax⟩ := hR.down
    rename_i hzf hfi
    simp only [CondCode.interp_z, StatusFlags.zf_from_result] at hzf
    have hs0 := start_ne _ hzf
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0xa8 (t₀.regs.get64 .rsp - 464#64),
        (320 * y.k0) ?@ (t₀.regs.get64 .rsi + 478304#64), (8 * y.k0) ?@ (t₀.regs.get64 .rsi + 547936#64),
        (8 * y.k0) ?@ (t₀.regs.get64 .rsi + 548448#64), 4 ?@ lab "LCPI19_0", 4 ?@ lab "LCPI19_1",
        16 ?@ lab "LCPI19_2", 16 ?@ lab "ps_mask3",
        Int.toBytes 8 e.fs.autocorr.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559928#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    rw [hhie]
    refine MachineWP.CallsTo.of_procSpec Rc hHI'.down
      (fun ra' => ⟨⟨?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero, HfInvF, hfInvN, FnCell, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, k0_n _ hk0, k0_n2 _ hk0]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero, hfInvN, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, k0_n _ hk0, k0_n2 _ hk0]
      first
        | exact hk0
    · exact hpm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero]
      first
        | exact al16_rsp456 _ hst
        | (rw [hsp.down]; exact al16_rsp456 _ hst)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero, HfInvF, hfInvN, FnCell, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, k0_n _ hk0, k0_n2 _ hk0] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_8]
        refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, y, hK, hCy, hs0, ?_⟩
        simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, DScW, c4, ScW, FnW, FnCell, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
        rw [hC'.down.1, hC'.down.2.1, hC'.down.2.2, call_res_n k 0xa8 hSt (by omega)]
        try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] at hm' ⊢
        sep_close hm'
      · first
          | var_step
          | (simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
             sep_mem hm'
             simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat]
             try simp only [BitVec.toNat_ofNat] at hn
             var_step)
