theorem blk_L7750_5 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_5" ⟨"ff_aac_sbr_apply.L7750_5", B.L7750_5, some "ff_aac_sbr_apply.L7750_6"⟩ := by
  obtain ⟨-, -, -, -, -, hlfe, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_5.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, DArrW, DScW, c4, ArrW, FnW, ScW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal
  simp only [hfd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  rw [ana_t128 i (by omega)] at hn
  have hyp := ApplyC_ypos_le hCy ch
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hm
    rw [call_res_n k (0x30 + k) hSt (by omega)] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_5]
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
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    case vc1 =>
      obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
      rename_i hz
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result] at hz
      have hi1 := ana_nz i hi hz
      simp only [ana_r13_step i hi, ana_r15_step]
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7750") ?_
      refine ⟨isSome_at L.L7750, ?_, ?_⟩
      · rw [T.L7750]
        refine ⟨_, c0, i + 1, hC, ⟨?_, ?_⟩, hch, hc0, hi1, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h12, h13,
          h14, h15, hbx, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, Args.d,
          ↓reduceIte, Nat.one_ne_zero, BitVec.ofNat_eq_ofNat]; done)
        simp only [Mm, ApplyF, FrA6, DArrW, DScW, c4, ArrW, FnW, ScW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
        rw [call_res_n k (0x30 + k) hSt (by omega)]
        try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        first
          | sep_close hm
      · left
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, h13,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, ana_t128 (i + 1) (by omega)]
        first
          | var_step
    case vc9 =>
      obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
      simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero] at h12 h14 h15
      first
        | guard_hyp hch :ₛ 0 < 2
          sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (0x30 + k) (t₀.regs.get64 .rsp - 464#64),
            10240 ?@ (t₀.regs.get64 .rsi + 478304#64), 16384 ?@ (t₀.regs.get64 .rsi + 180928#64),
            Int.toBytes 4 (y.kx0 : Int) =@ (t₀.regs.get64 .rsi + 166260#64),
            Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64)] as Rc hRc
        | guard_hyp hch :ₛ 1 < 2
          sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (0x30 + k) (t₀.regs.get64 .rsp - 464#64),
            10240 ?@ (t₀.regs.get64 .rsi + 478304#64), 16384 ?@ (t₀.regs.get64 .rsi + 269696#64),
            Int.toBytes 4 (y.kx0 : Int) =@ (t₀.regs.get64 .rsi + 166260#64),
            Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64)] as Rc hRc
      have hRc' := PLift.up hRc
      clear hRc
      rw [hlfe]
      refine MachineWP.CallsTo.of_procSpec (⟨Rc, y.kx0, y.kx1⟩ : LfGenArgs) hFR'.down
        (fun ra' => ⟨⟨?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, LfGenF, LfGenKx]
        sep_mem hm
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, lfBuf]
        first
          | exact ypos_buf _ hyp
      · exact hCy.1.1
      · exact hCy.1.2.1
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, LfGenF, LfGenKx] at hpost
        obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        rw [hsp.down] at hrsp'
        have e := hRc'.down
        subst e
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨?_, ?_⟩
        · rw [T.L7750_6]
          refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_⟩
          all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, hbx', h12', h13', h14', h15', dA, sbrA, arg1]; done)
          simp only [Mm, ApplyF, FrA6, DArrW, DScW, c4, ArrW, FnW, ScW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
            BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
          rw [call_res_n k (0x30 + k) hSt (by omega)]
          try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
          first
            | sep_close hm'
        · simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_mem hm'
          simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
          first
            | var_step
