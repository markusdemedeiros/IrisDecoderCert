theorem blk_L7682_7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_7" ⟨"ff_aac_sbr_apply.L7682_7", B.L7682_7, some "ff_aac_sbr_apply.L7682_8"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMc, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h12, hbx, h13, y, hK, hCy, h15, hm⟩ := T.L7682_7.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, DArrW, OutW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hds : 4096 ≤ 8192 >>> dsN y := by unfold dsN; split <;> decide
  -- memcpy(x + 0x480, L/R, 0x1000): the destination carved from the analysis block
  -- (d + 0x2480, 5248), the source from the output block (L or R, 8192 >>> dsN)
  have hD := Block.carve (a := dA t₀ ch + 0x2480#64) (b := dA t₀ ch + 0x2900#64) (len := 5248) (n := 4096)
    (by simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff])
    (by decide)
  have hL : ∀ a : BitVec 64, (8192 >>> dsN y) ?@ a
      = 4096 ?@ a ⋆ (0 ?@ a ⋆ (8192 >>> dsN y - 0 - 4096) ?@ (a + BitVec.ofNat 64 4096)) := by
    intro a
    have h := Block.carve (a := a) (b := a) (len := 8192 >>> dsN y) (n := 4096)
      (by simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hds)
      (by unfold dsN; split <;> decide)
    simpa only [BitVec.sub_self, BitVec.toNat_zero] using h
  have hA : ∀ a c : BitVec 64, (10496#64) + (a + c) = a + (10496#64 + c) := by intro a c; ac_rfl
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hD hm
    rw [hD, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    first
      | (rw [hL (arg3 t₀)] at hm
         simp only [arg3, arg4] at hm
         have hm0 := hm
         sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          4096 ?@ (t₀.regs.get64 .rsi + 176800#64), 4096 ?@ t₀.regs.get64 .rcx] as Rc hRc)
      | (rw [hL (arg4 t₀)] at hm
         simp only [arg3, arg4] at hm
         have hm0 := hm
         sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          4096 ?@ (t₀.regs.get64 .rsi + 265568#64), 4096 ?@ t₀.regs.get64 .r8] as Rc hRc)
    have hRc' := PLift.up hRc
    clear hRc
    dsimp only
    simp only [B.L7682_7]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen [MachineWP.call_proc_spec_at Rc "memcpy" hMc]
    all_goals try subst_vars
    case vc1 =>
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
      sep_mem hm0
    case vc2 =>
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul] at *
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
      sep_vals hm0
      try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, ↓reduceIte, Nat.one_ne_zero] at *
      sep_mem hm0
    case vc3 =>
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul] at *
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
      sep_vals hm0
      try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, ↓reduceIte, Nat.one_ne_zero] at *
      sep_vals hm0
      try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, ↓reduceIte, Nat.one_ne_zero] at *
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
      rotate_left 2
      · try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
        sep_mem hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
        sep_mem hm
        try (rw [hA]; simp only [BitVec.reduceAdd])
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth] at hpost
        obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        try (rw [hA] at hm'; simp only [BitVec.reduceAdd] at hm')
        try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hrsp'
        have e := hRc'.down
        subst e
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨?_, ?_⟩
        · rw [T.L7682_8]
          refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
          all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, hbx', h12', h13', h14', h15', Args.d, ↓reduceIte, Nat.one_ne_zero]; done)
          simp only [Mm, ApplyF, FrA6, DArrW, OutW, Blocks, ↓reduceIte, Nat.one_ne_zero, dA, sbrA, arg0, arg1,
            BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]
          rw [hD, call_res k hSt]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
          simp only [ite_true, ite_false, ↓reduceIte, Nat.one_ne_zero, dsN] at hm'
          first
            | (rw [hL (arg3 t₀)]; simp only [arg3, arg4, dsN]; sep_close hm')
            | (rw [hL (arg4 t₀)]; simp only [arg3, arg4, dsN]; sep_close hm')
        · try simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_mem hm'
          simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
          var_step
