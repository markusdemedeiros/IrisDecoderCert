theorem blk_L7682_5 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_5" ⟨"ff_aac_sbr_apply.L7682_5", B.L7682_5, some "ff_aac_sbr_apply.L7682_6"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMc, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h9, h14, h13, hcx, hdi, y, hK, hCy, hm⟩ := T.L7682_5.mp hs
  clear hs
  have hyp := ApplyC_ypos_le hCy ch
  simp only [Mm, ApplyF, FrA5, DArrW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hcx
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  -- memcpy(x, x + 0x1000, 0x480) inside the analysis block (d + 0x2480, 5248)
  obtain ⟨H, hH⟩ := Block.carve2_ex (a := dA t₀ ch + 0x2480#64) (b₁ := dA t₀ ch + 0x2480#64)
    (b₂ := dA t₀ ch + 0x3480#64) (len := 5248) (n₁ := 1152) (n₂ := 1152)
    (by simp only [BitVec.sub_self, Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat,
          BitVec.toNat_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff])
    (by simp only [BitVec.sub_self, Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat,
          BitVec.toNat_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff])
    (by decide)
  have hsx : ∀ p : Nat, p ≤ 1 → BitVec.signExtend 64 (BitVec.ofInt 32 (p : Int)) = BitVec.ofNat 64 p := by
    intro p hp; rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rfl
  have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
      a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
    intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hH hm
    rw [hH, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    simp only [DScW, Args.d, ↓reduceIte, Nat.one_ne_zero, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
      Nat.reduceMul, Nat.reduceAdd] at hm hyp
    first
      | have hyl : loadInt s₀.dmem (t₀.regs.get64 .rsi + 197312#64) 4 = some (y.d0.ypos : Int) := by
          sep_mem hm; rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by simp only [Nat.reduceMul, Nat.reducePow]; omega)]
      | have hyl : loadInt s₀.dmem (t₀.regs.get64 .rsi + 286080#64) 4 = some (y.d1.ypos : Int) := by
          sep_mem hm; rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by simp only [Nat.reduceMul, Nat.reducePow]; omega)]
    first
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          1152 ?@ (t₀.regs.get64 .rsi + 175648#64), 1152 ?@ (t₀.regs.get64 .rsi + 179744#64)] as Rc hRc
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          1152 ?@ (t₀.regs.get64 .rsi + 264416#64), 1152 ?@ (t₀.regs.get64 .rsi + 268512#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    dsimp only
    simp only [B.L7682_5]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen [MachineWP.call_proc_spec_at Rc "memcpy" hMc]
    all_goals try subst_vars
    case vc1 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
      simp only [hyl, Option.isSome_some]
    case vc2 =>
      rename_i v hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul] at hv
      rw [hyl, Option.some.injEq] at hv
      subst hv
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
      rotate_left 2
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
        sep_mem hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
        sep_mem hm
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth] at hpost
        obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hrsp'
        have e := hRc'.down
        subst e
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨?_, ?_⟩
        · rw [T.L7682_6]
          refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
          all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, hbx', h12', h13', h14', h15', hsx _ hyp, Args.d, ↓reduceIte, Nat.one_ne_zero]; done)
          simp only [Mm, ApplyF, FrA5, DArrW, DScW, Blocks, Args.d, ↓reduceIte, Nat.one_ne_zero, dA, sbrA, arg0, arg1, arg3, arg4,
            BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]
          rw [hH, call_res k hSt]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_close hm'
        · simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_mem hm'
          simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
          var_step
