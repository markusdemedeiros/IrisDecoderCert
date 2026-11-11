theorem blk_L7750_6 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_6" ⟨"ff_aac_sbr_apply.L7750_6", B.L7750_6, some "ff_aac_sbr_apply.L7750_7"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h15, hbx, y, hK, hCy, hm⟩ := T.L7750_6.mp hs
  clear hs
  have hyp := ApplyC_ypos_le hCy ch
  have PsW_ypos0 : ∀ p : Nat, PsW { y with d0 := { y.d0 with ypos := p } } t₀ = PsW y t₀ := fun _ => rfl
  have PsW_ypos1 : ∀ p : Nat, PsW { y with d1 := { y.d1 with ypos := p } } t₀ = PsW y t₀ := fun _ => rfl
  simp only [Mm, ApplyF, FrA6, DScW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  · simp only [Args.d, ↓reduceIte] at hyp
    dsimp only
    simp only [B.L7750_6]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7750_7]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_,
                     { y with d0 := { y.d0 with ypos := 1 - y.d0.ypos } }, ⟨Keep_ypos0 hK.1 _, hK.2⟩,
                     ApplyC_ypos0 hCy _ (by omega), ?_, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx, dA, ↓reduceIte,
          sbrA, arg1, BitVec.add_assoc, Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64,
          BitVec.setWidth_eq, Args.d, BitVec.toNat_ofNat, Nat.reduceEqDiff, BitVec.toNat_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl] at *
    all_goals try sep_mem hm
    all_goals try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try exact ypos_xor_rax _ hyp
    all_goals try (simp only [Mm, ApplyF, FrA6, DScW, c4, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd, FnW_ypos0, AcW_ypos0, ScW_ypos0, TabW_ypos0,
      OutW_ypos0, PsW_ypos0, ypos_xor _ hyp] at hm ⊢)
    all_goals try sep_close hm
    all_goals try simp only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero, Nat.reduceSub]
    all_goals try var_step
  · simp only [Args.d, ↓reduceIte, Nat.one_ne_zero] at hyp
    dsimp only
    simp only [B.L7750_6]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7750_7]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_,
                     { y with d1 := { y.d1 with ypos := 1 - y.d1.ypos } }, ⟨Keep_ypos1 hK.1 _, hK.2⟩,
                     ApplyC_ypos1 hCy _ (by omega), ?_, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx, dA, ↓reduceIte,
          sbrA, arg1, BitVec.add_assoc, Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64,
          BitVec.setWidth_eq, Args.d, BitVec.toNat_ofNat, Nat.reduceEqDiff, BitVec.toNat_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl] at *
    all_goals try sep_mem hm
    all_goals try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try exact ypos_xor_rax _ hyp
    all_goals try (simp only [Mm, ApplyF, FrA6, DScW, c4, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd, FnW_ypos1, AcW_ypos1, ScW_ypos1, TabW_ypos1,
      OutW_ypos1, PsW_ypos1, ypos_xor _ hyp] at hm ⊢)
    all_goals try sep_close hm
    all_goals try simp only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero, Nat.reduceSub]
    all_goals try var_step
