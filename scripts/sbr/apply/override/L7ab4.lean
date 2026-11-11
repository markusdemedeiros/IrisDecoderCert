theorem blk_L7ab4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7ab4" ⟨"ff_aac_sbr_apply.L7ab4", B.L7ab4, some "ff_aac_sbr_apply.L7b00"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, h5, hm⟩ := T.L7ab4.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7ab4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq]
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc5 =>
      rename_i hcc
      have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, sw32, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod,
        BitVec.reduceSetWidth, CondCode.interp_c, CondCode.interp_nz, StatusFlags.cf_from_result,
        StatusFlags.zf_from_result, cf_sub32 y.nq 5 (by omega) (by omega), zf_sub32 y.nq 5 (by omega) (by omega),
        decide_eq_true_eq, decide_eq_false_iff_not] at hcc
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hcc
      exfalso
      omega
    case vc6 =>
      refine ⟨?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step
