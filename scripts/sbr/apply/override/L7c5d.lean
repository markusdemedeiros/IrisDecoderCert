theorem blk_L7c5d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7c5d" ⟨"ff_aac_sbr_apply.L7c5d", B.L7c5d, some "ff_aac_sbr_apply.L7c80"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h13, y, hK, hCy, hst, hne, hj, hrax,
    hg, hps, hm⟩ := T.L7c5d.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hj1 := ofNat_succ64 j
  have hzx := zx_ofNat y.npatch (by omega)
  have hcf := cf_sub64 (j + 1) y.npatch (by omega) (by omega)
  have hzf := zf_sub64 (j + 1) 6 (by omega) (by omega)
  have hkk : kk ≤ 64 := by omega
  dsimp only
  simp only [B.L7c5d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h13, hrax,
      BitVec.add_assoc, BitVec.setWidth_eq, hj1, hzx] at *
  all_goals try simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, StatusFlags.zf_from_result, hcf, hzf, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc1 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L8b4f") ?_
    refine ⟨isSome_at L.L8b4f, ?_, ?_⟩
    · rw [T.L8b4f]
      refine ⟨_, c0, _, kk, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, hst, hne, hkk, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hj1, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hj1]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc2 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax⟩ := hR.down
    rename_i hz hc
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b2d") ?_
    refine ⟨isSome_at L.L7b2d, ?_, ?_⟩
    · rw [T.L7b2d]
      refine ⟨_, c0, _, j + 1, kk, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, by omega, ?_,
        hg, hps, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hj1, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hj1]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc3 =>
    exfalso
    rename_i hz hc
    omega
