theorem blk_L7b80 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b80" ⟨"ff_aac_sbr_apply.L7b80", B.L7b80, some "ff_aac_sbr_apply.L7bb0"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, xx, gg, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, hdx, hsi, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hax, hgg, hcx, h13, hm⟩ := T.L7b80.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hmul : BitVec.ofNat 64 gg * 2#64 = BitVec.ofNat 64 (2 * gg) := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have hz6 := zf_sub64 6 gg (by omega) (by omega)
  have hzq := zf_sub64 (y.nq + 1) (gg + 1) (by omega) (by omega)
  have hs1 := ofNat_succ64 gg
  have hnl : y.ftNoise.length = 12 := (hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst).2.2.1
  rw [word_split y.ftNoise _ gg (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478214#64 (BitVec.ofNat 64 (2 * gg))] at hm
  dsimp only
  simp only [B.L7b80]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, hdx, hsi, hax,
      hcx, h13, BitVec.add_assoc, BitVec.setWidth_eq, AddrIndex.offset64_scale2, hmul, hs1] at *
  all_goals try simp only [CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, hz6, hzq,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc1 =>
    exfalso
    rename_i h6
    omega
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7bb0") ?_
    refine ⟨isSome_at L.L7bb0, ?_, ?_⟩
    · rw [T.L7bb0]
      refine ⟨_, c0, _, j, kk, xx, gg, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx, hkk,
        ?_, hgg, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, hdx, hsi, hax, hcx, h13, hs1]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [word_split y.ftNoise _ gg (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478214#64 (BitVec.ofNat 64 (2 * gg))]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14, hcx, hdx, hs1]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, hcx, hdx, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ := hR.down
    rename_i _ hq _ _
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b80") ?_
    refine ⟨isSome_at L.L7b80, ?_, ?_⟩
    · rw [T.L7b80]
      refine ⟨_, c0, _, j, kk, xx, gg + 1, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj,
        hxx, hkk, ?_, by omega, ?_, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, hdx, hsi, hax, hcx, h13, hs1]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [word_split y.ftNoise _ gg (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478214#64 (BitVec.ofNat 64 (2 * gg))]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14, hcx, hdx, hs1]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, hcx, hdx, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc5 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ := hR.down
    rename_i h1 hq h3 h4
    have hq' : y.nq + 1 = gg + 1 := by
      by_cases hd : y.nq + 1 = gg + 1
      · exact hd
      · simp only [hd, decide_false, Bool.not_false] at hq
        exact absurd hq (by decide)
    have hF2 : u16 y.ftNoise y.nq = y.kx1 + y.m1 :=
      (hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exfalso
    clear hm hR hn
    have hbv : ∀ b0 b1 : UInt8, BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (Int.ofBytes [b0, b1])))
        = BitVec.ofNat 64 (b0.toNat + 256 * b1.toNat) := by
      intro b0 b1
      apply BitVec.eq_of_toNat_eq
      have ha := b0.toNat_lt
      have hb := b1.toNat_lt
      simp only [Int.ofBytes, List.foldr, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    have hu : (y.ftNoise.getD (2 * gg) 0).toNat + 256 * (y.ftNoise.getD (2 * gg + 1) 0).toNat
        = y.kx1 + y.m1 := by
      rw [show gg = y.nq by omega]; exact hF2
    rw [CondCode.interp_l_cmp, hbv, hu] at h4
    simp only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_false_iff_not] at h4
    split at h4 <;> split at h4 <;> omega
