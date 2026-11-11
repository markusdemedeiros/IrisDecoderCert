theorem blk_L7b50 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b50" ⟨"ff_aac_sbr_apply.L7b50", B.L7b50, some "ff_aac_sbr_apply.L7b80"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hg, hm⟩ := T.L7b50.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hpl : y.pstart.length = 6 := hT.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [byte_split y.pstart _ j (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478298#64 (BitVec.ofNat 64 j)] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hzq := zx32 y.nq (by omega)
  have hzg := zx_ofNat g (by omega)
  have hzg' := zx32n g (by omega)
  have hz13 := zx_ofNat (y.nq + 1) (by omega)
  have hs1 := ofNat_succ64 y.nq
  have hsg := sw32 g
  have hsq := sw32 y.nq
  have hcf := cf_sub32 g y.nq (by omega) (by omega)
  have hzf := zf_sub32 g y.nq (by omega) (by omega)
  have hcf7 := cf_sub64 g 7 (by omega) (by omega)
  have hg7 : decide (g < 7) = true := by simp only [decide_eq_true_eq]; omega
  have h6 : BitVec.setWidth 64 (BitVec.setWidth 32 6#64) = 6#64 := rfl
  dsimp only
  simp only [B.L7b50]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, h13,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [hzq, hzg, hs1, hz13, hsg, hsq, hzg', zx_byte, h6] at *
  all_goals try simp only [CondCode.interp_nc, CondCode.interp_a, StatusFlags.cf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, StatusFlags.zf_from_result, hcf, hzf, hcf7, hg7, Bool.not_true,
    Bool.false_eq_true, ite_false] at *
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13⟩ := hR.down
    rename_i hz
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7bb3") ?_
    refine ⟨isSome_at L.L7bb3, ?_, ?_⟩
    · rw [T.L7bb3]
      refine ⟨_, c0, _, j, kk, g, xx, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx, hkk,
        ?_, hg, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, h13, hzq, hzg, hs1, hz13, hzg', zx_byte, h6, hcf7, hg7, Bool.not_true, Bool.false_eq_true]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pstart _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478298#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13⟩ := hR.down
    rename_i hz
    have hgq : g < y.nq + 1 := by
      refine (Nat.lt_or_ge g (y.nq + 1)).elim id fun hc => ?_
      exfalso
      have h1 : decide (g < y.nq) = false := by simp only [decide_eq_false_iff_not]; omega
      have h2 : decide (g = y.nq) = false := by simp only [decide_eq_false_iff_not]; omega
      simp only [h1, h2] at hz
      exact absurd hz (by decide)
    refine ⟨?_, ?_⟩
    · rw [T.L7b80]
      refine ⟨_, c0, _, j, kk, xx, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx,
        hkk, ?_, hgq, ?_, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, h13, hzq, hzg, hs1, hz13, hzg', zx_byte, h6, hcf7, hg7, Bool.not_true, Bool.false_eq_true]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pstart _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478298#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
