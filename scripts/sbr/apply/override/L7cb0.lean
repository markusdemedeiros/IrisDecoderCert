theorem blk_L7cb0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7cb0" ⟨"ff_aac_sbr_apply.L7cb0", B.L7cb0, some "ff_aac_sbr_apply.L7cbf"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hne, h12, hm⟩ := T.L7cb0.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [arg1] at h8
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hkx : y.kx1 ≤ 32 := hCy.1.2.1
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hzk := zx32n y.kx1 (by omega)
  have had32 : BitVec.ofNat 32 y.m1 + BitVec.ofNat 32 y.kx1 = BitVec.ofNat 32 (y.m1 + y.kx1) := BitVec.ofNat_add_ofNat _ _
  have hzs := zx32n (y.m1 + y.kx1) (by omega)
  have hsub := sub32z (y.m1 + y.kx1) y.kx1 (by omega) (by omega)
  have hcf := cf_sub32 (y.m1 + y.kx1) y.kx1 (by omega) (by omega)
  have hzf := zf_sub32 (y.m1 + y.kx1) y.kx1 (by omega) (by omega)
  dsimp only
  simp only [B.L7cb0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h8, hbx, h12,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [BitVec.ofInt_natCast, sw32, hzk, hzs, had32, hsub, hcf, hzf,
    Nat.add_sub_cancel, CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.from_result.Remaining.cf_mk,
    StatusFlags.zf_from_result, Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc2 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7ce4") ?_
    refine ⟨isSome_at L.L7ce4, ?_, ?_⟩
    · rw [T.L7ce4]
      refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          h8, hbx]
        done
      simp only [Mm, ApplyF, FrC, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ := hR.down
    refine ⟨?_, ?_⟩
    · rw [T.L7cbf]
      refine ⟨_, c0, _, y.kx1, y.m1, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, hst, hne, by omega, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          h8, hbx, h12]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
