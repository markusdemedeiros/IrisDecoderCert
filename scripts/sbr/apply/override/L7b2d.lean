theorem blk_L7b2d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b2d" ⟨"ff_aac_sbr_apply.L7b2d", B.L7b2d, some "ff_aac_sbr_apply.L7b50"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h13, y, hK, hCy, hst, hne, hj, hrax,
    hg, hps, hm⟩ := T.L7b2d.mp hs
  clear hs
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hpl : y.pnum.length = 6 := hT.2.2.2.2.1
  have hps1 := ps_succ (fun i => u8 y.pnum i) j y.npatch hj
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hkk : kk ≤ 64 := by omega
  have hsx := sx_kk kk (by omega)
  try dsimp only at hps1
  have hA : (y.pnum.getD j 0).toNat = 0 → kk + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 := by
    intro h0; have h0' : u8 y.pnum j = 0 := h0; omega
  have hB : kk + (u8 y.pnum j - 0) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 := by omega
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [byte_split y.pnum _ j (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax, hsx, hA, hB⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7b2d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h13, hrax,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc2 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax, hsx, hA, hB⟩ := hR.down
    rename_i hz _
    simp only [CondCode.interp_z, StatusFlags.zf_from_result, zf_byte, decide_eq_true_eq] at hz
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7c5d") ?_
    refine ⟨isSome_at L.L7c5d, ?_, ?_⟩
    · rw [T.L7c5d]
      refine ⟨_, c0, _, j, kk, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, ?_, hg, hA hz, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hsx, xz64]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, xz64]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax, hsx, hA, hB⟩ := hR.down
    rename_i hz _
    simp only [CondCode.interp_z, StatusFlags.zf_from_result, zf_byte, decide_eq_false_iff_not] at hz
    refine ⟨?_, ?_⟩
    · rw [T.L7b50]
      refine ⟨_, c0, _, j, kk, g, 0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj,
        (show 0 < (y.pnum.getD j 0).toNat by omega), hB, hg, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hsx, xz64]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, xz64]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
