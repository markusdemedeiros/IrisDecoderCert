theorem blk_L7bb3_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb3_2" ⟨"ff_aac_sbr_apply.L7bb3_2", B.L7bb3_2, some "ff_aac_sbr_apply.L7c5d"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hg, hm⟩ := T.L7bb3_2.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hpl : y.pnum.length = 6 := hT.2.2.2.2.1
  have hP : u8 y.pstart j + u8 y.pnum j ≤ 32 := hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [byte_split y.pnum _ j (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at hbx
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h15, h12, h14, h13⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hk1 := ofNat_succ64 kk
  have hzx := zx32 y.npatch (by omega)
  have hb256 : (y.pnum.getD j 0).toNat < 256 := UInt8.toNat_lt _
  have hx1 : BitVec.ofNat 32 xx + 1#32 = BitVec.ofNat 32 (xx + 1) := BitVec.ofNat_add_ofNat _ _
  have hzx1 := zx32n (xx + 1) (by omega)
  have hzb := zx32n (y.pnum.getD j 0).toNat (by omega)
  have hcf := cf_sub32 (xx + 1) (y.pnum.getD j 0).toNat (by omega) (by omega)
  dsimp only
  simp only [B.L7bb3_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h15, h12, h14, h13,
      BitVec.add_assoc, BitVec.setWidth_eq, hk1, hzx] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [sw32, hx1, hzx1, sw_byte32, hzb, hcf, CondCode.interp_c, StatusFlags.cf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, hbx, h15, h12, h14, h13⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b50") ?_
    refine ⟨isSome_at L.L7b50, ?_, ?_⟩
    · rw [T.L7b50]
      refine ⟨_, c0, _, j, kk + 1, g, xx + 1, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj,
        (by (try simp only [u8] at *); omega), (by (try simp only [u8] at *); omega), (by (try simp only [u8] at *); omega), ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, hbx,
          h15, h12, h14, h13, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hzx1]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc5 =>
    obtain ⟨hrsp, hrbp, hsl, hn, hbx, h15, h12, h14, h13⟩ := hR.down
    have hzx := zx32 y.npatch (by omega)
    refine ⟨?_, ?_⟩
    · rw [T.L7c5d]
      refine ⟨_, c0, _, j, kk + 1, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, ?_,
        (by (try simp only [u8] at *); omega), (by (try simp only [u8] at *); omega), ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, hbx,
          h15, h12, h14, h13, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hzx1]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
