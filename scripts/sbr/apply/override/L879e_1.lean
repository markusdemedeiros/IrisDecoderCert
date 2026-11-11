theorem blk_L879e_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L879e_1" ⟨"ff_aac_sbr_apply.L879e_1", B.L879e_1, some "ff_aac_sbr_apply.L879e_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC0, ⟨hrsp, hrbp⟩, y, ch, c0, j, hK, hC, hc0, hst, hch, hj, h_rbx, hm⟩ := T.L879e_1.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, DScW, FrM0, sbrA, dA, Args.d, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd] at hm
  -- the 8-byte store covers `start` and `ready`: merge the two cells
  sep_pull hm [cell4 (t₀.regs.get64 .rsi + 0x28924#64) y.start,
    cell4 (t₀.regs.get64 .rsi + 0x28928#64) y.ready] as R hR
  rw [← Std.ExtHashMap.sep_assoc, ← Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  have hm0 := hm
  dsimp only
  simp only [B.L879e_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try (rename_i v hv; simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
    Width.bytes, hrbp, z, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv)
  all_goals try (simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at hv)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  refine ⟨?_, ?_⟩
  rotate_left
  · ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rbx]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_le; (repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)); first | exact Nat.le_refl _ | ((with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
  rw [T.L879e_2]
  refine ⟨hC0, ⟨?_, ?_⟩, y.turnoff, ch, c0, j, ⟨Args.Keep.turnoff hK.1, hK.2.turnoff⟩, hC.turnoff, hc0, hch, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h_rbx, arg1]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h_rbx, dA, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  have h8 : Int.toBytes 8 (BitVec.setWidth 64 0#64).toInt
      = Int.toBytes 4 (0#32).toInt ++ Int.toBytes 4 (0#32).toInt := by decide
  have e0 : (BitVec.setWidth 32 0#64).toInt = ((0 : Nat) : Int) := by decide
  have e32 : (BitVec.setWidth 32 32#64).toInt = ((32 : Nat) : Int) := by decide
  rw [h8, Val.append_eq _ _ _ (t₀.regs.get64 .rsi + 166184#64) (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  simp only [e0, e32] at hm
  have hT : TabW y.turnoff t₀ = TabW y t₀ := rfl
  have hF : FnW e y.turnoff t₀ = FnW e y t₀ := rfl
  have hA : AcW y.turnoff t₀ = AcW y t₀ := rfl
  have hO : OutW y.turnoff t₀ = OutW y t₀ := rfl
  have hP : PsW y.turnoff t₀ = PsW y t₀ := rfl
  have hD0 : DScW y.turnoff.d0 t₀ 0 = DScW y.d0 t₀ 0 := rfl
  have hD1 : DScW y.turnoff.d1 t₀ 1 = DScW y.d1 t₀ 1 := rfl
  simp only [Mm, ApplyF, hT, hF, hA, hO, hP, hD0, hD1]
  simp only [ScW, DScW, FrM0, sbrA, dA, Args.d, Args.turnoff, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd]
  sep_close hm
