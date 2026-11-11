theorem blk_L879e_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L879e_2" ⟨"ff_aac_sbr_apply.L879e_2", B.L879e_2, none⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC0, ⟨hrsp, hrbp⟩, y, ch, c0, j, hK, hC, hc0, hch, h_rbx, hm⟩ := T.L879e_2.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, FrM0, sbrA, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    Nat.reduceMul, Nat.reduceAdd] at hm
  have hm0 := hm
  dsimp only
  simp only [B.L879e_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals mapb_name
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h_rbx]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, z, hrsp, hrbp] at ld1
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at ld1
  all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1; done) | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try omega
  -- exit to L9927 (shared boundary, FrCs)
  all_goals try (goal_has_str "ff_aac_sbr_apply.L9927"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9927") ?_; refine ⟨isSome_at L.L9927, ?_, ?_⟩; rw [T.L9927]; refine ⟨hC0, ?_, ch, c0, hch, hc0, ?_, y.spSet, ⟨hK.1, hK.2.spSet⟩, hC.spSet, ?_⟩ <;> try and_intros)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h_rbx]; done)
  all_goals try (simp only [Mm, ApplyF, show TabW y.spSet t₀ = TabW y t₀ from rfl, show PsW y.spSet t₀ = PsW y t₀ from rfl, show FnW e y.spSet t₀ = FnW e y t₀ from rfl, show AcW y.spSet t₀ = AcW y t₀ from rfl, show OutW y.spSet t₀ = OutW y t₀ from rfl]; simp only [Mm, ApplyF, ScW, Args.spSet, FrCs, FrM0, sbrA, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat,
    Nat.reduceMul, Nat.reduceAdd]; (have es32 : BitVec.setWidth 32 4294967295#64 = BitVec.allOnes 32 := by decide); (have es16 : BitVec.setWidth 16 65535#64 = BitVec.allOnes 16 := by decide); simp only [es32, es16] at hm; sep_close hm; done)
  all_goals try (mapb_head Or; left; ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rbx]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
  all_goals try (((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rbx]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
