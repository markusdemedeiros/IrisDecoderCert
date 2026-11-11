theorem blk_L879e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L879e" ⟨"ff_aac_sbr_apply.L879e", B.L879e, some "ff_aac_sbr_apply.L879e_1"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC0, ⟨hrsp, hrbp⟩, y, ch, c0, j, hK, hC, hc0, hst, hch, hj, h_rbx, hm⟩ := T.L879e.mp hs
  clear hs
  simp only [Mm, ApplyF, AcW, FnW, FrM0, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  have hm0 := hm
  dsimp only
  simp only [B.L879e]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try subst_vars
  all_goals try dsimp only
  all_goals mapb_name
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, z, hrsp, hrbp]
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, z, hrsp, hrbp] at ld1
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1; done) | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, arg0, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, arg0, BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try all_goals try (revert ld2; sep_mem hm; all_goals (first | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2; done) | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
  all_goals try (sep_mem hm; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, z, hrsp, hrbp]; sep_mem hm; done)
  refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
  rotate_left 2
  · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
    sep_mem hm
  · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
    sep_mem hm
    sep_close hm
  · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
    obtain ⟨hrsp', hrbp', hsv, hm1⟩ := hpost
    have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
      intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    rotate_left
    · ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp', hrbp', hrsp, hrbp]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm1); (try sep_mem hm); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_le; (repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)); first | exact Nat.le_refl _ | ((with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
    rw [T.L879e_1]
    refine ⟨hC0, ⟨hrsp', hrbp'⟩, y, ch, c0, j, hK, hC, hc0, hst, hch, hj, ?_, ?_⟩
    · first
      | (rw [hsv.1]; exact h_rbx)
      | (simp only [hsv, MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; exact h_rbx)
    simp only [Mm, ApplyF, AcW, FnW, FrM0, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd]
    rw [call_res k hSt]
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_close hm1
