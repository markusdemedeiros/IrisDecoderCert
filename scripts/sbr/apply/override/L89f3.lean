theorem blk_L89f3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L89f3" ⟨"ff_aac_sbr_apply.L89f3", B.L89f3, some "ff_aac_sbr_apply.L89f3_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, j, p, hK, hCy, hc0, hst, hch, hf0, hrsi, hr14, hr12, hr8, hrdi, hf6, hrbx, hrcx, hm⟩ := T.L89f3.mp hs
  clear hs
  obtain ⟨hn1, hn8, hm1, hm48, hk32, hkm, hte, hmono, hfr, htl, hfl⟩ := env_wf hCy hst hch (hK.2.live hst)
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have e22 : 2 * p + 2 = 2 * (p + 1) := by omega
  have e23 : 2 * p + 2 + 1 = 2 * (p + 1) + 1 := by omega
  have e33 : 2 * p + 3 = 2 * (p + 1) + 1 := by omega
  have hls : ∀ (m : Mem 64) (r : BitVec 64) (c d n : Nat) (v : Int), c + 8 ≤ d → d < 2 ^ 32 → n ≤ 8 → (m.storeInt (r - BitVec.ofNat 64 c) n v).loadInt (r - BitVec.ofNat 64 d) 8 = m.loadInt (r - BitVec.ofNat 64 d) 8 := by
    intro m r c d n v h1 h2 h3
    apply Mem.loadInt_storeInt_of_above
    all_goals rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (2 ^ 64 - (d - c)) by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega, BitVec.toNat_ofNat]
    all_goals omega
  have hfz01 : u8 (y.d ch).freqRes (j + 1) = 0 ∨ u8 (y.d ch).freqRes (j + 1) = 1 := by have := hfr (j + 1) (by omega); omega
  obtain ⟨hfl50, hfl98⟩ := env_ftlen hCy hst
  have htb := env_tab hCy hst (u8 (y.d ch).freqRes (j + 1) = 0) 0 (by omega)
  have hch01 : ch = 0 ∨ ch = 1 := by omega
  simp only [B.L89f3]
  vcgen
  all_goals obtain hfz | hfz := hfz01
  all_goals try simp only [hfz, ↓reduceIte, Nat.one_ne_zero, ite_true, ite_false] at hm htb hf0 hrsi hr14 hr12 hr8 hrdi hf6 hrbx hrcx ⊢
  all_goals obtain rfl | rfl := hch01
  all_goals simp only [FrN, Mm, ApplyF, TabW, dA, sbrA, arg1, Args.d, Nat.one_ne_zero, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hf0 hrsi hr14 hr12 hr8 hrdi hf6 hrbx hrcx hn1 hn8 hte hmono hfr htl hfl ⊢
  all_goals try simp only [u8, u16] at hf0 hrsi hr14 hr12 hr8 hrdi hf6 hrbx hrcx hte hmono hfr
  all_goals try dsimp only
  all_goals have hm00 := hm
  all_goals have hm0 := hm
  all_goals try simp only [c8, c4] at hm0
  all_goals try subst_vars
  all_goals env_name
  all_goals try simp only [u8, u16, Args.d, ↓reduceIte, ite_true, ite_false, Nat.one_ne_zero] at hfz
  all_goals try simp only [u8, u16, Args.d, ↓reduceIte, ite_true, ite_false, Nat.one_ne_zero] at htb
  all_goals try simp only [u8, u16, Args.d, ↓reduceIte, ite_true, ite_false, Nat.one_ne_zero] at htp1
  all_goals try simp only [u8, u16, Args.d, ↓reduceIte, ite_true, ite_false, Nat.one_ne_zero] at htp2
  all_goals try simp only [hfz, ↓reduceIte, Nat.one_ne_zero, ite_true, ite_false] at ld1
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at ld1
  all_goals try simp only [hfz, ↓reduceIte, Nat.one_ne_zero, ite_true, ite_false] at ld2
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try simp only [hfz, ↓reduceIte, Nat.one_ne_zero, ite_true, ite_false] at ld3
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at ld3
  all_goals try simp only [hfz, ↓reduceIte, Nat.one_ne_zero, ite_true, ite_false] at ⊢
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at ⊢
  all_goals try have hteJ := hte (j) (by omega)
  all_goals try have hfrJ := hfr (j) (by omega)
  all_goals try have hteJ1 := hte (j + 1) (by omega)
  all_goals try have hfrJ1 := hfr (j + 1) (by omega)
  all_goals try have hmoJ := hmono j (by omega)
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast] at ld1
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.zero_add, BitVec.add_assoc, BitVec.reduceAdd] at ld1
  all_goals try simp (disch := omega) only [env_ab (b := 478066) (c := 478116), env_ab (b := 478116) (c := 478216), env_ab' (b := 478066) (c := 478116), env_ab' (b := 478116) (c := 478216), Nat.reduceSub, Nat.zero_add, BitVec.add_assoc] at ld1
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld1
  all_goals try simp (disch := decide) only [env_ra4, Nat.reduceAdd] at ld1
  all_goals try simp (disch := decide) only [env_ra3] at ld1
  all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | (simp only [Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1]; done) | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast] at ld2
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.zero_add, BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try simp (disch := omega) only [env_ab (b := 478066) (c := 478116), env_ab (b := 478116) (c := 478216), env_ab' (b := 478066) (c := 478116), env_ab' (b := 478116) (c := 478216), Nat.reduceSub, Nat.zero_add, BitVec.add_assoc] at ld2
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try simp (disch := decide) only [env_ra4, Nat.reduceAdd] at ld2
  all_goals try simp (disch := decide) only [env_ra3] at ld2
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast] at ld3
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.zero_add, BitVec.add_assoc, BitVec.reduceAdd] at ld3
  all_goals try simp (disch := omega) only [env_ab (b := 478066) (c := 478116), env_ab (b := 478116) (c := 478216), env_ab' (b := 478066) (c := 478116), env_ab' (b := 478116) (c := 478216), Nat.reduceSub, Nat.zero_add, BitVec.add_assoc] at ld3
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
  all_goals try simp (disch := decide) only [env_ra4, Nat.reduceAdd] at ld3
  all_goals try simp (disch := decide) only [env_ra3] at ld3
  all_goals try sep_vals hm0
  all_goals try simp only [env_sub_base, BitVec.toNat_ofNat]
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt]
  all_goals try simp (disch := omega) only [env_take1, env_take2]
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv]
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.zero_add, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try simp (disch := omega) only [env_shl4, env_sx, env_lea5_shl6, env_lea3_shl4, env_sw, env_u8bv', env_u8bv]
  all_goals try simp (disch := decide) only [env_ra, env_ra2]
  all_goals try dsimp only
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1]; done)
  all_goals try ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv]
  all_goals try simp only [env_sub_base, BitVec.toNat_ofNat] at cc1
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc1
  all_goals try simp (disch := omega) only [env_take1, env_take2] at cc1
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc1
  all_goals try (dsimp only at cc1)
  all_goals try (rw [CondCode.interp_a_sub] at cc1; rotate_left; rfl)
  all_goals try (rw [CondCode.interp_be_sub] at cc1; rotate_left; rfl)
  all_goals try (rw [env_nc_sub] at cc1; rotate_left; rfl)
  all_goals try (rw [env_c_sub] at cc1; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx] at cc1
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, BitVec.and_self] at cc1
  all_goals try simp only [BitVec.toNat_eq, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast] at cc1
  all_goals try simp only [env_sub_base, BitVec.toNat_ofNat] at cc2
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc2
  all_goals try simp (disch := omega) only [env_take1, env_take2] at cc2
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc2
  all_goals try (dsimp only at cc2)
  all_goals try (rw [CondCode.interp_a_sub] at cc2; rotate_left; rfl)
  all_goals try (rw [CondCode.interp_be_sub] at cc2; rotate_left; rfl)
  all_goals try (rw [env_nc_sub] at cc2; rotate_left; rfl)
  all_goals try (rw [env_c_sub] at cc2; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx] at cc2
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, BitVec.and_self] at cc2
  all_goals try simp only [BitVec.toNat_eq, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast] at cc2
  all_goals try simp only [env_sub_base, BitVec.toNat_ofNat] at cc3
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc3
  all_goals try simp (disch := omega) only [env_take1, env_take2] at cc3
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc3
  all_goals try (dsimp only at cc3)
  all_goals try (rw [CondCode.interp_a_sub] at cc3; rotate_left; rfl)
  all_goals try (rw [CondCode.interp_be_sub] at cc3; rotate_left; rfl)
  all_goals try (rw [env_nc_sub] at cc3; rotate_left; rfl)
  all_goals try (rw [env_c_sub] at cc3; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx] at cc3
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, BitVec.and_self] at cc3
  all_goals try simp only [BitVec.toNat_eq, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast] at cc3
  all_goals try simp only [env_sub_base, BitVec.toNat_ofNat] at cc4
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc4
  all_goals try simp (disch := omega) only [env_take1, env_take2] at cc4
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc4
  all_goals try (dsimp only at cc4)
  all_goals try (rw [CondCode.interp_a_sub] at cc4; rotate_left; rfl)
  all_goals try (rw [CondCode.interp_be_sub] at cc4; rotate_left; rfl)
  all_goals try (rw [env_nc_sub] at cc4; rotate_left; rfl)
  all_goals try (rw [env_c_sub] at cc4; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx] at cc4
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, BitVec.and_self] at cc4
  all_goals try simp only [BitVec.toNat_eq, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast] at cc4
  all_goals try (obtain ⟨htb1, htb2, htb3, htb4⟩ := htb)
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast] at ld2
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.zero_add, BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try simp (disch := omega) only [env_ab (b := 478066) (c := 478116), env_ab (b := 478116) (c := 478216), env_ab' (b := 478066) (c := 478116), env_ab' (b := 478116) (c := 478216), Nat.reduceSub, Nat.zero_add, BitVec.add_assoc] at ld2
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try simp (disch := decide) only [env_ra4, Nat.reduceAdd] at ld2
  all_goals try simp (disch := decide) only [env_ra3] at ld2
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast] at ld3
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
  all_goals try simp only [BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.add_zero, BitVec.zero_add, BitVec.add_assoc, BitVec.reduceAdd] at ld3
  all_goals try simp (disch := omega) only [env_ab (b := 478066) (c := 478116), env_ab (b := 478116) (c := 478216), env_ab' (b := 478066) (c := 478116), env_ab' (b := 478116) (c := 478216), Nat.reduceSub, Nat.zero_add, BitVec.add_assoc] at ld3
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
  all_goals try simp (disch := decide) only [env_ra4, Nat.reduceAdd] at ld3
  all_goals try simp (disch := decide) only [env_ra3] at ld3
  all_goals try ((have _hg : (_ : Nat) = 0 := hfz); refine (fun (e_ld2 : _ = Int.ofBytes (List.take 2 (List.drop (2 * (p + 1)) y.ftLow))) => ?_) (Option.some.inj (ld2.symm.trans ?_)); rotate_left; focus (sep_mem hm00; all_goals (first | omega | (simp only [env_sub_base, BitVec.toNat_ofNat]; omega) | (simp only [env_sub_base, BitVec.toNat_ofNat]; congr; all_goals omega)); done); all_goals (try subst e_ld2))
  all_goals try ((have _hg : (_ : Nat) = 1 := hfz); refine (fun (e_ld2 : _ = Int.ofBytes (List.take 2 (List.drop (2 * (p + 1)) y.ftHigh))) => ?_) (Option.some.inj (ld2.symm.trans ?_)); rotate_left; focus (sep_mem hm00; all_goals (first | omega | (simp only [env_sub_base, BitVec.toNat_ofNat]; omega) | (simp only [env_sub_base, BitVec.toNat_ofNat]; congr; all_goals omega)); done); all_goals (try subst e_ld2))
  all_goals try ((have _hg : (_ : Nat) = 0 := hfz); refine (fun (e_ld3 : _ = Int.ofBytes (List.take 2 (List.drop (2 * p) y.ftLow))) => ?_) (Option.some.inj (ld3.symm.trans ?_)); rotate_left; focus (sep_mem hm00; all_goals (first | omega | (simp only [env_sub_base, BitVec.toNat_ofNat]; omega) | (simp only [env_sub_base, BitVec.toNat_ofNat]; congr; all_goals omega)); done); all_goals (try subst e_ld3))
  all_goals try ((have _hg : (_ : Nat) = 1 := hfz); refine (fun (e_ld3 : _ = Int.ofBytes (List.take 2 (List.drop (2 * p) y.ftHigh))) => ?_) (Option.some.inj (ld3.symm.trans ?_)); rotate_left; focus (sep_mem hm00; all_goals (first | omega | (simp only [env_sub_base, BitVec.toNat_ofNat]; omega) | (simp only [env_sub_base, BitVec.toNat_ofNat]; congr; all_goals omega)); done); all_goals (try subst e_ld3))
  all_goals try subst e_ld2
  all_goals try subst e_ld3
  all_goals try simp (disch := omega) only [env_u16g] at cc2
  all_goals try sep_vals hm0
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv]
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp (disch := omega) only [env_drop2]
  all_goals try simp (disch := omega) only [env_u16bv]
  all_goals try simp only [env_sw16]
  all_goals try simp (disch := omega) only [env_off, env_off']
  all_goals try simp (disch := omega) only [env_u16a, env_u16b]
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self]
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g]
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33]
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self] at cc2
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g] at cc2
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33] at cc2
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self] at cc3
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g] at cc3
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33] at cc3
  all_goals try omega
  all_goals try simp only [env_sw16c]
  all_goals try omega
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc1
  all_goals try simp (disch := omega) only [env_u16bv] at cc1
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc1
  all_goals try simp only [env_mod16] at cc1
  all_goals try simp (disch := omega) only [env_u16] at cc1
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc2
  all_goals try simp (disch := omega) only [env_u16bv] at cc2
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc2
  all_goals try simp only [env_mod16] at cc2
  all_goals try simp (disch := omega) only [env_u16] at cc2
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc3
  all_goals try simp (disch := omega) only [env_u16bv] at cc3
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc3
  all_goals try simp only [env_mod16] at cc3
  all_goals try simp (disch := omega) only [env_u16] at cc3
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt, BitVec.ofInt_natCast, Mem.sub_add_add_lit, BitVec.sub_self, BitVec.reduceSub, BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.reduceMod, Nat.reducePow, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLeDiff, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, env_ob1, env_u8bv] at cc4
  all_goals try simp (disch := omega) only [env_u16bv] at cc4
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc4
  all_goals try simp only [env_mod16] at cc4
  all_goals try simp (disch := omega) only [env_u16] at cc4
  all_goals try have hte0 := hte 0 (by omega)
  all_goals try (have hmo0 := hmono 0 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo0)
  all_goals try have hte1 := hte 1 (by omega)
  all_goals try (have hmo1 := hmono 1 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo1)
  all_goals try have hte2 := hte 2 (by omega)
  all_goals try (have hmo2 := hmono 2 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo2)
  all_goals try have hte3 := hte 3 (by omega)
  all_goals try (have hmo3 := hmono 3 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo3)
  all_goals try have hte4 := hte 4 (by omega)
  all_goals try (have hmo4 := hmono 4 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo4)
  all_goals try have hte5 := hte 5 (by omega)
  all_goals try (have hmo5 := hmono 5 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo5)
  all_goals try have hte6 := hte 6 (by omega)
  all_goals try (have hmo6 := hmono 6 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo6)
  all_goals try have hte7 := hte 7 (by omega)
  all_goals try (have hmo7 := hmono 7 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo7)
  all_goals try have hte8 := hte 8 (by omega)
  all_goals try (have hmo8 := hmono 8 (by omega); simp only [Nat.reduceAdd, Nat.zero_add] at hmo8)
  all_goals try (exfalso; omega)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try exact not_false
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L8b00") ?_; refine ⟨isSome_at L.L8b00, ?_, ?_⟩; rw [T.L8b00]; refine ⟨hC, ⟨?_, ?_⟩, y, _, c0, j, hK, hCy, hc0, hst, hch, ?_⟩ <;> try and_intros)
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L89e0") ?_; refine ⟨isSome_at L.L89e0, ?_, ?_⟩; rw [T.L89e0]; refine ⟨hC, ⟨?_, ?_⟩, y, _, c0, j, p + 1, hK, hCy, hc0, hst, hch, ?_⟩ <;> try and_intros)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L89f3_1]; refine ⟨hC, ⟨?_, ?_⟩, y, _, c0, j, p, hK, hCy, hc0, hst, hch, ?_⟩ <;> try and_intros)
  all_goals try simp only [Mm, ApplyF, TabW, dA, sbrA, arg1, Args.d, Nat.one_ne_zero, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, u8, u16]
  all_goals try ((with_reducible show Option.isSome _ = true); (try simp (disch := decide) only [env_ra2]); (try simp (disch := decide) only [env_ra4, Nat.reduceAdd]); (try simp (disch := decide) only [env_ra3]); sep_mem hm; all_goals (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
  all_goals try simp (disch := omega) only [env_shl4, env_sx, env_lea5_shl6, env_lea3_shl4, env_sw, env_u8bv', env_u8bv]
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]; done)
  all_goals try omega
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast]; (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]; simp only [env_z8]; congr 1; all_goals (apply BitVec.eq_of_toNat_eq; simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast]; (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega))
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.toNat_replaceLow8_mod, CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self, BitVec.toNat_ofNat]; simp (disch := omega) only [env_flag, env_flag']; done)
  all_goals try (have e := hcc'.down; subst e)
  all_goals try simp only [u8, u16, Args.d, ↓reduceIte, ite_true, ite_false, Nat.one_ne_zero]
  all_goals try simp only [hfz, ↓reduceIte, Nat.one_ne_zero, ite_true, ite_false]
  all_goals try simp (disch := omega) only [env_drop2]
  all_goals try simp (disch := omega) only [env_u16bv]
  all_goals try simp only [env_sw16]
  all_goals try simp (disch := omega) only [env_off, env_off']
  all_goals try simp (disch := omega) only [env_u16a, env_u16b]
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self]
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g]
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33]
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self] at cc2
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g] at cc2
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33] at cc2
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self] at cc3
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g] at cc3
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33] at cc3
  all_goals try omega
  all_goals try simp only [env_sw16c]
  all_goals try omega
  all_goals try (simp only [StatusFlags.from_result]; simp (disch := first | assumption | omega) only [env_cf16]; done)
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc1
  all_goals try simp only [env_mod16] at cc1
  all_goals try simp (disch := omega) only [env_u16] at cc1
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc2
  all_goals try simp only [env_mod16] at cc2
  all_goals try simp (disch := omega) only [env_u16] at cc2
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc3
  all_goals try simp only [env_mod16] at cc3
  all_goals try simp (disch := omega) only [env_u16] at cc3
  all_goals try (obtain ⟨htb1, htb2, htb3, htb4⟩ := htb; omega)
  all_goals try (exfalso; obtain ⟨htb1, htb2, htb3, htb4⟩ := htb; omega)
  all_goals try (obtain ⟨hfl50, hfl98⟩ := env_ftlen hCy hst; simp only [hfl50, hfl98]; done)
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]; done)
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, env_sw320, env_r15]; done)
  all_goals try (simp only [Nat.add_sub_cancel' htp1, Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx, BitVec.ofNat_add]; rfl)
  all_goals try (simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]; obtain ⟨htb1, htb2, htb3, htb4⟩ := htb; omega)
  all_goals try (simp only [FrN, Mm, ApplyF, TabW, dA, sbrA, arg1, Args.d, Nat.one_ne_zero, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, u8, u16]; (try simp (disch := omega) only [env_shl4]); (try simp (disch := decide) only [env_ra2]); sep_close hm; all_goals (try with_reducible rfl); done)
  all_goals try (env_head Or; left; simp only [lex_var]; (try simp only [slot64, Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try simp (disch := decide) only [env_ra2]); (try (sep_mem hm <;> try (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))); (try (sep_mem hm0 <;> try (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))); (try simp only [Option.getD_some]); (try env_lex_split); all_goals ((try simp only [Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega); done)
  all_goals try (env_head Or; right; constructor; (simp only [lex_var]; (try simp only [slot64, Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try (sep_mem hm <;> try (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))); (try (sep_mem hm0 <;> try (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))); (try simp only [Option.getD_some]); (try with_reducible rfl)); (try simp only [lex_var]); omega)
  all_goals try (env_head LE.le; simp only [lex_var]; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, hrbx]); (try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]); simp (disch := omega) only [hls])
  all_goals try (env_head LE.le; simp only [lex_var]; (try simp only [slot64, Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceToNat, Nat.reduceEqDiff, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.xor_self, z, hrsp, hrbp, hrsi, hr14, hr12, hr8, hrdi, hrbx, hrcx]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try simp (disch := decide) only [env_ra2]); (try (sep_mem hm <;> try (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))); (try (sep_mem hm0 <;> try (first | ((try simp only [env_sub_base, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega) | ((try simp only [env_sub_base, BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))); (try simp only [Option.getD_some]); (try env_lex_split); all_goals ((try simp only [Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.zero_eq, BitVec.toNat_zero, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega); done)
  all_goals try edge_step
  all_goals try (have a0 : (y.ftLow.getD (2 * p) 0).toNat < 2 ^ 8 := (y.ftLow.getD (2 * p) 0).toBitVec.isLt; have a1 : (y.ftLow.getD (2 * p + 1) 0).toNat < 2 ^ 8 := (y.ftLow.getD (2 * p + 1) 0).toBitVec.isLt; have a2 : (y.ftLow.getD (2 * (p + 1)) 0).toNat < 2 ^ 8 := (y.ftLow.getD (2 * (p + 1)) 0).toBitVec.isLt; have a3 : (y.ftLow.getD (2 * (p + 1) + 1) 0).toNat < 2 ^ 8 := (y.ftLow.getD (2 * (p + 1) + 1) 0).toBitVec.isLt; simp only [Nat.reducePow] at a0 a1 a2 a3; omega)
  all_goals try (have a0 : (y.ftHigh.getD (2 * p) 0).toNat < 2 ^ 8 := (y.ftHigh.getD (2 * p) 0).toBitVec.isLt; have a1 : (y.ftHigh.getD (2 * p + 1) 0).toNat < 2 ^ 8 := (y.ftHigh.getD (2 * p + 1) 0).toBitVec.isLt; have a2 : (y.ftHigh.getD (2 * (p + 1)) 0).toNat < 2 ^ 8 := (y.ftHigh.getD (2 * (p + 1)) 0).toBitVec.isLt; have a3 : (y.ftHigh.getD (2 * (p + 1) + 1) 0).toNat < 2 ^ 8 := (y.ftHigh.getD (2 * (p + 1) + 1) 0).toBitVec.isLt; simp only [Nat.reducePow] at a0 a1 a2 a3; omega)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega)
  all_goals try (env_lex_split; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]; omega)
  all_goals try (rw [show (8 ?@ (t₀.regs.get64 Reg64.rsp - 88#64) : Mem 64 → Prop) = 4 ?@ (t₀.regs.get64 Reg64.rsp - 88#64) ⋆ 4 ?@ (t₀.regs.get64 Reg64.rsp - 84#64) by rw [show t₀.regs.get64 Reg64.rsp - 84#64 = t₀.regs.get64 Reg64.rsp - 88#64 + BitVec.ofNat 64 4 by bv_omega]; exact Block.split _ 4 4 (by decide)] at hm)
  all_goals try (simp only [FrNP, Mm, ApplyF, TabW, dA, sbrA, arg1, Args.d, Nat.one_ne_zero, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, u8, u16])
  all_goals try simp (disch := omega) only [env_drop2] at hm
  all_goals try simp (disch := omega) only [env_u16bv] at hm
  all_goals try simp only [env_sw16] at hm
  all_goals try simp (disch := omega) only [env_off, env_off'] at hm
  all_goals try simp (disch := omega) only [env_u16a, env_u16b] at hm
  all_goals try simp (disch := omega) only [env_offd, Nat.add_sub_cancel, Nat.sub_self] at hm
  all_goals try simp (disch := simp) only [env_u16gw, env_u16g] at hm
  all_goals try simp only [List.getD_cons_succ, List.getD_cons_zero, e22, e23, e33] at hm
  all_goals try (rw [show (8 ?@ (t₀.regs.get64 Reg64.rsp - 88#64) : Mem 64 → Prop) = 4 ?@ (t₀.regs.get64 Reg64.rsp - 88#64) ⋆ 4 ?@ (t₀.regs.get64 Reg64.rsp - 84#64) by rw [show t₀.regs.get64 Reg64.rsp - 84#64 = t₀.regs.get64 Reg64.rsp - 88#64 + BitVec.ofNat 64 4 by bv_omega]; exact Block.split _ 4 4 (by decide)])
  all_goals (first | lex_guard_le | sep_close hm)
