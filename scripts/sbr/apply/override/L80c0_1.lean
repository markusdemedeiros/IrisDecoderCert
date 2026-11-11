theorem blk_L80c0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L80c0_1" ⟨"ff_aac_sbr_apply.L80c0_1", B.L80c0_1, some "ff_aac_sbr_apply.L814a"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC0, ⟨hrsp, hrbp⟩, y, ch, c0, j, kk, t, hK, hC, hc0, hst, hch, hj, h_rax, h_rcx, hf2, h_rdx, h_r12, h_r15, hf6, hf7, hf8, hf9, hf10, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, hf18, h_r14, hm⟩ := T.L80c0_1.mp hs
  clear hs
  have hb := mapb_bounds hC
  have hj8 := mapb_j_lt8 hC hch hj
  have hL := mapb_lens hC hst
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  · try simp only [Args.d, ↓reduceIte, ite_true] at hj hst
    simp only [Mm, ApplyF, ArrW, DArrW, TabW, ScW, DScW, Args.d, ↓reduceIte, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at hm
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rax
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rcx
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rdx
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r12
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r15
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r8
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rsi
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rbx
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r11
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r10
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r9
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rdi
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r14
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rax
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rcx
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf2
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rdx
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r12
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r15
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf6
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf7
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf8
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf9
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf10
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r8
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rsi
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rbx
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r11
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r10
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r9
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rdi
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf18
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r14
    obtain ⟨A, hAw⟩ : ∃ A, A = (y.ftNoise.getD 2 0).toNat + 256 * (y.ftNoise.getD 3 0).toNat + ((y.ftNoise.getD 4 0).toNat + 256 * (y.ftNoise.getD 5 0).toNat - ((y.ftNoise.getD 2 0).toNat + 256 * (y.ftNoise.getD 3 0).toNat)) % 4 - y.kx1 ∧ True := ⟨_, rfl, trivial⟩
    have hA44 : A + 4 * t + 4 ≤ 48 := by have := hAw.1; omega
    try rw [← hAw.1] at h_rbx
    try rw [← hAw.1] at h_r11
    try rw [← hAw.1] at h_r10
    try rw [← hAw.1] at h_r9
    try rw [← hAw.1] at h_r8
    have hm0 := hm
    try dsimp only
    simp only [B.L80c0_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals mapb_name
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld1
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld1
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld1
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld1
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld2
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld2
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld2
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld3
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
    all_goals try sep_vals hm
    all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1; done) | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld2; sep_mem hm; all_goals (first | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2; done) | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld3; sep_mem hm; all_goals (first | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3; done) | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld1
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld1
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld1
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld1
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld2
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld2
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld2
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld3
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
    all_goals try sep_vals hm
    all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1; done) | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld2; sep_mem hm; all_goals (first | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2; done) | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld3; sep_mem hm; all_goals (first | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3; done) | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]
    all_goals try dsimp only
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub]
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub]
    all_goals try sep_mem hm
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd]
    all_goals try ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc1
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc1
    all_goals try ((try dsimp only at cc1); rw [CondCode.interp_a_sub] at cc1; rotate_left; rfl)
    all_goals try ((try dsimp only at cc1); rw [CondCode.interp_be_sub] at cc1; rotate_left; rfl)
    all_goals try ((try dsimp only at cc1); rw [mapb_nc_sub] at cc1; rotate_left; rfl)
    all_goals try ((try dsimp only at cc1); rw [mapb_c_sub] at cc1; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc1
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc1
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc1
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc2
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc2
    all_goals try ((try dsimp only at cc2); rw [CondCode.interp_a_sub] at cc2; rotate_left; rfl)
    all_goals try ((try dsimp only at cc2); rw [CondCode.interp_be_sub] at cc2; rotate_left; rfl)
    all_goals try ((try dsimp only at cc2); rw [mapb_nc_sub] at cc2; rotate_left; rfl)
    all_goals try ((try dsimp only at cc2); rw [mapb_c_sub] at cc2; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc2
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc2
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc2
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc3
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc3
    all_goals try ((try dsimp only at cc3); rw [CondCode.interp_a_sub] at cc3; rotate_left; rfl)
    all_goals try ((try dsimp only at cc3); rw [CondCode.interp_be_sub] at cc3; rotate_left; rfl)
    all_goals try ((try dsimp only at cc3); rw [mapb_nc_sub] at cc3; rotate_left; rfl)
    all_goals try ((try dsimp only at cc3); rw [mapb_c_sub] at cc3; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc3
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc3
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc3
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc4
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc4
    all_goals try ((try dsimp only at cc4); rw [CondCode.interp_a_sub] at cc4; rotate_left; rfl)
    all_goals try ((try dsimp only at cc4); rw [CondCode.interp_be_sub] at cc4; rotate_left; rfl)
    all_goals try ((try dsimp only at cc4); rw [mapb_nc_sub] at cc4; rotate_left; rfl)
    all_goals try ((try dsimp only at cc4); rw [mapb_c_sub] at cc4; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc4
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc4
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc4
    all_goals try have hN1 := mapb_noise hC hst 1 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN1
    all_goals try have hN2 := mapb_noise hC hst 2 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN2
    all_goals try have hN3 := mapb_noise hC hst 3 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN3
    all_goals try have hN4 := mapb_noise hC hst 4 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN4
    all_goals try (exfalso; omega)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L80c0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L80c0") ?_; refine ⟨isSome_at L.L80c0, ?_, ?_⟩; rw [T.L80c0]; refine ⟨hC0, ?_, y, 0, c0, j, kk, t + 1, hK, hC, hc0, ?_⟩ <;> try and_intros)
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L814a]; refine ⟨hC0, ?_, y, 0, c0, j, kk, hK, hC, hc0, ?_⟩ <;> try and_intros)
    all_goals try simp only [← hAw.1]
    all_goals try simp only [u8, u16, sbrA, arg0, arg1, Args.d, dA, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd]
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]; done)
    all_goals try omega
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]; (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)
    all_goals try (simp only [Mm, ApplyF, ArrW, DArrW, TabW, ScW, DScW, Args.d, ↓reduceIte, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd]; (try simp only [Nat.reduceAdd] at hm); sep_close hm; done)
    all_goals try (simp only [Mm, ApplyF, ArrW, DArrW, TabW, ScW, DScW, Args.d, ↓reduceIte, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd]; (try simp only [Nat.reduceAdd] at hm); sep_close hm; done)
    all_goals try (mapb_head Or; left; (try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega))
    all_goals try (mapb_head Or; right; constructor; (focus (first | (simp only [lex_var]; done) | ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); first | (with_reducible rfl) | (refine congrArg Kraken.lex ?_; (try simp only [List.cons.injEq]); all_goals (and_intros <;> first | (with_reducible rfl) | ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))))); (first | (simp only [lex_var]; done) | (simp only [lex_var]; omega)))
    all_goals try ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_le; (repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)); first | (with_reducible exact Nat.le_refl _) | ((with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
    all_goals try ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega))
  · try simp only [Args.d, ↓reduceIte, ite_true] at hj hst
    simp only [Mm, ApplyF, ArrW, DArrW, TabW, ScW, DScW, Args.d, ↓reduceIte, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at hm
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rax
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rcx
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rdx
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r12
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r15
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r8
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rsi
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rbx
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r11
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r10
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r9
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rdi
    try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r14
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rax
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rcx
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf2
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rdx
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r12
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r15
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf6
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf7
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf8
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf9
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf10
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r8
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rsi
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rbx
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r11
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r10
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r9
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rdi
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf18
    try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r14
    obtain ⟨A, hAw⟩ : ∃ A, A = (y.ftNoise.getD 2 0).toNat + 256 * (y.ftNoise.getD 3 0).toNat + ((y.ftNoise.getD 4 0).toNat + 256 * (y.ftNoise.getD 5 0).toNat - ((y.ftNoise.getD 2 0).toNat + 256 * (y.ftNoise.getD 3 0).toNat)) % 4 - y.kx1 ∧ True := ⟨_, rfl, trivial⟩
    have hA44 : A + 4 * t + 4 ≤ 48 := by have := hAw.1; omega
    try rw [← hAw.1] at h_rbx
    try rw [← hAw.1] at h_r11
    try rw [← hAw.1] at h_r10
    try rw [← hAw.1] at h_r9
    try rw [← hAw.1] at h_r8
    have hm0 := hm
    try dsimp only
    simp only [B.L80c0_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals mapb_name
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld1
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld1
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld1
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld1
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld2
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld2
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld2
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld3
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
    all_goals try sep_vals hm
    all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1; done) | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld2; sep_mem hm; all_goals (first | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2; done) | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld3; sep_mem hm; all_goals (first | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3; done) | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld1
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld1
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld1
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld1
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld2
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld2
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld2
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub] at ld3
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub] at ld3
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
    all_goals try sep_vals hm
    all_goals try (revert ld1; sep_mem hm; all_goals (first | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1; done) | (intro ld1; simp only [Option.some.injEq] at ld1; subst ld1) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld2; sep_mem hm; all_goals (first | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2; done) | (intro ld2; simp only [Option.some.injEq] at ld2; subst ld2) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try (revert ld3; sep_mem hm; all_goals (first | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3; done) | (intro ld3; simp only [Option.some.injEq] at ld3; subst ld3) | ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)))
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]
    all_goals try dsimp only
    all_goals try simp (disch := decide) only [mapb_off _ 311890 50, mapb_off _ 311940 98, mapb_off _ 312038 12, mapb_off _ 312050 60, Nat.reduceSub]
    all_goals try simp (disch := decide) only [mapb_rsi_off, Nat.reduceSub]
    all_goals try sep_mem hm
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd]
    all_goals try ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc1
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc1
    all_goals try ((try dsimp only at cc1); rw [CondCode.interp_a_sub] at cc1; rotate_left; rfl)
    all_goals try ((try dsimp only at cc1); rw [CondCode.interp_be_sub] at cc1; rotate_left; rfl)
    all_goals try ((try dsimp only at cc1); rw [mapb_nc_sub] at cc1; rotate_left; rfl)
    all_goals try ((try dsimp only at cc1); rw [mapb_c_sub] at cc1; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc1
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc1
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc1
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc2
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc2
    all_goals try ((try dsimp only at cc2); rw [CondCode.interp_a_sub] at cc2; rotate_left; rfl)
    all_goals try ((try dsimp only at cc2); rw [CondCode.interp_be_sub] at cc2; rotate_left; rfl)
    all_goals try ((try dsimp only at cc2); rw [mapb_nc_sub] at cc2; rotate_left; rfl)
    all_goals try ((try dsimp only at cc2); rw [mapb_c_sub] at cc2; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc2
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc2
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc2
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc3
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc3
    all_goals try ((try dsimp only at cc3); rw [CondCode.interp_a_sub] at cc3; rotate_left; rfl)
    all_goals try ((try dsimp only at cc3); rw [CondCode.interp_be_sub] at cc3; rotate_left; rfl)
    all_goals try ((try dsimp only at cc3); rw [mapb_nc_sub] at cc3; rotate_left; rfl)
    all_goals try ((try dsimp only at cc3); rw [mapb_c_sub] at cc3; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc3
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc3
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc3
    all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc4
    all_goals try simp (disch := omega) only [mapb_take2, mapb_take1, Nat.reduceAdd] at cc4
    all_goals try ((try dsimp only at cc4); rw [CondCode.interp_a_sub] at cc4; rotate_left; rfl)
    all_goals try ((try dsimp only at cc4); rw [CondCode.interp_be_sub] at cc4; rotate_left; rfl)
    all_goals try ((try dsimp only at cc4); rw [mapb_nc_sub] at cc4; rotate_left; rfl)
    all_goals try ((try dsimp only at cc4); rw [mapb_c_sub] at cc4; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul] at cc4
    all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapb_and3] at cc4
    all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg] at cc4
    all_goals try have hN1 := mapb_noise hC hst 1 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN1
    all_goals try have hN2 := mapb_noise hC hst 2 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN2
    all_goals try have hN3 := mapb_noise hC hst 3 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN3
    all_goals try have hN4 := mapb_noise hC hst 4 (by omega)
    all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN4
    all_goals try (exfalso; omega)
    all_goals try (simp only [Option.isSome_some]; done)
    all_goals try (goal_has_str "ff_aac_sbr_apply.L80c0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L80c0") ?_; refine ⟨isSome_at L.L80c0, ?_, ?_⟩; rw [T.L80c0]; refine ⟨hC0, ?_, y, 1, c0, j, kk, t + 1, hK, hC, hc0, ?_⟩ <;> try and_intros)
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L814a]; refine ⟨hC0, ?_, y, 1, c0, j, kk, hK, hC, hc0, ?_⟩ <;> try and_intros)
    all_goals try simp only [← hAw.1]
    all_goals try simp only [u8, u16, sbrA, arg0, arg1, Args.d, dA, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd]
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]; done)
    all_goals try omega
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]; (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)
    all_goals try (simp only [Mm, ApplyF, ArrW, DArrW, TabW, ScW, DScW, Args.d, ↓reduceIte, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd]; (try simp only [Nat.reduceAdd] at hm); sep_close hm; done)
    all_goals try (simp only [Mm, ApplyF, ArrW, DArrW, TabW, ScW, DScW, Args.d, ↓reduceIte, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd]; (try simp only [Nat.reduceAdd] at hm); sep_close hm; done)
    all_goals try (mapb_head Or; left; (try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega))
    all_goals try (mapb_head Or; right; constructor; (focus (first | (simp only [lex_var]; done) | ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); first | (with_reducible rfl) | (refine congrArg Kraken.lex ?_; (try simp only [List.cons.injEq]); all_goals (and_intros <;> first | (with_reducible rfl) | ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))))); (first | (simp only [lex_var]; done) | (simp only [lex_var]; omega)))
    all_goals try ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_le; (repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)); first | (with_reducible exact Nat.le_refl _) | ((with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
    all_goals try ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_r8, h_rsi, h_rbx, h_r11, h_r10, h_r9, h_rdi, h_r14, AddrIndex.offset64_scale1, mapb_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapb_and3w, mapb_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega))
