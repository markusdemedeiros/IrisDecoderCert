theorem blk_L7f80 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7f80" ⟨"ff_aac_sbr_apply.L7f80", B.L7f80, some "ff_aac_sbr_apply.L7f80_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC0, ⟨hrsp, hrbp⟩, y, ch, c0, j, kk, t, hK, hC, hc0, hst, hch, hj, h_rax, h_rcx, hf2, h_rdx, h_r12, h_r15, hf6, hf7, hf8, hf9, h_rsi, hf11, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, hf18, h_r14, hm⟩ := T.L7f80.mp hs
  clear hs
  have hb := mapa_bounds hC
  try have hj8 := mapa_j_lt8 hC hch hj
  have hL := mapa_lens hC hst
  try simp only [Args.d, ↓reduceIte, ite_true, Nat.one_ne_zero, ite_false] at hj hst
  try simp only [Args.d, ↓reduceIte, ite_true, Nat.one_ne_zero, ite_false] at hnz
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [ArrW, DArrW, TabW, ScW, DScW, FrMb, dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, BitVec.add_zero] at hm
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rax
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rcx
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rdx
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r12
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r15
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rsi
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r8
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rdi
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_rbx
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r11
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r10
  try simp only [dA, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at h_r9
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
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rsi
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf11
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r8
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rdi
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_rbx
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r11
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r10
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r9
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at hf18
  try simp only [u16, u8, Nat.reduceMul, Nat.mul_one, Nat.reduceAdd] at h_r14
  obtain ⟨A, hAw⟩ : ∃ A, A = (y.ftNoise.getD 0 0).toNat + 256 * (y.ftNoise.getD 1 0).toNat + ((y.ftNoise.getD 2 0).toNat + 256 * (y.ftNoise.getD 3 0).toNat - ((y.ftNoise.getD 0 0).toNat + 256 * (y.ftNoise.getD 1 0).toNat)) % 4 - y.kx1 ∧ True := ⟨_, rfl, trivial⟩
  have hA44 : A + 4 * t + 4 ≤ 48 := by have := hAw.1; omega
  try rw [← hAw.1] at h_rbx
  try rw [← hAw.1] at h_r11
  try rw [← hAw.1] at h_r10
  try rw [← hAw.1] at h_r9
  try rw [← hAw.1] at h_r8
  generalize hD : t₀.regs.get64 Reg64.rsi + 166176#64 + BitVec.ofNat 64 (128 + 88768 * ch) = D at hm h_rdx
  replace hD := PLift.up hD
  have hm0 := hm
  try dsimp only
  simp only [B.L7f80]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  all_goals (have phm : PLift _ := ⟨hm⟩; have phm0 : PLift _ := ⟨hm0⟩; clear hm hm0)
  vcgen
  all_goals (have hm := phm.down; have hm0 := phm0.down; clear phm phm0)
  all_goals try subst_vars
  all_goals mapa_name
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld1
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld1
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld1
  all_goals try simp (disch := decide) only [mapa_off _ 311890 50, mapa_off _ 311940 98, mapa_off _ 312038 12, mapa_off _ 312050 60, Nat.reduceSub] at ld1
  all_goals try simp (disch := decide) only [mapa_rsi_off, Nat.reduceSub] at ld1
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld2
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld2
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld2
  all_goals try simp (disch := decide) only [mapa_off _ 311890 50, mapa_off _ 311940 98, mapa_off _ 312038 12, mapa_off _ 312050 60, Nat.reduceSub] at ld2
  all_goals try simp (disch := decide) only [mapa_rsi_off, Nat.reduceSub] at ld2
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt] at ld3
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at ld3
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at ld3
  all_goals try simp (disch := decide) only [mapa_off _ 311890 50, mapa_off _ 311940 98, mapa_off _ 312038 12, mapa_off _ 312050 60, Nat.reduceSub] at ld3
  all_goals try simp (disch := decide) only [mapa_rsi_off, Nat.reduceSub] at ld3
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]
  all_goals try dsimp only
  all_goals try simp (disch := decide) only [mapa_off _ 311890 50, mapa_off _ 311940 98, mapa_off _ 312038 12, mapa_off _ 312050 60, Nat.reduceSub]
  all_goals try simp (disch := decide) only [mapa_rsi_off, Nat.reduceSub]
  all_goals try (first | mapa_head Table.ofLabels | mapa_head table | sep_mem hm)
  all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  all_goals try simp (disch := omega) only [mapa_take2, mapa_take1, Nat.reduceAdd]
  all_goals try ((try simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega)
  all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc1
  all_goals try simp (disch := omega) only [mapa_take2, mapa_take1, Nat.reduceAdd] at cc1
  all_goals try ((try dsimp only at cc1); rw [CondCode.interp_a_sub] at cc1; rotate_left; rfl)
  all_goals try ((try dsimp only at cc1); rw [CondCode.interp_be_sub] at cc1; rotate_left; rfl)
  all_goals try ((try dsimp only at cc1); rw [mapa_nc_sub] at cc1; rotate_left; rfl)
  all_goals try ((try dsimp only at cc1); rw [mapa_c_sub] at cc1; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul] at cc1
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapa_and3] at cc1
  all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg] at cc1
  all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc2
  all_goals try simp (disch := omega) only [mapa_take2, mapa_take1, Nat.reduceAdd] at cc2
  all_goals try ((try dsimp only at cc2); rw [CondCode.interp_a_sub] at cc2; rotate_left; rfl)
  all_goals try ((try dsimp only at cc2); rw [CondCode.interp_be_sub] at cc2; rotate_left; rfl)
  all_goals try ((try dsimp only at cc2); rw [mapa_nc_sub] at cc2; rotate_left; rfl)
  all_goals try ((try dsimp only at cc2); rw [mapa_c_sub] at cc2; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul] at cc2
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapa_and3] at cc2
  all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg] at cc2
  all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc3
  all_goals try simp (disch := omega) only [mapa_take2, mapa_take1, Nat.reduceAdd] at cc3
  all_goals try ((try dsimp only at cc3); rw [CondCode.interp_a_sub] at cc3; rotate_left; rfl)
  all_goals try ((try dsimp only at cc3); rw [CondCode.interp_be_sub] at cc3; rotate_left; rfl)
  all_goals try ((try dsimp only at cc3); rw [mapa_nc_sub] at cc3; rotate_left; rfl)
  all_goals try ((try dsimp only at cc3); rw [mapa_c_sub] at cc3; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul] at cc3
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapa_and3] at cc3
  all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg] at cc3
  all_goals try simp only [Mem.sub_add_add_lit, Mem.sub_base_add, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at cc4
  all_goals try simp (disch := omega) only [mapa_take2, mapa_take1, Nat.reduceAdd] at cc4
  all_goals try ((try dsimp only at cc4); rw [CondCode.interp_a_sub] at cc4; rotate_left; rfl)
  all_goals try ((try dsimp only at cc4); rw [CondCode.interp_be_sub] at cc4; rotate_left; rfl)
  all_goals try ((try dsimp only at cc4); rw [mapa_nc_sub] at cc4; rotate_left; rfl)
  all_goals try ((try dsimp only at cc4); rw [mapa_c_sub] at cc4; rotate_left; rfl)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul] at cc4
  all_goals try simp only [CondCode.interp_nz, CondCode.interp_z, StatusFlags.zf_from_result, Bool.not_eq_true', Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, beq_eq_false_iff_ne, beq_iff_eq, ne_eq, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt, Nat.not_le, mapa_and3] at cc4
  all_goals try simp only [BitVec.toNat_eq, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg] at cc4
  all_goals try have hN0 := mapa_noise hC hst 0 (by omega)
  all_goals try simp only [u16, u8, Nat.reduceMul, Nat.reduceAdd] at hN0
  all_goals try (exfalso; omega)
  all_goals try simp only [BitVec.add_zero] at hm ⊢
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (refine mapa_al32 _ _ _ _ ?_ (by decide) (by decide) (by decide); have h := hC0.2.1; simp only [arg1] at h; exact h)
  all_goals try (simp only [Option.isSome_some]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7f80_1]; refine ⟨hC0, ?_, y, ch, c0, j, kk, t, hK, hC, hc0, ?_⟩ <;> try and_intros)
  all_goals try simp only [← hAw.1]
  all_goals try simp only [u8, u16, sbrA, arg0, arg1, Args.d, dA, hD.down, ↓reduceIte, Nat.reduceMul, Nat.reduceAdd, Nat.one_ne_zero, ite_false]
  all_goals try simp only [hz, ↓reduceIte, ite_true, ite_false, Nat.one_ne_zero]
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try omega
  all_goals try ((repeat' split) <;> omega)
  all_goals try (have := mapa_u16lt (y.ftNoise.getD 0 0) (y.ftNoise.getD 1 0); have := mapa_u16lt (y.ftNoise.getD 2 0) (y.ftNoise.getD 3 0); rw [mapa_zf4]; all_goals omega)
  all_goals try (rw [if_pos (by omega : y.d0.nnoise < 2)]; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]; done)
  all_goals try (rw [if_neg (by omega : ¬y.d0.nnoise < 2)]; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]; rw [mapa_sbb _ _ _ rfl])
  all_goals try (rw [mapa_cf_sub _ _ _ rfl]; simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]; (repeat' split) <;> (try (exfalso; omega)) <;> (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg, decide_eq_true_eq, Bool.toNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]; split <;> omega))
  all_goals try ((repeat' split) <;> (try (exfalso; omega)) <;> (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]; done))
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg]; (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)
  all_goals try (simp only [Mm, ApplyF]; rw [applyF_dpair y t₀ ch hch]; simp only [ArrW, DArrW, TabW, ScW, DScW, FrMb, dA, sbrA, arg0, arg1, hD.down, Nat.mul_zero, BitVec.add_zero, Nat.reduceMul, Nat.reduceAdd]; (try simp only [Nat.reduceAdd] at hm); sep_close hm; done)
  all_goals try (mapa_head Or; left; (try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp (disch := omega) only [mapa_in1, mapa_in0]); (try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega))
  all_goals try (mapa_head Or; right; constructor; (focus (first | (simp only [lex_var]; done) | ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); all_goals first | (with_reducible rfl) | (refine congrArg Kraken.lex ?_; (try simp only [List.cons.injEq]); all_goals (and_intros <;> first | (with_reducible rfl) | ((try simp (disch := omega) only [mapa_in1, mapa_in0]); (try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))))); (first | (simp only [lex_var]; done) | (simp only [lex_var]; omega)))
  all_goals try ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_le; (repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)); first | (with_reducible exact Nat.le_refl _) | ((with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_); ((try simp (disch := omega) only [mapa_in1, mapa_in0]); (try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega)))
  all_goals try ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale4, AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reduceMul, BitVec.ofInt_natCast, BitVec.xor_self, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r12, h_r15, h_rsi, h_r8, h_rdi, h_rbx, h_r11, h_r10, h_r9, h_r14, AddrIndex.offset64_scale1, mapa_mul4, BitVec.reduceMul]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm); (try sep_mem hm0); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_ofBytes_toBytes 16 2 rfl, BitVec.ofInt_toInt]); lex_guard_lt; (repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)); (with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_); ((try simp (disch := omega) only [mapa_in1, mapa_in0]); (try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast, mapa_and3w, mapa_and3v, BitVec.toNat_neg]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); all_goals omega))
