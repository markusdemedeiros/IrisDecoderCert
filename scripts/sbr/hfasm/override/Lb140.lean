set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_Lb140 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb140" := by
  clear hc
  cfg_block
  measure_hb "Lb140"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, hm⟩, hn⟩ := hs₀
    generalize hI0 : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV0 : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    have hI := And.intro hI0 True.intro
    have hV := And.intro hV0 True.intro
    clear hI0 hV0
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hsw1 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rdi)) = s₀.regs.get64 .rdi := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth]; omega
    have hsw2 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rdi) + BitVec.setWidth 32 (s₀.regs.get64 .rdi))
        = s₀.regs.get64 .rdi + s₀.regs.get64 .rdi := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_add]; omega
    have hrw : t₀.regs.get64 .rsp - 648#64 + 584#64 = t₀.regs.get64 .rsp - 0x40#64 := by bv_omega
    rw [Lb140_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb140") ⟨by decide, Lb140_rb (i := i) (v := v) rfl h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩)
    all_goals try refine ⟨Lb16c_rb (i := i) (v := v) rfl h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp only [hI.1, hV.1, hrw]
    all_goals (run_tac Lean.Elab.Tactic.withMainContext do
      let lctx ← Lean.getLCtx
      let mut k := 0
      for d in lctx do
        if d.isImplementationDetail then continue
        if !d.userName.hasMacroScopes then continue
        let ty ← Lean.instantiateMVars d.type
        if ty.isAppOfArity ``Eq 3 && ((ty.getArg! 1).getAppFn.constName?.map (·.toString) |>.getD "").endsWith "loadInt" then
          let g ← Lean.Elab.Tactic.getMainGoal
          let g' ← g.rename d.fvarId (Lean.Name.mkSimple s!"hld{k}")
          Lean.Elab.Tactic.replaceMainGoal [g']
          k := k + 1)
    all_goals try simp only [Option.some.injEq] at hld0
    all_goals try simp only [Option.some.injEq] at hld1
    all_goals try simp only [Option.some.injEq] at hld2
    all_goals try simp only [Option.some.injEq] at hld3
    all_goals try simp only [Option.some.injEq] at hld4
    all_goals try simp only [Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hsw1, hsw2]
    try (case vc1 => exact hf_dw_ld2 hm (hf_inR14m _ _ _ _ h10 (by omega) (by omega)))
    try (case vc2 => exact hf_dw_ld0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    try (case vc3 => exact hf_dw_ld0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    try (case vc4 => exact hf_dw_ld2 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inR14 _ _ _ _ h10 (by omega) (by omega)))
    try (case vc5 => exact hf_dw_ld0 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    try (case vc6 => exact hf_dw_ld0 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    all_goals first
      | (have hl := ‹CondCode.l.interp _ = true›
         have hlt := hf_l_true_lt64 _ _ (by simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega) (by rw [h12, BitVec.toNat_ofNat]; omega) _ hl rfl
         rw [h12] at hlt
         simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hlt ⊢
         omega)
      | (rw [hf3_read_i (hf_T_st2 (Lb140_pre _ _ _ _ _ _ _ _) hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega))) (by omega)]
         try simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
         omega)
      | (rw [Lb140_pre]; exact hf_dw_st0 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _)
      | (simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;> omega)
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | (rw [h15, BitVec.toNat_ofNat]; omega)
      | (rw [Lb140_pre]; exact hm)
