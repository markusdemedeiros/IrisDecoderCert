set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_Laf40 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Laf40" := by
  clear hc
  cfg_block
  measure_hb "Laf40"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, hm⟩, hn⟩ := hs₀
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte0 := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat) (by omega)
    have hte1 := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    rw [Laf40_pre] at hm
    have hT := hm
    rw [hf4_te_arr (arg3 t₀) x.te] at hT
    obtain ⟨htl0, htl1⟩ := hf4_te_ld2 (r := s₀.regs.get64 .r10) hT h2 (by omega)
    clear hT
    have hmH := hm
    unfold Mem.Hid at hmH
    have hlf0 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hlf1 := Mem.Val.loadInt hmH (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hlf2 := Mem.Val.loadInt hmH (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    clear hmH
    have hsb0 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hsb1 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb400") ⟨by decide, Lb400_tbl_Laf40 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lafd9") ⟨by decide, Lafd9_tbl_Laf40 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
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
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld0); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld0); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld1); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld1); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld2); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld2); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld3); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld3); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld4); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld4); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld5); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld5); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5)
    all_goals try subst_vars
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld0); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld0); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld1); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld1); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld2); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld2); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld3); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld3); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld4); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld4); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld5); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld5); simp only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5)
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, BitVec.toNat_ofNat]
    all_goals try simp only [hf4_b8] at *
    all_goals try (refine Mem.Block.storeInt_val2 hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) ?_ ?_)
    case vc11.refine_8 =>
      rw [hf4_r12 _ _ _ hte0]
      try rfl
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | (rw [htl0]; rfl)
      | (rw [htl1]; rfl)
      | (rw [Laf40_pre]; with_reducible exact hm)
      | (congr 1; rw [hf4_r192]; all_goals first | rfl | omega)
      | (congr 1; rw [hf4_inc]; all_goals omega)
      | (rw [hf4_inc]; all_goals omega)
      | exact fun h => h
      | (rw [hlf0]; rfl)
      | with_reducible exact hsb0
      | (rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide), hlf1]; rfl)
      | (rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide), hlf2]; rfl)
      | (rw [Mem.loadInt_storeInt_sub_hi _ _ 176 80 _ (by decide) (by decide)]; with_reducible exact hsb1)
      | (rw [hf4_tn_inc]; all_goals first | omega | (left; omega))
      | (rw [hf4_tn_inc, Nat.add_sub_cancel, h6]; all_goals first | rfl | omega)
      | (rw [hf4_r12 _ _ _ hte0]; rfl)
      | (simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega)
      | (have hc := ‹CondCode.nc.interp _ = false›
         rw [CondCode.interp_nc_sub8 _ _ _ rfl] at hc
         simp only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hc
         simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
         omega)
      | (try simp only [arg0, arg3, hSL]
         apply BitVec.eq_of_toNat_eq
         simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
         try generalize (if x.smooth = 0 then 4 else 0) = H at hh ⊢
         omega)
