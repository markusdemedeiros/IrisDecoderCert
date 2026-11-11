set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_Lafa0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lafa0" := by
  clear hc
  cfg_block
  measure_hb "Lafa0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    rw [Lafa0_pre] at hm
    have hl50 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hvec := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hl11 := hf4_l11 hm
    have htl := hf4_te_ld ((s₀.regs.get64 .r10).toNat + 1) (by omega) hm
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    have htv := hf4_te2 (x.te ((s₀.regs.get64 .r10).toNat + 1)) (by omega)
    have htl2 : s₀.dmem.loadInt (s₀.regs.get64 .r8 + BitVec.ofNat 64 ((s₀.regs.get64 .r10).toNat + 1) * 1#64 + 88732#64) 1
        = some (Int.ofBytes (Int.toBytes 1 ((x.te ((s₀.regs.get64 .r10).toNat + 1) : Nat) : Int))) := by
      rw [BitVec.mul_one, h2, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _) 88732#64, ← BitVec.add_assoc]
      exact htl
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb400") ⟨by decide, Lb400_tbl_Lafa0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lafd9_tbl_Lafa0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4
    all_goals try simp only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, BitVec.toNat_ofNat]
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | with_reducible exact hf4_xb _
      | (rw [hl11]; rfl)
      | (rw [hl50]; rfl)
      | (rw [htl2]; rfl)
      | with_reducible exact hvec
      | (rw [hf4_tn_succ _ (by omega)]; omega)
      | (have hc := ‹CondCode.nc.interp _ = false›
         rw [CondCode.interp_nc_sub64 _ _ _ rfl, htv] at hc
         simp only [decide_eq_false_iff_not, Nat.not_le] at hc
         rw [hf4_tn_succ _ (by omega)] at hc ⊢
         omega)
      | (simp only [ArgRegs]; with_reducible exact hf4_step _ _ _ _ _ h7 (by omega) (by rw [hf4_tn_succ _ (by omega)]; omega))
      | (try simp only [arg0, arg3, hSL]
         rw [h7, hf4_tn_succ _ (by omega)]
         apply BitVec.eq_of_toNat_eq
         simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
         try generalize (if x.smooth = 0 then 4 else 0) = H at hh ⊢
         omega)
      | (simp only [ArgRegs]; with_reducible exact hf4_step _ _ _ _ _ h8 (by omega) (by rw [hf4_tn_succ _ (by omega)]; omega))
      | (try simp only [arg0, arg3, hSL]
         rw [h8, hf4_tn_succ _ (by omega)]
         apply BitVec.eq_of_toNat_eq
         simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
         try generalize (if x.smooth = 0 then 4 else 0) = H at hh ⊢
         omega)
      | (rw [h9]; congr 3; omega)
      | (refine ⟨?_, ?_⟩
         · first | (rw [h9]; congr 3; omega) | (rw [h9]; congr 2; congr 1; omega) | (simp only [ArgRegs]; rw [h9]; congr 3; omega)
         · first | with_reducible assumption | exact hm)
      | (rw [Lafa0_pre]; exact hm)
