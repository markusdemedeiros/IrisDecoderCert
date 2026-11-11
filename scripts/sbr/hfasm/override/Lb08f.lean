set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_Lb08f (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb08f" := by
  clear hc
  cfg_block
  measure_hb "Lb08f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    try dsimp only at *
    generalize hI0 : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV0 : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    have hI := And.intro hI0 True.intro
    have hV := And.intro hV0 True.intro
    clear hI0 hV0
    rw [Lb08f_pre] at hm
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hkx := Mem.Val.loadInt_lo4 (v := (BitVec.ofNat 64 x.kx).toInt) hm (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    rw [BitVec.toInt_ofNat64_of_lt _ (by omega)] at hkx
    have hlf8 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0xf8#64) 8 = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 (x.m - 1)).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hlc0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0xc0#64) 8 = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 x.m).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hl88 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x88#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀ + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i)).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hl40 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8 = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 i).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hl38 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x38#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨n2_tbl_Lb08f _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb16c") ⟨by decide, Lb16c_tbl_Lb08f _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp only [hI.1, hV.1]
    case vc2 =>
      exfalso
      have hl := ‹Mem.loadInt _ (t₀.regs.get64 .rsp - 0x90#64) 4 = some _›
      rw [hkx] at hl
      obtain rfl := Option.some.inj hl
      have hf := ‹CondCode.z.interp _ = true›
      rw [BitVec.ofInt32_ofBytes_toBytes4, hf_z32_ne _ _ (by omega) (by decide)] at hf
      exact absurd hf (by decide)
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
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld0
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld1
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld2
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld3
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld4
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld5
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld6
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld7
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld8
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld9
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld10
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld11
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld12
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld13
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld14
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld15
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld16
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld17
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld18
    all_goals try simp only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld19
    all_goals try subst_vars
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | cell_some
      | cell_lcpi
      | (simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] <;> omega)
      | exact hf_and1_lt2 _
      | (have hf := ‹CondCode.l.interp _ = false›
         exact hf_l_false_ge _ _ (by omega) (by omega) _ hf rfl)
      | (have hf := ‹CondCode.l.interp _ = false›
         rw [CondCode.interp_l_sub32 _ _ _ rfl] at hf
         simp (disch := omega) only [decide_eq_false_iff_not, not_lt, BitVec.ofInt64_ofBytes_toBytes8,
           BitVec.ofInt_toInt, hf_toInt_sw32] at hf
         omega)
      | (rw [h14]; exact hf_lea4 _ _ _)
      | (simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.isSome_some]; done)
      | with_reducible exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
      | (have hD := hm; simp only [DataW] at hD
         first
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.here _ _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _))
      | (rw [hkx]; rfl)
      | (rw [hlf8]; rfl)
      | (rw [hlc0]; rfl)
      | (rw [hl88]; rfl)
      | (rw [hl40]; rfl)
      | (rw [hl38]; rfl)
