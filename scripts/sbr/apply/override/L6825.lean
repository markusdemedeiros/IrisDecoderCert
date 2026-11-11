theorem blk_L6825 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6825" ⟨"ff_aac_sbr_apply.L6825", B.L6825, some "ff_aac_sbr_apply.L6838"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, x', hx', hbl, hp, hid, hm⟩ := T.L6825.mp hs
  clear hs
  have hK : x.Keep x'.push ∧ IdLive t₀ x'.push := ⟨by rcases hx' with rfl | rfl <;> first | exact Args.Keep.rfl'.push | exact Args.Keep.rfl'.turnoff.push, hid⟩
  have hid' := PLift.up hid; clear hid
  have hC' : ApplyC x'.push t₀ := by rcases hx' with rfl | rfl <;> first | exact hC.push | exact hC.turnoff.spSet.push
  have hK' := PLift.up hK; have hC'' := PLift.up hC'; clear hK hC'
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  have hp' : ¬ x'.pushed = 0#32 := hp
  have e0 : BitVec.setWidth 32 0#64 = 0#32 := by decide
  simp only [B.L6825]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  -- the `test %bl,%bl` branch
  all_goals try (rcases hbl with hb | ⟨hb, rfl, hst⟩ <;>
    simp_conds [CondCode.interp, StatusFlags.from_result, Reg64s.get64_set64, ite_true, ite_false, hb,
      BitVec.and_self, reduceCtorEq, BitVec.zero_eq, beq_eq_false_iff_ne, ne_eq, BitVec.reduceEq,
      not_false_eq_true, not_true_eq_false, beq_self_eq_true, Bool.true_eq_false, Bool.not_eq_eq_eq_not,
      Bool.not_false, Bool.not_true, beq_iff_eq])
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L74e9"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74e9") ?_
                 refine ⟨isSome_at L.L74e9, ?_, ?_⟩; rw [T.L74e9])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6838])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x'.push, hK'.down, hC''.down, ?_⟩)
  all_goals try (refine ⟨⟨hC, hid'.down⟩, ⟨?_, ?_⟩, ?_, hst, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd,
    Int.toBytes4_reload, TabW_push, FnW_push, AcW_push, OutW_push, PsW, hp', ite_true, ite_false,
    Int64.toBitVec_ofNat_norm, e0, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done
