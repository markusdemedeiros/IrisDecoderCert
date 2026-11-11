theorem blk_L6817 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6817" ⟨"ff_aac_sbr_apply.L6817", B.L6817, some "ff_aac_sbr_apply.L6825"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hb, x', hx', hid, hm⟩ := T.L6817.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  have hp0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x'.pushed
  simp only [B.L6817]
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
  all_goals try simp_conds [CondCode.interp, StatusFlags.from_result, hp0, Int64.toBitVec_ofNat_norm,
    BitVec.setWidth_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
    BitVec.zero_eq, beq_eq_false_iff_ne]
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L676e") ?_
                 refine ⟨isSome_at L.L676e, ?_, ?_⟩; rw [T.L676e])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6825])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x', hx', Or.inl hb, by assumption, hid, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done
