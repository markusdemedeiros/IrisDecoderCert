theorem blk_start_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.start_3" ⟨"ff_aac_sbr_apply.start_3", B.start_3, some "ff_aac_sbr_apply.L676e"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨⟨hC, hid⟩, ⟨hrsp, hrbp⟩, h9, hb, hst, hz, hm⟩ := T.start_3.mp hs
  clear hs
  simp only [B.start_3]
  vcgen
  all_goals try subst_vars
  all_goals try simp_conds [CondCode.interp, hz, decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    Bool.not_eq_true', Bool.not_eq_false', decide_not, ne_eq]
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6825") ?_
                 refine ⟨isSome_at L.L6825, ?_, ?_⟩; rw [T.L6825])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L676e])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x, Or.inl rfl, Or.inr ⟨?_, rfl, hst⟩, by assumption, hid, hm⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, hb]; done)
  all_goals try edge_step
  all_goals try var_step
  done
