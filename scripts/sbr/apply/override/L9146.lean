theorem blk_L9146 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9146" ⟨"ff_aac_sbr_apply.L9146", B.L9146, some "ff_aac_sbr_apply.L914e"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrax, hrbx, hm⟩ := T.L9146.mp hs
  dsimp only
  simp only [B.L9146]
  vcgen
  all_goals try subst_vars
  all_goals try (goal_has_str "ff_aac_sbr_apply.L98e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L98e0") ?_; refine ⟨isSome_at L.L98e0, ?_, ?_⟩; rw [T.L98e0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L914e])
  all_goals try edge_step
  all_goals try (left; dq_var)
  all_goals try var_step
  all_goals try (refine ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx]; done)
  all_goals try (simp only [Mm, FrX, FrGA]; sep_close hm)
