theorem blk_L9a02_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a02_1" ⟨"ff_aac_sbr_apply.L9a02_1", B.L9a02_1, some "ff_aac_sbr_apply.L9a50"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, y, hK, hCy, hm⟩ := T.L9a02_1.mp hs
  clear hs
  simp only [B.L9a02_1]
  vcgen
  all_goals try subst s₀
  left
  refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a7d") ?_
  refine ⟨isSome_at L.L9a7d, ?_, Or.inr ⟨?_, ?_⟩⟩
  rotate_left
  · simp only [lex_var] at hn ⊢; exact hn
  · simp only [lex_var]; decide
  rw [T.L9a7d]
  exact ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, y, hK, hCy, hm⟩
