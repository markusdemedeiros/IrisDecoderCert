theorem blk_L8b6b (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L8b6b" ⟨"ff_aac_sbr_apply.L8b6b", B.L8b6b, some "ff_aac_sbr_apply.L8b77"⟩ := by
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  exact (T.L8b6b.mp hs).elim
