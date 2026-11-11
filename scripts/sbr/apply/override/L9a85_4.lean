theorem blk_L9a85_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_4" ⟨"ff_aac_sbr_apply.L9a85_4", B.L9a85_4, some "ff_aac_sbr_apply.L9b2b"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, y, hK, hCy, hm⟩ := T.L9a85_4.mp hs
  clear hs
  have hK' := PLift.up hK; clear hK
  simp only [Mm] at hm
  rw [show y.R = x.R from hK'.down.1] at hm
  have hm' := fpost_of hK'.down hCy.1 hm
  clear hm
  simp only [B.L9a85_4]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hsp : PLift (∀ a : BitVec 64, BitVec.setWidth 64 440#64 + (a - 488#64) = a - 48#64) := ⟨by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  vcgen
  all_goals try subst s₀
  left
  refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9b2b") ?_
  refine ⟨isSome_at L.L9b2b, ?_, Or.inr ⟨?_, ?_⟩⟩
  rotate_left
  · simp only [lex_var] at hn ⊢; exact hn
  · simp only [lex_var]; decide
  rw [T.L9b2b]
  refine ⟨hC, ?_, ?_, ?_⟩
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hsp.down]
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp]
  · simp only [FrCs] at hm'
    simp only [FrRaw]
    sep_close hm'
