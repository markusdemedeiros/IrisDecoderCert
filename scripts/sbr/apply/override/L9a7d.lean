theorem blk_L9a7d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a7d" ⟨"ff_aac_sbr_apply.L9a7d", B.L9a7d, some "ff_aac_sbr_apply.L9a85"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, y, hK, hCy, hm⟩ := T.L9a7d.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  have hR := PLift.up (⟨hrsp, hrbp, hbx, h12, h14⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [Mm, FrCs] at hm
  simp only [B.L9a7d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      hbx, h12, h14] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L9a85])
  all_goals try (obtain ⟨hrsp, hrbp, hbx, h12, h14⟩ := hR.down
                 refine ⟨ch, c0, hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hbx, h12, h14,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (simp only [Mm, FrCs] at hm ⊢; sep_close hm)
  all_goals try var_step
  done
