theorem blk_L74de (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74de" ⟨"ff_aac_sbr_apply.L74de", B.L74de, some "ff_aac_sbr_apply.L74e9"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨⟨hC, hid⟩, ⟨hrsp, hrbp⟩, h9, hm⟩ := T.L74de.mp hs
  have hid' := PLift.up hid; clear hid
  clear hs
  simp only [Mm, ApplyF, ScW, sbrA, arg1, TabW_push, FnW_push, AcW_push, OutW_push, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h9
  have e0 : BitVec.setWidth 32 0#64 = 0#32 := by decide
  have hC' : ApplyC { x.push with ready := 0 } t₀ := hC.push
  have hC'' := PLift.up hC'; clear hC'
  simp only [B.L74de]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, { x.push with ready := 0 }, ⟨Args.Keep.rfl', hid'.down⟩,
    hC''.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, sbrA, arg1, TabW, FnW, AcW, OutW, PsW, e0, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done
