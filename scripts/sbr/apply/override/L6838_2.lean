theorem blk_L6838_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6838_2" ⟨"ff_aac_sbr_apply.L6838_2", B.L6838_2, some "ff_aac_sbr_apply.L68b0"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hst, hbx, h12, h13, hm⟩ := T.L6838_2.mp hs
  clear hs
  simp only [Mm, ApplyF, CstW, FrD, FrRaw, TabW_push, FnW_push, AcW_push, OutW_push] at hm
  have hne : 1 ≤ x.d0.nenv := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd0, -⟩, -⟩ := id hC.1
    exact (hd0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hst).1
  simp only [B.L6838_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L68b0])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨1, Nat.le_refl _, hne, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    hbx, h12, h13, arg1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul]; done)
  all_goals try (simp only [Mm, ApplyF, CstW, FrD, FrRaw, TabW_push, FnW_push, AcW_push, OutW_push] at hm ⊢; sep_close hm)
  all_goals try var_step
  done
