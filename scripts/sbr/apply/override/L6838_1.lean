theorem blk_L6838_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6838_1" ⟨"ff_aac_sbr_apply.L6838_1", B.L6838_1, some "ff_aac_sbr_apply.L6838_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hst, hm⟩ := T.L6838_1.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, DScW, dA, Args.d, CstW, FrE, FrRaw, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    TabW_push, FnW_push, AcW_push, OutW_push, PsW, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm h9
  simp only [B.L6838_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have e1 : BitVec.setWidth 64 (BitVec.setWidth 32 1#64) = 1#64 := by decide
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  -- exits
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6fca"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6fca") ?_
                 refine ⟨isSome_at L.L6fca, ?_, ?_⟩; rw [T.L6fca]
                 refine ⟨hC, ⟨?_, ?_⟩, ?_, 1, Or.inl rfl, ?_⟩)
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6fbe"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6fbe") ?_
                 refine ⟨isSome_at L.L6fbe, ?_, ?_⟩; rw [T.L6fbe]
                 refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6abf"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6abf") ?_
                 refine ⟨isSome_at L.L6abf, ?_, ?_⟩; rw [T.L6abf]
                 refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6838_2]; refine ⟨hC, ⟨?_, ?_⟩, ?_, hst, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    arg1, sbrA, e1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, DScW, CstW, FrD, FrE, FrS0, FrRaw, sbrA, arg0, arg1, arg3, arg4, TabW_push, FnW_push, AcW_push, OutW_push, PsW,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  all_goals (simp only [Mm, ApplyF, ScW, DScW, dA, Args.d, CstW, FrD, FrE, FrS0, FrRaw, sbrA, arg0, arg1, arg3, arg4, TabW_push, FnW_push, AcW_push, OutW_push, PsW,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd] at hm ⊢; sep_close hm)
