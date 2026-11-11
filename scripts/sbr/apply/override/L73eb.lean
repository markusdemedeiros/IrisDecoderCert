set_option maxRecDepth 8000 in
theorem blk_L73eb (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L73eb" ⟨"ff_aac_sbr_apply.L73eb", B.L73eb, some "ff_aac_sbr_apply.L7401"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L73eb.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L73eb]
    vcgen
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7401"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7401") ?_; refine ⟨isSome_at L.L7401, ?_, ?_⟩; rw [T.L7401]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7401]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done
