set_option maxRecDepth 8000 in
theorem blk_L71e0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L71e0" ⟨"ff_aac_sbr_apply.L71e0", B.L71e0, some "ff_aac_sbr_apply.L71e0_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hm⟩ := T.L71e0.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn
    dsimp only
    simp only [B.L71e0]
    vcgen
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd; dq_simp [] at *; intro hrbp h9 hd)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩)
  all_goals try simp only [hrbp, h9, hd] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, dq_zext32 x.d0.nnoise (by omega),
    dq_zext32 x.d1.nnoise (by omega), dq_zext32 x.nq (by omega)] at *
  all_goals try simp only [dq_test0 x.d0.nnoise (by omega), dq_test0 x.d1.nnoise (by omega), dq_test32 x.nq (by omega),
    dq_z32, Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7020"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7020") ?_; refine ⟨isSome_at L.L7020, ?_, ?_⟩; rw [T.L7020]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7226"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7226") ?_; refine ⟨isSome_at L.L7226, ?_, ?_⟩; rw [T.L7226]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L71e0_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done
