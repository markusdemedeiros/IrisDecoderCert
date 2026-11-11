set_option maxRecDepth 8000 in
theorem blk_L7166 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7166" ⟨"ff_aac_sbr_apply.L7166", B.L7166, some "ff_aac_sbr_apply.L717f"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L7166.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L7166]
    vcgen
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L717f]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done
