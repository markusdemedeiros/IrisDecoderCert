theorem blk_L7020_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7020_1" ⟨"ff_aac_sbr_apply.L7020_1", B.L7020_1, some "ff_aac_sbr_apply.L7020_2"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hm⟩ := T.L7020_1.mp hs
  clear hs
  simp only [lex_var, hd] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrL1, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn
    dsimp only
    simp only [B.L7020_1]
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
    CondCode.interp, StatusFlags.from_result] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7020_2])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrL2, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done
