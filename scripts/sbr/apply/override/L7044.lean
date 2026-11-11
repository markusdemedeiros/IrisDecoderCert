theorem blk_L7044 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7044" ⟨"ff_aac_sbr_apply.L7044", B.L7044, some "ff_aac_sbr_apply.L7044_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hax, hm⟩ := T.L7044.mp hs
  clear hs
  simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrM] at hm
  dsimp only
  simp only [B.L7044]
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, hrbp, h9, hax]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7044_1])
  rotate_left
  · simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax]
    obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
    · rw [if_pos (by decide), if_pos (by decide)]; exact Nat.le_refl _
    · rw [if_neg (by decide), if_neg (by decide)]; exact Nat.le_refl _
  refine ⟨hC, ⟨?_, ?_⟩, ?_, ch, nch, hch, hnch, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, arg1, and_self]; done)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax]
    obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
    all_goals rfl
  · simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrDq]
    sep_close hm
