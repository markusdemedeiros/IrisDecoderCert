theorem blk_L881c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L881c" ⟨"ff_aac_sbr_apply.L881c", B.L881c, some "ff_aac_sbr_apply.L881c_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hrbx, hr8, hr10, hrax, hm⟩ := T.L881c.mp hs
  clear hs
  obtain ⟨hn1, hn8, -⟩ := env_wf hCy hst hch (hK.2.live hst)
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals simp only [Mm, FrO, ApplyF, DArrW, Blocks, dA, Nat.reduceMul, Nat.reduceAdd, Args.d, Nat.one_ne_zero, ↓reduceIte] at hm hrbx hr10 hrax hn1 hn8 ⊢
  all_goals try dsimp only
  all_goals have hm0 := hm
  all_goals simp only [B.L881c]
  all_goals vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hrbx, hr8, hr10, hrax,
      AddrIndex.offset64_scale2, BitVec.reduceToNat, Nat.reduceEqDiff, ↓reduceIte]
  all_goals try simp (disch := omega) only [env_sw, env_lea3_shl4]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try dsimp only
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.add_zero, Mem.sub_base_add_add, Mem.sub_base_add, BitVec.toNat_mul, BitVec.toNat_add,
        BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.reducePow]; simp (disch := omega) only [Nat.mod_eq_of_lt]; omega)
  all_goals refine ⟨?_, ?_⟩
  all_goals try (rw [T.L881c_1]; refine ⟨hC, ⟨?_, ?_⟩, y, _, c0, hK, hCy, hc0, hst, hch, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hrbx, hr8, hrax, Args.d, ↓reduceIte]; done)
  all_goals try (simp only [Mm, FrE1, ApplyF, DArrW, Blocks, dA, Nat.reduceMul, Nat.reduceAdd]; sep_close hm)
  all_goals try (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp]
                 simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd])
  all_goals sep_mem hm
  all_goals sep_mem hm0
  all_goals first | exact Nat.le_refl _ | (simp only [Option.getD_some]; lex_cmp)
