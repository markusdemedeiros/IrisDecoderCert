theorem blk_L6fca (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6fca" ⟨"ff_aac_sbr_apply.L6fca", B.L6fca, some "ff_aac_sbr_apply.L6ff7"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, nch, hnch, hm⟩ := T.L6fca.mp hs
  clear hs
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, FrS0] at hm
  dsimp only
  simp only [B.L6fca]
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, hrbp, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7044") ?_
  refine ⟨isSome_at L.L7044, ?_, ?_⟩; rw [T.L7044]
  all_goals try edge_step
  refine ⟨hC, ⟨?_, ?_⟩, ?_, 0, nch, by omega, by omega, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, arg1, and_self]; done)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self,
      BitVec.reduceSetWidth]
  · simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, FrM, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd]
    sep_close hm
