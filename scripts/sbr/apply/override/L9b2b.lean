theorem blk_L9b2b (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b2b" ⟨"ff_aac_sbr_apply.L9b2b", B.L9b2b, some "ff_aac_sbr_apply.done"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, hrsp, hrbp, hm⟩ := T.L9b2b.mp hs
  clear hs
  dsimp only
  simp only [B.L9b2b]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Width.bytes, Width.bytesv, BitVec.reduceAdd, z, hrsp, hrbp, and_self] at *
  all_goals try simp only [BitVec.sub_add_ofNat_cancel, BitVec.sub_ofNat_add_eight, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_mem hm
  case vc7 =>
    sep_vals hm
    refine ⟨?_, by var_step⟩
    rw [T.done]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.sub_zero,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
    simp only [applyNeed]
    rw [reserve_frame k hSt, frame_split]
    sep_close hm
