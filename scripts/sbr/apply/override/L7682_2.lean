theorem blk_L7682_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_2" ⟨"ff_aac_sbr_apply.L7682_2", B.L7682_2, some "ff_aac_sbr_apply.L7682_3"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, hC, ⟨hrsp, hrbp⟩, hch, h9, h12, hdx, hcx, h14, y, hK, hCy, hm⟩ := T.L7682_2.mp hs
  clear hs
  have hfd := hK.1.2.2.2.2.2.1
  simp only [Mm, ApplyF, FnW, FrA2, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm h12
  dsimp only
  simp only [B.L7682_2]
  obtain ⟨c0, hc0⟩ : ∃ c0, BitVec.setWidth 32 (s₀.regs.get64 .rcx) = c0 := ⟨_, rfl⟩
  have hc0b : c0.getLsbD 0 = decide (ch = 0) := by
    rw [← hc0, BitVec.getLsbD_setWidth, hcx]; rfl
  have hc0' := PLift.up hc0
  clear hc0
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_3]
                 refine ⟨ch, c0, hC, ⟨?_, ?_⟩, hch, hc0b, ?_, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
  all_goals try (exact zf_test1 _ _ hcx)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h12, hdx, hcx, h14, sbrA, arg1, BitVec.add_assoc, hc0'.down] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (simp only [Mm, ApplyF, FnW, FrA3, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd]; sep_close hm)
  all_goals try var_step
  all_goals try (simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]; exact Nat.le_refl _)
