theorem blk_L6abf (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6abf" ⟨"ff_aac_sbr_apply.L6abf", B.L6abf, some "ff_aac_sbr_apply.L6b00"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hm⟩ := T.L6abf.mp hs
  clear hs
  obtain ⟨-, -, -, hnn, -, -, hnq⟩ := dq_facts hC.1
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    Nat.reduceMul, Nat.reduceAdd] at hm h9
  rw [← h9] at hm
  dsimp only
  simp only [B.L6abf]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
    AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, z] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try (refine dq_isSome_add0 ?_; sep_mem hm)
  all_goals try (simp; done)
  all_goals try simp only [dq_c4_val, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, dq_xlo_zext, CondCode.interp_z, CondCode.interp_nz,
    StatusFlags.zf_from_result, BitVec.and_self] at *
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74de") ?_; refine ⟨isSome_at L.L74de, ?_, ?_⟩; rw [T.L74de])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6b12") ?_; refine ⟨isSome_at L.L6b12, ?_, ?_⟩; rw [T.L6b12])
  all_goals try edge_step
  -- L6b12
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨0, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩; rotate_left 8)
  -- L74de
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩; rotate_left 3)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, CstW, dA, sbrA, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]; rw [← h9]; sep_close hm)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, and_self, hrsp, hrbp, h9, arg1]; done)
  all_goals try (apply dq_ne0 _ (by omega); assumption)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, dq_inc32 _ hnn,
    BitVec.xor_self, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0),
    dq_xlo_zext]; done)
  all_goals (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self]; decide)
