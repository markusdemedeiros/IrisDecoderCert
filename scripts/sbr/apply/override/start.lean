theorem blk_start (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply" ⟨"ff_aac_sbr_apply", B.start, some "ff_aac_sbr_apply.start_1"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨rfl, ⟨hm, hC⟩⟩ := T.start.mp hs
  simp only [CallPre, applyNeed] at hm
  rw [reserve_frame k hSt, frame_split] at hm
  dsimp only
  simp only [B.start]
  clear hs
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd,
      Width.bytes, BitVec.add_zero, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub,
    Nat.reduceLeDiff] at *
  case vc9 =>
    rw [T.start_1]
    refine ⟨⟨hC, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, arg0, arg1, arg2, arg3, arg4]
    case refine_8 =>
      sep_mem hm
      dsimp only [Mm, FrA, c8, arg3, arg4]
      sep_close hm
    case refine_9 => var_step
  all_goals sep_mem hm
