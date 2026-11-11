theorem blk_done (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.done" ⟨"ff_aac_sbr_apply.done", B.done, some "ff_aac_sbr_apply.L9b36"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hrsp, hrbp, hsv, hm⟩ := T.done.mp hs
  clear hs
  dsimp only
  simp only [B.done]
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self]
  case vc1 =>
    simp only [MachineData.retAddr_eq, hrsp, Width.bytes, Option.isSome_map]
    sep_mem hm
  case vc2 =>
    rename_i a ha
    right
    refine ⟨?_, rfl, trivial, hsv, ?_⟩
    · revert ha
      simp only [MachineData.retAddr_eq, hrsp, Width.bytes]
      sep_mem hm
      simp only [Option.map_some, Option.some.injEq, Width.bits, BitVec.ofInt_ofBytes_toBytes 64 8 rfl,
        Int64.ofBitVec_toBitVec]
      exact fun h => h.symm
    · sep_close hm
