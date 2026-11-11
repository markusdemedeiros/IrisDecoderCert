theorem blk_L9a69 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a69" ⟨"ff_aac_sbr_apply.L9a69", B.L9a69, some "ff_aac_sbr_apply.L9a7d"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMc, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, hax, y, hK, hCy, hm⟩ := T.L9a69.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ArrW, FrCs, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm hax h12
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hsl : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 176#64) 8) = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rsi + 509024#64).toInt)) := by
    sep_mem hm
    exact Eq.refl _
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
    19456 ?@ (t₀.regs.get64 .rsi + 528480#64), 19456 ?@ (t₀.regs.get64 .rsi + 509024#64)] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  dsimp only
  simp only [B.L9a69]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen [MachineWP.call_proc_spec_at Rc "memcpy" hMc]
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, hbx, h12, h14, hax, hsl]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  all_goals try sep_mem hm
  case vc1 => simp only [hsl, Option.isSome_some]
  case vc2 =>
    rename_i v hv
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrbp,
      Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv
    simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hv
    rw [hsl, Option.some.injEq] at hv
    subst hv
    have hw : (BitVec.setWidth 64 (BitVec.setWidth 32 19456#64)).toNat = 19456 := by decide
    have hv8 := BitVec.ofInt_ofBytes_toBytes 64 8 rfl (t₀.regs.get64 .rsi + 509024#64)
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      first | sep_mem hm | (simp only [BitVec.toNat_ofNat]; decide) | trivial
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, hax, hsl, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd,
        Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        BitVec.add_assoc, Option.getD_some, hw, hv8]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, hax, hsl, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd,
        Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        BitVec.add_assoc, Option.getD_some, hw, hv8] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', -, h14', -⟩ := hsv
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a7d]
      refine ⟨ch, c0, hC, ⟨hrsp', hrbp'⟩, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩
      · rw [hb']; simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, hbx]
      · rw [h12']; simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, h12, sbrA,
          arg1, BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h14']; simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, h14]
      have e := hRc'.down
      subst e
      simp only [Mm, ApplyF, ArrW, FrCs, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm'
