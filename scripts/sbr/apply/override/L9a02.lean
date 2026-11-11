theorem blk_L9a02 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a02" ⟨"ff_aac_sbr_apply.L9a02", B.L9a02, some "ff_aac_sbr_apply.L9a02_1"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPs, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, h9, h12, y, hK, hCy, hm⟩ := T.L9a02.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hPW : PsWF y.psc y.psh := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpl : y.psc.length = 764 := hPW.1
  have ha1 : isAligned 32 (t₀.regs.get64 .rsi) = true := hCy.2.1
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; have hPW' := PLift.up hPW; clear hK hCy hPW
  simp only [Mm, ApplyF, ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h12
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hR := PLift.up (⟨hrsp, hrbp, h9, h12⟩ : _ ∧ _ ∧ _ ∧ _)
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
    y.psc =@ (t₀.regs.get64 .rsi + 343840#64), 4 ?@ (t₀.regs.get64 .rsi + 344604#64),
    133200 ?@ (t₀.regs.get64 .rsi + 344608#64), y.psh =@ (t₀.regs.get64 .rsi + 477808#64),
    76 ?@ (t₀.regs.get64 .rsi + 477876#64),
    19456 ?@ (t₀.regs.get64 .rsi + 509024#64), 19456 ?@ (t₀.regs.get64 .rsi + 528480#64), e.PsTab] as Rc hRc
  have hpsl : s₀.dmem.loadInt (t₀.regs.get64 .rsi + 343840#64) 4
      = some (Int.ofBytes ((y.psc.drop 0).take 4)) := by
    have h0 : (0 : Nat) = (t₀.regs.get64 .rsi + 343840#64 - (t₀.regs.get64 .rsi + 343840#64)).toNat := by
      rw [BitVec.sub_self, BitVec.toNat_zero]
    rw [h0]
    sep_mem hm
    all_goals first | rfl | (rw [hpl]; (try rw [BitVec.sub_self, BitVec.toNat_zero]); decide)
  have hRc' := PLift.up hRc
  clear hRc
  dsimp only
  simp only [B.L9a02]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen [MachineWP.call_proc_spec_at ({ R := Rc, psc := y.psc, psh := y.psh } : PsArgs) "ff_ps_apply" hPs]
  all_goals try subst s₀
  all_goals try (have e := hRc'.down; subst e)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h12, hpsl, BitVec.add_assoc] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (simp only [Option.isSome_some]; done)
  case vc4 =>
    obtain ⟨hrsp, hrbp, h9, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a85") ?_
    refine ⟨isSome_at L.L9a85, ?_, Or.inr ⟨?_, ?_⟩⟩
    rotate_left
    · simp only [lex_var] at hn ⊢; exact hn
    · simp only [lex_var]; decide
    rw [T.L9a85]
    refine ⟨ch, c0, hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, h12, sbrA, arg0, arg1, dsN,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd]; done)
    · simp only [Mm, ApplyF, ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm
  case vc6 =>
    obtain ⟨hrsp, hrbp, h9, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a69") ?_
    refine ⟨isSome_at L.L9a69, ?_, Or.inr ⟨?_, ?_⟩⟩
    rotate_left
    · simp only [lex_var] at hn ⊢; exact hn
    · simp only [lex_var]; decide
    rw [T.L9a69]
    refine ⟨ch, c0, hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, h12, sbrA, arg0, arg1, dsN,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd]; done)
    · simp only [Mm, ApplyF, ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm
  case vc10 =>
    obtain ⟨hrsp, hrbp, h9, h12⟩ := hR.down
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc,
        PsApplyF, PsApplyPre, CallPre, arg0, arg1, arg2]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc,
        PsApplyC, arg0, arg1, arg2, arg3]
      refine ⟨?_, ?_, hPW'.down, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al16 (syn_al32 _ _ ha1 (by decide)),
        syn_al16 (syn_al32 _ _ ha1 (by decide))⟩
      · simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast, BitVec.toNat_setWidth,
          BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      · exact ps_gate2 ‹some (Int.ofBytes _) = some _› ‹CondCode.z.interp _ = false›
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, PsApplyPost, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      obtain ⟨h', hl, h6, hm2⟩ := ps_post_ex3 hm'
      clear hm'
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', -, h14', -⟩ := hsv
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a02_1]
      refine ⟨ch, c0, hC, ⟨hrsp', hrbp'⟩, ?_, ?_, ?_, { y with psh := h' }, hK'.down,
        ⟨ps_sbrwf_post hCy'.down.1 hl h6, hCy'.down.2⟩, ?_⟩
      · rw [hb']; try simp only [arg0]
      · rw [h12']; try simp only [sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h14']; try simp only [dsN]
      simp only [PsApplyF, Blocks, arg0, arg1, arg2, MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, h9, h12, BitVec.add_assoc, BitVec.reduceAdd] at hm2
      simp only [Mm, ApplyF]
      rw [show TabW { y with psh := h' } t₀ = TabW y t₀ from rfl, show OutW { y with psh := h' } t₀ = OutW y t₀ from rfl]
      simp only [ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm2
