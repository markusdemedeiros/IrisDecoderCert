theorem blk_L8e7c_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L8e7c_1" ⟨"ff_aac_sbr_apply.L8e7c_1", B.L8e7c_1, some "ff_aac_sbr_apply.L8e7c_2"⟩ := by
  obtain ⟨-, hSS, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, m, hK, hCy, hc0, hst, hch, hn4, hr13, hr15, hr14, hm1', hmm, hrbx, hr12, hm⟩ :=
    T.L8e7c_1.mp hs
  clear hs
  obtain ⟨hn1, hn8, hm1, hm48, hk32, hkm, hte, hmono, -, htl, -⟩ := env_wf hCy hst hch (hK.2.live hst)
  have hte3 := hte 4 (by omega)
  have hte4 := hte 5 hn4
  have hmo3 := hmono 4 (by omega)
  simp only [u8] at hte3 hte4 hmo3 hr15 hr12
  simp only [Nat.reduceAdd] at hmo3
  simp only [Mm, ApplyF, ArrW, DspW, ScW, c4, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm hr13 hr14 hr12
  have hm0 := hm
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  by_cases hlt : m < y.m1
  · obtain ⟨P, hP⟩ : ∃ P, t₀.regs.get64 .rsi + (488544#64 +
        BitVec.ofNat 64 (16 + 16 * ((y.d ch).te.getD 4 0).toNat + 320 * (y.kx1 + m))) = P := ⟨_, rfl⟩
    obtain ⟨N, hN⟩ : ∃ N, 8 * (2 * (((y.d ch).te.getD 5 0).toNat - ((y.d ch).te.getD 4 0).toNat)) = N :=
      ⟨_, rfl⟩
    have hin : (P - (t₀.regs.get64 .rsi + 488544#64)).toNat + N ≤ 20480 := by
      rw [← hP, ← hN, env_sub2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hPc : s₀.regs.get64 .r12 = P := by rw [hr12, ← hP]
    have hNc := envb_cnt (BitVec.ofNat 64 (2 * (((y.d ch).te.getD 5 0).toNat - ((y.d ch).te.getD 4 0).toNat))) _ rfl (by omega)
    rw [hN] at hNc
    rw [Block.carve hin (by decide), call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    rw [res_k0 hSt] at hm
    have hP' := PLift.up hP
    have hN' := PLift.up hN
    have hPc' := PLift.up hPc
    have hNc' := PLift.up hNc
    have hr12' := PLift.up hr12
    clear hP hN hPc hNc hr12
    dsimp only
    simp only [B.L8e7c_1]
    vcgen
    all_goals try subst_vars
    all_goals envb_name
    all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hr13,
        AddrIndex.offset64_scale8, BitVec.add_assoc]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr13, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, z, BitVec.add_assoc, BitVec.reduceAdd] at ld1
    all_goals try (revert ld1; sep_mem hm; intro ld1; (try simp only [Option.some.injEq] at ld1); subst ld1)
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl] at *
    all_goals try simp (disch := omega) only [envb_zext32] at *
    all_goals try (dsimp only at cc1)
    all_goals try (rw [env_nc_sub] at cc1; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, BitVec.toNat_ofNat,
      Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at cc1
    all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc1
    all_goals try (exfalso; omega)
    all_goals try sep_mem hm
    all_goals try (simp only [Option.isSome_some]; done)
    case vc5 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr13, Int64.toBitVec_ofNat_norm,
        AddrIndex.offset64_none, z, Nat.reducePow, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd] at ld2
      revert ld2
      sep_mem hm
      intro ld2
      (try simp only [Option.some.injEq] at ld2)
      subst ld2
      simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
      sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
        N ?@ P] as Rc hRc
      have hRc' := PLift.up hRc
      clear hRc
      refine MachineWP.CallsTo.of_procSpec Rc hSS (fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩)
      · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, Reg64s.get_low32,
          reduceCtorEq, ite_true, ite_false, z, hrsp, hrbp, hr13, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, hPc'.down, hr15, hNc'.down]
        sep_mem hm
        sep_close hm
      · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, Reg64s.get_low32,
          reduceCtorEq, ite_true, ite_false, z, hrsp, hrbp, hr13, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, hPc'.down, hr15, hNc'.down] at hpost
        obtain ⟨hrsp', hrbp', ⟨hsbx, hs12, hs13, hs14, hs15⟩, hm'⟩ := hpost
        have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
            a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
          intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
        simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
        refine MachineWP.nil_spec.le_wp s' ?_
        have e := hRc'.down
        subst e
        refine ⟨?_, ?_⟩
        rotate_left
        · simp only [lex_var]
          simp only [slot64, hrbp', hrbp, hsbx, BitVec.sub_sub_ofNat, Nat.reduceAdd, Reg64s.get64_set64,
            reduceCtorEq, ite_true, ite_false]
          (try sep_mem hm'); (try sep_mem hm0); (try simp only [Option.getD_some])
          envb_lex_split
          all_goals omega
        rw [T.L8e7c_2]
        refine ⟨hC, ⟨hrsp', hrbp'⟩, y, ch, c0, m, hK, hCy, hc0, hst, hch, hn4, ?_, ?_, ?_, hm1', hlt, ?_, ?_, ?_⟩
        · rw [hs13]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr13, arg1]
        · rw [hs15]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr15, u8]
        · rw [hs14]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr14, sbrA,
            BitVec.add_assoc, BitVec.reduceAdd]
        · rw [hsbx]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx]
        · rw [hs12]; (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, sbrA, u8, BitVec.add_assoc, BitVec.reduceAdd]); first | exact hP'.down.symm | exact hPc'.down.trans hP'.down.symm | rfl
        simp only [Mm, ApplyF, ArrW, DspW, ScW, c4, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        rw [Block.carve hin (by decide), call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        rw [res_k0 hSt]
        sep_close hm'
  · dsimp only
    simp only [B.L8e7c_1]
    vcgen
    all_goals try subst_vars
    all_goals envb_name
    all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hr13,
        AddrIndex.offset64_scale8, BitVec.add_assoc]
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr13, AddrIndex.offset64_none,
      Int64.toBitVec_ofNat_norm, z, BitVec.add_assoc, BitVec.reduceAdd] at ld1
    all_goals try (revert ld1; sep_mem hm; intro ld1; (try simp only [Option.some.injEq] at ld1); subst ld1)
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl] at *
    all_goals try simp (disch := omega) only [envb_zext32] at *
    all_goals try (dsimp only at cc1)
    all_goals try (rw [env_nc_sub] at cc1; rotate_left; rfl)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx, BitVec.toNat_ofNat,
      Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_le, Nat.not_lt] at cc1
    all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt] at cc1
    all_goals try (exfalso; omega)
    all_goals try sep_mem hm
    case vc2 =>
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L8ebf") ?_
      refine ⟨isSome_at L.L8ebf, ?_, ?_⟩
      · rw [T.L8ebf]
        refine ⟨hC, ⟨?_, ?_⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hn4, ?_, ?_, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hr13, hr14,
          sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]; done)
        simp only [Mm, ApplyF, ArrW, DspW, ScW, c4, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        sep_close hm
      · left
        simp only [lex_var]
        simp only [slot64, hrbp, hrbx, BitVec.sub_sub_ofNat, Nat.reduceAdd, Reg64s.get64_set64,
          reduceCtorEq, ite_true, ite_false]
        (try sep_mem hm); (try simp only [Option.getD_some])
        envb_lex_split
        all_goals (try simp only [BitVec.toNat_ofNat]); (try simp (disch := omega) only [Nat.mod_eq_of_lt]); omega
