theorem blk_L8a50_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L8a50_1" ⟨"ff_aac_sbr_apply.L8a50_1", B.L8a50_1, some "ff_aac_sbr_apply.L8a50_2"⟩ := by
  obtain ⟨-, hSS, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, j, p, q, hK, hCy, hc0, hst, hch, hj, hr14, hr12, hp, hrbx, htlt,
    hq1, hq2, hr13, hr15, hrdi, hrsi, hm⟩ := T.L8a50_1.mp hs
  clear hs
  obtain ⟨hn1, hn8, hm1, hm48, hk32, hkm, hte, hmono, hfr, htl, hfl⟩ := env_wf hCy hst hch (hK.2.live hst)
  have htb := env_tab hCy hst (u8 (y.d ch).freqRes (j + 1) = 0) (p + 1) (by omega)
  have hteJ := hte j (by omega)
  have hteJ1 := hte (j + 1) (by omega)
  have hmoJ := hmono j hj
  simp only [u8] at hteJ hteJ1 hmoJ hr12 hrsi hrdi hr15
  simp only [Mm, ApplyF, ArrW, DspW, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm hrdi hr15
  -- q < tb(p+1) ≤ kx1 + m1 ≤ 64
  have hq64 : q < 64 := by
    obtain ⟨-, h2, -, -⟩ := htb
    omega
  obtain ⟨P, hP⟩ : ∃ P, t₀.regs.get64 .rsi + (488544#64 +
      BitVec.ofNat 64 (16 + 16 * ((y.d ch).te.getD j 0).toNat + 320 * q)) = P := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, 8 * (2 * (((y.d ch).te.getD (j + 1) 0).toNat - ((y.d ch).te.getD j 0).toNat)) = N :=
    ⟨_, rfl⟩
  have hin : (P - (t₀.regs.get64 .rsi + 488544#64)).toNat + N ≤ 20480 := by
    rw [← hP, ← hN, env_sub2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hPc : s₀.regs.get64 .rdi = P := by rw [hrdi, ← hP]
  have hNc : 8 * ((BitVec.ofNat 64 (2 * (((y.d ch).te.getD (j + 1) 0).toNat - ((y.d ch).te.getD j 0).toNat))).toNat % 2 ^ 32) = N := by
    rw [← hN, BitVec.toNat_ofNat]; omega
  have hm0 := hm
  rw [Block.carve hin (by decide), call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  rw [res_k0 hSt] at hm
  have hP' := PLift.up hP
  have hN' := PLift.up hN
  have hPc' := PLift.up hPc
  have hNc' := PLift.up hNc
  have hr15' := PLift.up hr15
  clear hP hN hPc hNc hr15
  dsimp only
  simp only [B.L8a50_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64_none, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      AddrIndex.offset64_scale8, BitVec.add_assoc]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  case vc2 =>
      rename_i v1 hv1
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, AddrIndex.offset64_none, z,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat,
        Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd] at hv1
      try simp only [Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at hv1
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hv1
      revert hv1
      sep_mem hm
      intro hv1
      simp only [Option.some.injEq] at hv1
      subst hv1
      simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, arg1]
      try simp only [BitVec.add_assoc, BitVec.reduceAdd]
      sep_mem hm
  case vc4 =>
      rename_i v1 hv1 v hv
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, AddrIndex.offset64_none, z,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat,
        Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd] at hv1
      try simp only [Nat.reduceMod, Nat.reducePow, Nat.reduceSub] at hv1
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hv1
      revert hv1
      sep_mem hm
      intro hv1
      simp only [Option.some.injEq] at hv1
      subst hv1
      simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, arg1]
      dsimp only at hv
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Int64.toBitVec_ofNat_norm,
        AddrIndex.offset64_none, z, Nat.reducePow, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, arg1] at hv
      revert hv
      sep_mem hm
      intro hv
      (try simp only [Option.some.injEq] at hv)
      subst hv
      simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
      sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
        N ?@ P] as Rc hRc
      have hRc' := PLift.up hRc
      clear hRc
      refine MachineWP.CallsTo.of_procSpec Rc hSS (fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩)
      · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, Reg64s.get_low32,
          reduceCtorEq, ite_true, ite_false, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, hPc'.down, hrsi, hNc'.down]
        sep_mem hm
        sep_close hm
      · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, Reg64s.get_low32,
          reduceCtorEq, ite_true, ite_false, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, hPc'.down, hrsi, hNc'.down] at hpost
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
          simp only [slot64, hrbp', hrbp, hsbx, hs13, BitVec.sub_sub_ofNat, Nat.reduceAdd, Reg64s.get64_set64,
            reduceCtorEq, ite_true, ite_false]
          (try sep_mem hm'); (try sep_mem hm0); (try simp only [Option.getD_some])
          env_lex_split
          all_goals omega
        rw [T.L8a50_2]
        refine ⟨hC, ⟨hrsp', hrbp'⟩, y, ch, c0, j, p, q, hK, hCy, hc0, hst, hch, hj, ?_, ?_, hp, ?_, htlt, hq1, hq2, ?_, ?_, ?_⟩
        · rw [hs14]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr14]
        · rw [hs12]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr12, u8]
        · rw [hsbx]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbx]
        · rw [hs13]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr13]
        · rw [hs15]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr15'.down, sbrA, u8,
            BitVec.add_assoc, BitVec.reduceAdd]
        simp only [Mm, ApplyF, ArrW, DspW, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        rw [Block.carve hin (by decide), call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        rw [res_k0 hSt]
        sep_close hm'
