theorem blk_L9a85_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_3" ⟨"ff_aac_sbr_apply.L9a85_3", B.L9a85_3, some "ff_aac_sbr_apply.L9a85_4"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQ0, hQ1, -⟩ := hc
  have hQ := syn_qspec (x := x) hQ0 hQ1
  clear hQ0 hQ1
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, hbx, h15, h13, h12, h14, y, hK, hCy, hdi, hsi, hcx, hdx, h8, h9, v, hw1, hw2, hm⟩ :=
    T.L9a85_3.mp hs
  clear hs
  have hdy : dsN y = dsN x := by simp only [dsN, hK.2.2.2.1, hK.2.2.2.2.2.2.2]
  have hB : (1280 ?@ (t₀.regs.get64 .rsi + 558560#64) : Mem 64 → Prop)
      = 256 ?@ (t₀.regs.get64 .rsi + 558560#64) ⋆ (256 ?@ (t₀.regs.get64 .rsi + 558816#64)
        ⋆ 768 ?@ (t₀.regs.get64 .rsi + 559072#64)) := by
    rw [show (1280 : Nat) = 256 + (256 + 768) from rfl, Block.split _ 256 (256 + 768) (by decide),
      Block.split _ 256 768 (by decide)]
    simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
  have hB' := PLift.up hB; clear hB
  simp only [MmS, SynArgs, ApplyF] at hm
  rw [show ScW (y.setV0 v) t₀ = ScW y t₀ from rfl, show TabW (y.setV0 v) t₀ = TabW y t₀ from rfl,
    show AcW (y.setV0 v) t₀ = AcW y t₀ from rfl, show OutW (y.setV0 v) t₀ = OutW y t₀ from rfl,
    show FnW e (y.setV0 v) t₀ = FnW e y t₀ from rfl, show PsW (y.setV0 v) t₀ = PsW y t₀ from rfl] at hm
  rw [c8_div _ _ (syn_dsN_le x), res_qmf k (t₀.regs.get64 .rsp - 0x1e8#64) (by (try simp only [applyNeed] at hSt); bv_omega)] at hm
  simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
    Args.setV0, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
    BitVec.ofNat_eq_ofNat] at hm
  rw [hB'.down] at hm
  have hq := qv_carve (t₀.regs.get64 .rsi + 255200#64) (dsN x) y.d1.vOff
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
  rw [hq] at hm
  have hq' := PLift.up hq; clear hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (syn_dsN_le x) with hd | hd
  · rw [syn_win0 hd] at hm
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 496#64), Reserve (304 + k) (t₀.regs.get64 .rsp - 496#64),
      19456 ?@ (t₀.regs.get64 .rsi + 528480#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64),
      qmfVSize (dsN x) y.d1.vOff ?@ (t₀.regs.get64 .rsi + 255200#64),
      cell4 (t₀.regs.get64 .rsi + 269664#64) y.d1.vOff,
      (8192 >>> dsN x) ?@ t₀.regs.get64 .r8, (2560 >>> dsN x) ?@ qmfWin (dsN x),
      4 ?@ lab "LCPI15_1", 16 ?@ lab "ps_mask2", 16 ?@ lab "ff_ps_neg",
      FnCell (t₀.regs.get64 .rsi + 559888#64) e.fs.qfs.negOdd64,
      FnCell (t₀.regs.get64 .rsi + 559912#64) e.fs.qfs.deintNeg,
      FnCell (t₀.regs.get64 .rsi + 559920#64) e.fs.qfs.deintBfly,
      FnCell y.fdsp e.fs.qfs.fmul, FnCell (y.fdsp + 48#64) e.fs.qfs.fmulAdd, e.Ctx y.synCtx, e.TxTab,
      c8 (t₀.regs.get64 .rsp - 488#64) (t₀.regs.get64 .rsi + 558560#64),
      c8 (t₀.regs.get64 .rsp - 480#64) (t₀.regs.get64 .rsi + 255200#64),
      c8 (t₀.regs.get64 .rsp - 472#64) (t₀.regs.get64 .rsi + 269664#64),
      Int.toBytes 4 (dsN x : Int) =@ (t₀.regs.get64 .rsp - 464#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    simp only [B.L9a85_3]
    vcgen [MachineWP.call_proc_spec_at
      ({ R := Rc, mdctBuf := t₀.regs.get64 .rsi + 558560#64, v0 := t₀.regs.get64 .rsi + 255200#64,
         vOff := t₀.regs.get64 .rsi + 269664#64, off := y.d1.vOff } : QmfArgs) "sbr_qmf_synthesis" hQ]
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    all_goals try subst s₀
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        Nat.reduceSub]
      sep_mem hm
      sep_close hm
    · obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hD0, -⟩, ha1, hsA0, ha3, ha4, -, -, -, -, hds, hneg, ⟨-, hus, hm2⟩, -, -⟩ := hCy
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv1, hv2, -⟩ := hD0
      simp only [sbrA, arg1, arg3, arg4] at ha1 hsA0 ha3 ha4
      simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfC, qmfWin, hd, Nat.one_ne_zero, ite_true, ite_false, Nat.reduceShiftRight, Int64.ofBitVec_toBitVec]
      exact ⟨by decide, trivial, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al32 _ _ ha1 (by decide),
        syn_al32 _ _ ha1 (by decide), ha4, ‹_›, hm2, hneg, hv1, hv2⟩
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have e := hRc'.down; subst e
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', h13', h14', h15'⟩ := hsv
      sep_pull hm' [VOffW (t₀.regs.get64 .rsi + 269664#64)] as F hF
      obtain ⟨v', hw1', hw2', hm2⟩ := voffw_cell hm'
      subst hF
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a85_4]
      refine ⟨ch, c0, hC, by rw [hrsp']; bv_omega, hrbp', (y.setV0 v).setV1 v', hK,
        applyc_setV1 (applyc_setV0 hCy hw1 hw2) hw1' hw2', ?_⟩
      simp only [Mm, ApplyF]
      rw [show ScW ((y.setV0 v).setV1 v') t₀ = ScW y t₀ from rfl, show TabW ((y.setV0 v).setV1 v') t₀ = TabW y t₀ from rfl,
        show AcW ((y.setV0 v).setV1 v') t₀ = AcW y t₀ from rfl, show OutW ((y.setV0 v).setV1 v') t₀ = OutW y t₀ from rfl,
        show FnW e ((y.setV0 v).setV1 v') t₀ = FnW e y t₀ from rfl]
      rw [res_args k hSt, BitVec.sub_sub_ofNat,
        res_qmf k (t₀.regs.get64 .rsp - 0x1c8#64 - 32#64) (by (try simp only [applyNeed] at hSt); bv_omega)]
      simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
        Args.setV0, Args.setV1, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
        BitVec.ofNat_eq_ofNat]
      rw [hB'.down, hq'.down]
      have h8 : (8 ?@ (t₀.regs.get64 .rsp - 464#64) : Mem 64 → Prop)
          = 4 ?@ (t₀.regs.get64 .rsp - 464#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 460#64) := by
        rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide),
          syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide)]
      rw [h8]
      simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide), Nat.reduceSub] at hm2
      simp only [c4, cell4, FnCell, lab, dsN, qmfWin] at hm2 ⊢
      have hd0 := hd
      try simp only [dsN] at hd
      simp only [hd, ite_true, Nat.reduceShiftRight] at hm2 ⊢
      simp only [FrCs, hd0, BitVec.ofNat_eq_ofNat] at hm2 ⊢
      try simp only [PsW] at hm2 ⊢
      sep_close hm2
  · rw [syn_win1 hd] at hm
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 496#64), Reserve (304 + k) (t₀.regs.get64 .rsp - 496#64),
      19456 ?@ (t₀.regs.get64 .rsi + 528480#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64),
      qmfVSize (dsN x) y.d1.vOff ?@ (t₀.regs.get64 .rsi + 255200#64),
      cell4 (t₀.regs.get64 .rsi + 269664#64) y.d1.vOff,
      (8192 >>> dsN x) ?@ t₀.regs.get64 .r8, (2560 >>> dsN x) ?@ qmfWin (dsN x),
      4 ?@ lab "LCPI15_1", 16 ?@ lab "ps_mask2", 16 ?@ lab "ff_ps_neg",
      FnCell (t₀.regs.get64 .rsi + 559888#64) e.fs.qfs.negOdd64,
      FnCell (t₀.regs.get64 .rsi + 559912#64) e.fs.qfs.deintNeg,
      FnCell (t₀.regs.get64 .rsi + 559920#64) e.fs.qfs.deintBfly,
      FnCell y.fdsp e.fs.qfs.fmul, FnCell (y.fdsp + 48#64) e.fs.qfs.fmulAdd, e.Ctx y.synCtx, e.TxTab,
      c8 (t₀.regs.get64 .rsp - 488#64) (t₀.regs.get64 .rsi + 558560#64),
      c8 (t₀.regs.get64 .rsp - 480#64) (t₀.regs.get64 .rsi + 255200#64),
      c8 (t₀.regs.get64 .rsp - 472#64) (t₀.regs.get64 .rsi + 269664#64),
      Int.toBytes 4 (dsN x : Int) =@ (t₀.regs.get64 .rsp - 464#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    simp only [B.L9a85_3]
    vcgen [MachineWP.call_proc_spec_at
      ({ R := Rc, mdctBuf := t₀.regs.get64 .rsi + 558560#64, v0 := t₀.regs.get64 .rsi + 255200#64,
         vOff := t₀.regs.get64 .rsi + 269664#64, off := y.d1.vOff } : QmfArgs) "sbr_qmf_synthesis" hQ]
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    all_goals try subst s₀
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        Nat.reduceSub]
      sep_mem hm
      sep_close hm
    · obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hD0, -⟩, ha1, hsA0, ha3, ha4, -, -, -, -, hds, hneg, ⟨-, hus, hm2⟩, -, -⟩ := hCy
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv1, hv2, -⟩ := hD0
      simp only [sbrA, arg1, arg3, arg4] at ha1 hsA0 ha3 ha4
      simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfC, qmfWin, hd, Nat.one_ne_zero, ite_true, ite_false, Nat.reduceShiftRight, Int64.ofBitVec_toBitVec]
      exact ⟨by decide, trivial, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al32 _ _ ha1 (by decide),
        syn_al32 _ _ ha1 (by decide), ha4, ‹_›, hm2, hneg, hv1, hv2⟩
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have e := hRc'.down; subst e
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', h13', h14', h15'⟩ := hsv
      sep_pull hm' [VOffW (t₀.regs.get64 .rsi + 269664#64)] as F hF
      obtain ⟨v', hw1', hw2', hm2⟩ := voffw_cell hm'
      subst hF
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a85_4]
      refine ⟨ch, c0, hC, by rw [hrsp']; bv_omega, hrbp', (y.setV0 v).setV1 v', hK,
        applyc_setV1 (applyc_setV0 hCy hw1 hw2) hw1' hw2', ?_⟩
      simp only [Mm, ApplyF]
      rw [show ScW ((y.setV0 v).setV1 v') t₀ = ScW y t₀ from rfl, show TabW ((y.setV0 v).setV1 v') t₀ = TabW y t₀ from rfl,
        show AcW ((y.setV0 v).setV1 v') t₀ = AcW y t₀ from rfl, show OutW ((y.setV0 v).setV1 v') t₀ = OutW y t₀ from rfl,
        show FnW e ((y.setV0 v).setV1 v') t₀ = FnW e y t₀ from rfl]
      rw [res_args k hSt, BitVec.sub_sub_ofNat,
        res_qmf k (t₀.regs.get64 .rsp - 0x1c8#64 - 32#64) (by (try simp only [applyNeed] at hSt); bv_omega)]
      simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
        Args.setV0, Args.setV1, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
        BitVec.ofNat_eq_ofNat]
      rw [hB'.down, hq'.down]
      have h8 : (8 ?@ (t₀.regs.get64 .rsp - 464#64) : Mem 64 → Prop)
          = 4 ?@ (t₀.regs.get64 .rsp - 464#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 460#64) := by
        rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide),
          syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide)]
      rw [h8]
      simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide), Nat.reduceSub] at hm2
      simp only [c4, cell4, FnCell, lab, dsN, qmfWin] at hm2 ⊢
      have hd0 := hd
      try simp only [dsN] at hd
      simp only [hd, Nat.one_ne_zero, ite_false, Nat.reduceShiftRight] at hm2 ⊢
      simp only [FrCs, hd0, BitVec.ofNat_eq_ofNat] at hm2 ⊢
      try simp only [PsW] at hm2 ⊢
      sep_close hm2
