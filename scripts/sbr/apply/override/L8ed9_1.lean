theorem blk_L8ed9_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L8ed9_1" ⟨"ff_aac_sbr_apply.L8ed9_1", B.L8ed9_1, some "ff_aac_sbr_apply.L8ed9_2"⟩ := by
  obtain ⟨-, hSS, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hn4, hrdi, hrax, hr15, hr12, hr8, hm⟩ :=
    T.L8ed9_1.mp hs
  clear hs
  obtain ⟨hn1, hn8, hm1, hm48, hk32, hkm, hte, hmono, -, htl, -⟩ := env_wf hCy hst hch (hK.2.live hst)
  have hte3 := hte 5 (by omega)
  have hte4 := hte 6 hn4
  have hmo3 := hmono 5 (by omega)
  simp only [u8] at hte3 hte4 hmo3 hrax hr15 hr12
  simp only [Nat.reduceAdd] at hmo3
  simp only [Mm, ApplyF, ArrW, DspW, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm hrdi hr8
  -- the callee footprint `N ?@ P` inside X_high
  obtain ⟨P, hP⟩ : ∃ P, t₀.regs.get64 .rsi + (488544#64 +
      BitVec.ofNat 64 (16 + 16 * ((y.d ch).te.getD 5 0).toNat + 320 * y.kx1)) = P := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, 8 * (2 * (((y.d ch).te.getD 6 0).toNat - ((y.d ch).te.getD 5 0).toNat)) = N :=
    ⟨_, rfl⟩
  have hin : (P - (t₀.regs.get64 .rsi + 488544#64)).toNat + N ≤ 20480 := by
    rw [← hP, ← hN, env_sub2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  have hPc : s₀.regs.get64 .rdi + (s₀.regs.get64 .rax * 8#64 + 16#64) = P := by
    rw [hrdi, hrax, ← hP, BitVec.add_assoc]; congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  have hr15' : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r15) + BitVec.setWidth 32 (s₀.regs.get64 .r15))
      = BitVec.ofNat 64 (2 * (((y.d ch).te.getD 6 0).toNat - ((y.d ch).te.getD 5 0).toNat)) := by
    rw [hr15, envb_dbl _ (by omega)]
  have hNc := envb_cnt (BitVec.ofNat 64 (2 * (((y.d ch).te.getD 6 0).toNat - ((y.d ch).te.getD 5 0).toNat))) _ rfl (by omega)
  rw [hN] at hNc
  have hm0 := hm
  rw [Block.carve hin (by decide), call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  rw [res_k0 hSt] at hm
  have hP' := PLift.up hP
  have hN' := PLift.up hN
  have hPc' := PLift.up hPc
  have hNc' := PLift.up hNc
  have hr15'' := PLift.up hr15'
  have hrdi' := PLift.up hrdi
  clear hP hN hPc hNc hr15'
  have hadd : ∀ a b : BitVec 64, BitVec.setWidth 64 16#64 + (a + b) = a + (b + 16#64) := by
    intro a b; rw [BitVec.setWidth_eq, BitVec.add_comm _ (a + b), BitVec.add_assoc]
  dsimp only
  simp only [B.L8ed9_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, Reg64s.get_low32, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64_none, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hr8,
      AddrIndex.offset64_scale8, BitVec.add_assoc]
  all_goals try sep_mem hm
  case vc3 =>
    rename_i v hv
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr8, Int64.toBitVec_ofNat_norm,
      AddrIndex.offset64_none, z, Nat.reducePow, Nat.reduceMod, BitVec.add_assoc, BitVec.reduceAdd] at hv
    revert hv
    sep_mem hm
    intro hv
    simp only [Option.some.injEq] at hv
    subst hv
    simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec]
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
      N ?@ P] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hSS (fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩)
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, Reg64s.get_low32,
        reduceCtorEq, ite_true, ite_false, z, hrsp, hrbp, hr8, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd, Blocks, hadd, BitVec.add_assoc, hPc'.down, hr15''.down, hNc'.down]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, Reg64s.get_low32,
        reduceCtorEq, ite_true, ite_false, z, hrsp, hrbp, hr8, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd, Blocks, hadd, BitVec.add_assoc, hPc'.down, hr15''.down, hNc'.down] at hpost
      obtain ⟨hrsp', hrbp', ⟨-, hs12, hs13, hs14, hs15⟩, hm'⟩ := hpost
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
        simp only [slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        (try sep_mem hm'); (try sep_mem hm0); (try simp only [Option.getD_some])
        envb_lex_split
        all_goals omega
      rw [T.L8ed9_2]
      refine ⟨hC, ⟨hrsp', hrbp'⟩, y, ch, c0, hK, hCy, hc0, hst, hch, hn4, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hs13]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr8, arg1]
      · rw [hs12]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr12, u8]
      · rw [hs15]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hr15''.down, u8]
      · rw [hs14]; try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdi'.down, sbrA,
          BitVec.add_assoc, BitVec.reduceAdd]
      simp only [Mm, ApplyF, ArrW, DspW, sbrA, Blocks, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [Block.carve hin (by decide), call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      rw [res_k0 hSt]
      sep_close hm'
