theorem blk_L86b0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L86b0" ⟨"ff_aac_sbr_apply.L86b0", B.L86b0, some "ff_aac_sbr_apply.L86b0_1"⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMs, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC0, ⟨hrsp, hrbp⟩, y, ch, c0, j, i, hK, hC, hc0, hst, hch, hj, h_rbx, h_r14, h_r12, h_r15, hf4, h_r13, hf6, hf7, hf8, h_rax, h_rcx, h_rdx, hm⟩ := T.L86b0.mp hs
  clear hs
  have hb := mapb_bounds hC
  have hj8 := mapb_j_lt8 hC hch hj
  have hcnt := mapb_cnt hC (u8 (y.d ch).freqRes (j + 1) = 0)
  generalize u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) i = a at *
  generalize u16 (if u8 (y.d ch).freqRes (j + 1) = 0 then y.ftLow else y.ftHigh) (i + 1) = b at *
  simp only [Mm, ApplyF, ArrW, Blocks, FrMs, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd] at hm
  rw [mapb_carve (t₀.regs.get64 .rsi + 166176#64 + 385856#64) 384 (48 * j + (a - y.kx1)) (b - a) (by omega) (by omega)] at hm
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
    (b - a) ?@ (t₀.regs.get64 .rsi + 166176#64 + 385856#64 + BitVec.ofNat 64 (48 * j + (a - y.kx1)))]
    as Rc hRc
  have hm0 := hm
  dsimp only
  simp only [B.L86b0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen [MachineWP.call_proc_spec_at Rc "memset" hMs]
  all_goals try subst_vars
  all_goals try dsimp only
  all_goals mapb_name
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, z, hrsp, hrbp, h_rax, h_rcx, h_rdx, h_r14, h_r13]
  have hrdi : t₀.regs.get64 Reg64.rsi + 166176#64 + 385856#64 + BitVec.ofNat 64 (48 * j) +
      BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (a - y.kx1))) =
      t₀.regs.get64 Reg64.rsi + 166176#64 + 385856#64 + BitVec.ofNat 64 (48 * j + (a - y.kx1)) := by
    rw [mapb_zx32 _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]
  have hcnt' : BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 b) - BitVec.setWidth 32 (BitVec.ofNat 64 a)))) =
      BitVec.ofNat 64 (b - a) := by
    rw [mapb_sub32 a b (by omega) (by omega), mapb_sext _ (by omega)]
  refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
  rotate_left 2
  · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
    sep_mem hm
  · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
    simp only [MemsetF, Blocks, arg0, arg2, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdi, hcnt', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b - a < 2 ^ 64 by omega)]
    sep_mem hm
    sep_close hm
  · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
    obtain ⟨hrsp', hrbp', hsv, hm1⟩ := hpost
    have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
      intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
    simp only [Blocks, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrdi, hcnt', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show b - a < 2 ^ 64 by omega)] at hm1
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    rotate_left
    · ((try simp only [lex_var]); lex_guard_lex; (try simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, BitVec.ofInt_natCast, z, hrsp', hrbp', hrsp, hrbp, hsv.2.2.1, h_r13]); (try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]); (try sep_mem hm1); (try sep_mem hm); (try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl, BitVec.ofInt_toInt]); lex_guard_le; (repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)); first | exact Nat.le_refl _ | ((with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_); ((try simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]); (try simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, BitVec.zero_eq, BitVec.toNat_zero, BitVec.toNat_setWidth, BitVec.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, BitVec.ofInt_natCast]); (try simp only [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]); all_goals omega)))
    rw [T.L86b0_1]
    refine ⟨hC0, ⟨hrsp', hrbp'⟩, y, ch, c0, j, i + 1, hK, hC, hc0, hst, hch, hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsv.1, h_rbx]; (try simp only [dA, sbrA, Nat.reduceMul, Nat.reduceAdd])
    · rw [hsv.2.2.2.1, h_r14]; (try simp only [sbrA, Nat.reduceMul, Nat.reduceAdd])
    · rw [hsv.2.1, h_r12]; (try simp only [sbrA, Nat.reduceMul, Nat.reduceAdd])
    · rw [hsv.2.2.2.2, h_r15]; (try simp only [u8, Args.d, sbrA, Nat.reduceMul, Nat.reduceAdd])
    · simp only [u8, Args.d]; omega
    · rw [hsv.2.2.1]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
    simp only [Mm, ApplyF, ArrW, Blocks, FrMs, sbrA, arg0, arg1, Nat.reduceMul, Nat.reduceAdd]
    rw [mapb_carve (t₀.regs.get64 .rsi + 166176#64 + 385856#64) 384 (48 * j + (a - y.kx1)) (b - a) (by omega) (by omega)]
    rw [call_res k hSt]
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_close hm1
