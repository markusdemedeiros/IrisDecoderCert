import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetE4
import Kraken.X64.Examples.Sbr.Parse.ResetA1W

/-!
# `sbr_reset`: `sbr_make_f_derived`, the 16-wide `f_tablelow` copy (`L2a30`, shard B, env)

Four `vmovdqu` loads of 16 bytes of `f_tablehigh` (entries `2(m+1)-p ..`), `vpshufb .LCPI5_6`
keeps every other `uint16_t` in the low quadword (`rsG_shuf`), `vpunpcklqdq` pairs them, and two
`vmovdqu` stores write `f_tablelow[m+1 .. m+16]` (`rsG_bytes`, `rsG_LowM16`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

section Specs

open Lean.Order

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

local macro "mem_rule" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AvxWidth.bytes, Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'))

local macro "reg_proof" : term =>
  `(fallthrough_spec (fun _ _ _ hP => by
      wp_step
      exact hP))

local macro "store_rule" : tactic =>
  `(tactic| (
    refine Triple.intro fun s h => ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    wp_step
    simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AvxWidth.bytes, Width.bytes, hv, Effects.All]
    exact hk _ hpl'))

/-- `vmovdqu %xmm, m128`: 16 present bytes, at any alignment. -/
@[spec low] theorem MachineWP.rsG_vmovdqu_store_mem_spec (x : AvxReg .W128) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128
        (.vmovdqu (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ := by store_rule

/-- `vpunpcklqdq %src2, %src1, %dst` (register form). -/
@[spec low] theorem MachineWP.rsG_vpunpcklqdq_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w)
    (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        (BitVec.packedBinOp 128 (fun x y => y.qw 0 ++ x.qw 0) (s.zmms.get src1)
          (s.zmms.get src2))) } ⦄
      (Directive.instr (.avx asz w (.vpunpcklqdq dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

end Specs

namespace Kraken.Examples.Sbr.Reset

set_option maxRecDepth 100000

open BitVec in
/-- `vpshufb .LCPI5_6`: the low quadword is every other `uint16_t`. -/
theorem rsG_shuf (a : BitVec 128) :
    (BitVec.pshufb128 a C56).qw 0
      = a.extractLsb' 96 16 ++ a.extractLsb' 64 16 ++ a.extractLsb' 32 16
        ++ a.extractLsb' 0 16 := by
  simp only [BitVec.pshufb128, BitVec.qw, C56]
  iterate 16 (rw [BitVec.packedBinOp,
    dite_eq_right_of_eq_false (eq_false (by decide))]; simp only [Nat.reduceSub])
  rw [BitVec.packedBinOp, dite_eq_left_of_eq_true (eq_true (by decide))]
  dsimp only [BitVec.take, BitVec.drop]
  have hA : ∀ {m n} (x : BitVec m) (y : BitVec n), BitVec.append x y = x ++ y :=
    fun _ _ => rfl
  simp only [hA]
  simp only [Nat.reduceSub, reduceExtractLsb', msb_zero, Bool.false_eq_true,
    ↓reduceIte, toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.mul_zero, Nat.reduceMod,
    Nat.reduceMul, msb_one, Nat.reduceEqDiff, decide_false, Nat.one_mod, Nat.mul_one,
    show (4#8).msb = false from rfl, show (5#8).msb = false from rfl,
    show (8#8).msb = false from rfl, show (9#8).msb = false from rfl,
    show (12#8).msb = false from rfl, show (13#8).msb = false from rfl,
    show (14#8).msb = false from rfl, show (15#8).msb = false from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi,
    Nat.zero_add, decide_true, Bool.true_and]
  have hc : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40)
      ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) := by omega
  rcases hc with h | h | h | h | h | h | h | h <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
    all_goals (congr 1; try omega)

/-- The low quadword picked by `.LCPI5_6`, as a number. -/
theorem rsG_lo (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    let a := BitVec.ofInt 128 (Int.ofBytes [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
      b12, b13, b14, b15])
    (a.extractLsb' 96 16 ++ a.extractLsb' 64 16 ++ a.extractLsb' 32 16
        ++ a.extractLsb' 0 16).toNat
      = q16 b0 b1 + 2 ^ 16 * q16 b4 b5 + 2 ^ 32 * q16 b8 b9 + 2 ^ 48 * q16 b12 b13 := by
  intro a
  have h128 : q16 b0 b1 + 2 ^ 16 * (q16 b2 b3 + 2 ^ 16 * (q16 b4 b5 + 2 ^ 16 * (q16 b6 b7
      + 2 ^ 16 * (q16 b8 b9 + 2 ^ 16 * (q16 b10 b11 + 2 ^ 16 * (q16 b12 b13
      + 2 ^ 16 * ((q16 b14 b15))))))))
      < 2 ^ 128 := by
    have := q16_lt b0 b1; have := q16_lt b2 b3; have := q16_lt b4 b5; have := q16_lt b6 b7
    have := q16_lt b8 b9; have := q16_lt b10 b11; have := q16_lt b12 b13
    have := q16_lt b14 b15; omega
  simp only [rsF_app, BitVec.extractLsb'_toNat, a, BitVec.toNat_ofInt,
    rsF_ofBytes16, Nat.shiftRight_eq_div_pow]
  rw [← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt h128,
    rsF_V _ _ _ _ _ _ _ _ (q16_lt _ _) (q16_lt _ _) (q16_lt _ _) (q16_lt _ _) (q16_lt _ _)
      (q16_lt _ _) (q16_lt _ _) rfl]

theorem rsG_ofBytes16 (b0 b1 b4 b5 b8 b9 b12 b13 c0 c1 c4 c5 c8 c9 c12 c13 : UInt8) :
    Int.ofBytes [b0, b1, b4, b5, b8, b9, b12, b13, c0, c1, c4, c5, c8, c9, c12, c13]
      = (((q16 b0 b1 + 2 ^ 16 * q16 b4 b5 + 2 ^ 32 * q16 b8 b9 + 2 ^ 48 * q16 b12 b13)
        + 2 ^ 64 * (q16 c0 c1 + 2 ^ 16 * q16 c4 c5 + 2 ^ 32 * q16 c8 c9
          + 2 ^ 48 * q16 c12 c13) : Nat) : Int) := by
  simp only [Int.ofBytes, List.foldr, q16]
  omega

theorem rsG_tb16 (X : BitVec 128) (bs : List UInt8) (hl : bs.length = 16)
    (h : (X.toNat : Int) = Int.ofBytes bs) : Int.toBytes 16 X.toInt = bs := by
  rw [← Int.toBytes_emod]
  have e : X.toInt.take (8 * 16) = Int.ofBytes bs := by
    rw [BitVec.toInt_eq_toNat_bmod, ← h]
    have := X.isLt
    simp only [Int.take, Nat.reduceMul, Int.bmod_def]
    split <;> omega
  rw [e, Int.toBytes_ofBytes _ _ (by omega), List.take_of_length_le (by omega)]

/-- Two `.LCPI5_6`-shuffled loads, interleaved by `vpunpcklqdq`, as 16 bytes. -/
theorem rsG_bytes (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : UInt8) :
    Int.toBytes 16 (BitVec.packedBinOp 128 (fun x y => y.qw 0 ++ x.qw 0)
      (BitVec.packedBinOp 128 BitVec.pshufb128 (BitVec.ofInt 128 (Int.ofBytes
        [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])) C56)
      (BitVec.packedBinOp 128 BitVec.pshufb128 (BitVec.ofInt 128 (Int.ofBytes
        [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15])) C56)).toInt
      = [b0, b1, b4, b5, b8, b9, b12, b13] ++ [c0, c1, c4, c5, c8, c9, c12, c13] := by
  rw [rsF_pk, rsF_pk, rsF_pk, rsG_shuf, rsG_shuf]
  apply rsG_tb16 _ _ rfl
  rw [rsF_app, rsG_lo, rsG_lo, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.nil_append, rsG_ofBytes16]
  omega


/-- The four `uint16_t`s picked from 16 bytes at entry `2(c+1)-q` of `H`. -/
theorem rsG_hhi (H : List UInt8) (f : Nat → Nat) (xo q c : Nat)
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8}
    (hq : q < 2)
    (hbs : slice H (2 * (2 * (c + 1) - q)) 16
      = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])
    (hH : ∀ i, i ≤ 2 * (c + 4) - q → u16 H i = f (xo + i) % 65536) :
    ∀ t, t < 4 → u16 [b0, b1, b4, b5, b8, b9, b12, b13] t
      = f (xo + (2 * (c + 1 + t) - q)) % 65536 := by
  intro t ht
  have e1 : u16 [b0, b1, b4, b5, b8, b9, b12, b13] t
      = u16 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] (2 * t) := by
    rcases t with _ | _ | _ | _ | t
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  have e2 : u16 (slice H (2 * (2 * (c + 1) - q)) 16) (2 * t)
      = u16 H (2 * (c + 1 + t) - q) := by
    unfold u16
    rw [u8_slice (by omega), u8_slice (by omega),
      show 2 * (2 * (c + 1) - q) + 2 * (2 * t) = 2 * (2 * (c + 1 + t) - q) by omega,
      show 2 * (2 * (c + 1) - q) + (2 * (2 * t) + 1) = 2 * (2 * (c + 1 + t) - q) + 1 by omega]
  rw [e1, ← hbs, e2, hH _ (by omega)]

/-- Entries `m + 1 .. m + 16` stored by two 16-byte stores. -/
theorem rsG_LowM16 (x : Args) (xo : Nat) (f : Nat → Nat) {m : Nat} (hm : m + 16 < 25)
    (B0 B1 B2 B3 : List UInt8) (h0 : B0.length = 8) (h1 : B1.length = 8) (h2 : B2.length = 8)
    (h3 : B3.length = 8)
    (hv0 : ∀ t, t < 4 → u16 B0 t = f (xo + (2 * (m + 1 + t) - x.n1 % 2)) % 65536)
    (hv1 : ∀ t, t < 4 → u16 B1 t = f (xo + (2 * (m + 4 + 1 + t) - x.n1 % 2)) % 65536)
    (hv2 : ∀ t, t < 4 → u16 B2 t = f (xo + (2 * (m + 8 + 1 + t) - x.n1 % 2)) % 65536)
    (hv3 : ∀ t, t < 4 → u16 B3 t = f (xo + (2 * (m + 12 + 1 + t) - x.n1 % 2)) % 65536) :
    wr (wr (LowM x xo f m) (2 * (m + 1)) (B0 ++ B1)) (2 * (m + 9)) (B2 ++ B3)
      = LowM x xo f (m + 16) := by
  have hl : ∀ c, (LowM x xo f c).length = 50 := fun _ => by simp [LowM]
  rw [a1_wr_append (A := B0) (B := B1)
      (by rw [hl, h0, h1]; omega), rsF_LowM_step4 _ _ _ (by omega) _ h0 hv0, h0,
    show 2 * (m + 1) + 8 = 2 * (m + 4 + 1) by omega,
    rsF_LowM_step4 _ _ _ (by omega) _ h1 hv1,
    a1_wr_append (A := B2) (B := B3)
        (by rw [hl, h2, h3]; omega), show 2 * (m + 9) = 2 * (m + 8 + 1) by omega,
    rsF_LowM_step4 _ _ _ (by omega) _ h2 hv2, h2,
    show 2 * (m + 8 + 1) + 8 = 2 * (m + 12 + 1) by omega,
    rsF_LowM_step4 _ _ _ (by omega) _ h3 hv3]

theorem rsG_ldaddr (x D : BitVec 64) (m q c i : Nat) (hq : q < 2) (hm : m < 2 ^ 32)
    (hc : c = m + 4 * i) (hi : i < 4) (hD : D = BitVec.ofNat 64 (2 ^ 64 - 48 + 16 * i)) :
    x + BitVec.ofNat 64 (0x4c2b8 - 2 * q) + BitVec.ofNat 64 m * 4#64 + D
      = x + 0x4c284#64 + BitVec.ofNat 64 (2 * (2 * (c + 1) - q)) := by
  subst hD hc
  have e : BitVec.ofNat 64 (0x4c2b8 - 2 * q) + BitVec.ofNat 64 m * 4#64
      + BitVec.ofNat 64 (2 ^ 64 - 48 + 16 * i)
      = 0x4c284#64 + BitVec.ofNat 64 (2 * (2 * (m + 4 * i + 1) - q)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc (BitVec.ofNat 64 _), e,
    ← BitVec.add_assoc]

theorem rsG_staddr (x : BitVec 64) (m d j : Nat) (hd : d = 0x4c252 + 2 * j) :
    x + BitVec.ofNat 64 m * 2#64 + BitVec.ofNat 64 d
      = x + 0x4c252#64 + BitVec.ofNat 64 (2 * (m + j)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

variable [CodeEnv]

/-- The 16-wide copy loop body: `f_tablelow[m+1 .. m+16] = f_tablehigh[2(m+1)-p, +2, ..]`. -/
theorem blk_L2a30 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2a30" ⟨"sbr_reset.L2a30", B.L2a30, some "sbr_reset.L2a77"⟩ := by
  info_off
  measure_hb "L2a30"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, h17, h13, h8, hsi, h9, hdx, hax,
        hm16, hlt, hdi, hx0⟩, hm⟩ := T.L2a30.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have hlt' : m < (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) := hlt
    have hR : ((nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2)) % 16 = 0
        ∧ (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) < (nm - xoOf a + 1) / 2 := by
      simp only [R16]; split <;> omega
    have h16 : m + 16 ≤ (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) := by omega
    have hq : (dD1 a k0 nm (fOf st)).n1 = nm - xoOf a := rfl
    have hp : (dD1 a k0 nm (fOf st)).n1 % 2 < 2 := Nat.mod_lt _ (by omega)
    have hfh : st.x.ftHigh.length = 98 := by rw [hx]; simp [derived1]
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; simp [LowM]
    have hfl0 : st.x.ftLow = LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) m := by rw [hx]
    have hH : ∀ i, i ≤ nm - xoOf a → u16 st.x.ftHigh i = fOf st (xoOf a + i) % 65536 := by
      intro i hi
      rw [hx]
      refine (u16_mk16 (f := fun i => if i ≤ nm - xoOf a then fOf st (xoOf a + i)
        else u16 (x0D a k0).ftHigh i) (by omega)).trans ?_
      rw [ite_eq_left (by omega)]
    obtain ⟨b0_0, b0_1, b0_2, b0_3, b0_4, b0_5, b0_6, b0_7, b0_8, b0_9, b0_10, b0_11,
        b0_12, b0_13, b0_14, b0_15, hbs0⟩ :=
      rsF_l16 _ (slice_length (l := st.x.ftHigh)
        (o := 2 * (2 * (m + 1) - (dD1 a k0 nm (fOf st)).n1 % 2)) (n := 16) (by omega))
    have hld0 : s₀.dmem.loadInt (s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 4#64 +
        (-48 : Int64).toBitVec) 16
        = some (Int.ofBytes [b0_0, b0_1, b0_2, b0_3, b0_4, b0_5, b0_6, b0_7, b0_8, b0_9, b0_10,
          b0_11, b0_12, b0_13, b0_14, b0_15]) := by
      rw [← hbs0]
      exact region_load (focus (Mm_ftHigh ..) hm)
        (by rw [hsi, hdi]; exact rsG_ldaddr _ _ _ _ _ 0 hp (by omega) (by omega)
              (by omega) rfl)
        (by omega) (by omega)
    have hhi0 := rsG_hhi st.x.ftHigh (fOf st) (xoOf a) _ (m) hp hbs0
      (fun i hi => hH i (by omega))
    obtain ⟨b1_0, b1_1, b1_2, b1_3, b1_4, b1_5, b1_6, b1_7, b1_8, b1_9, b1_10, b1_11,
        b1_12, b1_13, b1_14, b1_15, hbs1⟩ :=
      rsF_l16 _ (slice_length (l := st.x.ftHigh)
        (o := 2 * (2 * (m + 4 + 1) - (dD1 a k0 nm (fOf st)).n1 % 2)) (n := 16) (by omega))
    have hld1 : s₀.dmem.loadInt (s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 4#64 +
        (-32 : Int64).toBitVec) 16
        = some (Int.ofBytes [b1_0, b1_1, b1_2, b1_3, b1_4, b1_5, b1_6, b1_7, b1_8, b1_9, b1_10,
          b1_11, b1_12, b1_13, b1_14, b1_15]) := by
      rw [← hbs1]
      exact region_load (focus (Mm_ftHigh ..) hm)
        (by rw [hsi, hdi]; exact rsG_ldaddr _ _ _ _ _ 1 hp (by omega) (by omega)
              (by omega) rfl)
        (by omega) (by omega)
    have hhi1 := rsG_hhi st.x.ftHigh (fOf st) (xoOf a) _ (m + 4) hp hbs1
      (fun i hi => hH i (by omega))
    obtain ⟨b2_0, b2_1, b2_2, b2_3, b2_4, b2_5, b2_6, b2_7, b2_8, b2_9, b2_10, b2_11,
        b2_12, b2_13, b2_14, b2_15, hbs2⟩ :=
      rsF_l16 _ (slice_length (l := st.x.ftHigh)
        (o := 2 * (2 * (m + 8 + 1) - (dD1 a k0 nm (fOf st)).n1 % 2)) (n := 16) (by omega))
    have hld2 : s₀.dmem.loadInt (s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 4#64 +
        (-16 : Int64).toBitVec) 16
        = some (Int.ofBytes [b2_0, b2_1, b2_2, b2_3, b2_4, b2_5, b2_6, b2_7, b2_8, b2_9, b2_10,
          b2_11, b2_12, b2_13, b2_14, b2_15]) := by
      rw [← hbs2]
      exact region_load (focus (Mm_ftHigh ..) hm)
        (by rw [hsi, hdi]; exact rsG_ldaddr _ _ _ _ _ 2 hp (by omega) (by omega)
              (by omega) rfl)
        (by omega) (by omega)
    have hhi2 := rsG_hhi st.x.ftHigh (fOf st) (xoOf a) _ (m + 8) hp hbs2
      (fun i hi => hH i (by omega))
    obtain ⟨b3_0, b3_1, b3_2, b3_3, b3_4, b3_5, b3_6, b3_7, b3_8, b3_9, b3_10, b3_11,
        b3_12, b3_13, b3_14, b3_15, hbs3⟩ :=
      rsF_l16 _ (slice_length (l := st.x.ftHigh)
        (o := 2 * (2 * (m + 12 + 1) - (dD1 a k0 nm (fOf st)).n1 % 2)) (n := 16) (by omega))
    have hld3 : s₀.dmem.loadInt (s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 4#64 + 0#64) 16
        = some (Int.ofBytes [b3_0, b3_1, b3_2, b3_3, b3_4, b3_5, b3_6, b3_7, b3_8, b3_9, b3_10,
          b3_11, b3_12, b3_13, b3_14, b3_15]) := by
      rw [← hbs3]
      exact region_load (focus (Mm_ftHigh ..) hm)
        (by rw [hsi, hdi]; exact rsG_ldaddr _ _ _ _ _ 3 hp (by omega) (by omega)
              (by omega) rfl)
        (by omega) (by omega)
    have hhi3 := rsG_hhi st.x.ftHigh (fOf st) (xoOf a) _ (m + 12) hp hbs3
      (fun i hi => hH i (by omega))
    have hM1 := region_store (o := 2 * (m + 1)) (n := 16) (addr := (s₀.regs.get64 .r8
        + s₀.regs.get64 .rdi * 2#64 + 311892#64))
      (focus (Mm_ftLow ..) hm) (by rw [h8, hdi]; exact rsG_staddr _ _ _ _ rfl)
      (by rw [hfl]; omega) (by rw [hfl]; omega)
    have hlds1 : (s₀.dmem.loadInt (s₀.regs.get64 .r8 + s₀.regs.get64 .rdi * 2#64
        + 311892#64) 16).isSome = true := by
      rw [region_load (o := 2 * (m + 1)) (n := 16) (addr := (s₀.regs.get64 .r8
          + s₀.regs.get64 .rdi * 2#64 + 311892#64))
        (focus (Mm_ftLow ..) hm) (by rw [h8, hdi]; exact rsG_staddr _ _ _ _ rfl)
        (by rw [hfl]; omega) (by rw [hfl]; omega)]; rfl
    have hwl : ∀ w : Int, (wr st.x.ftLow (2 * (m + 1)) (Int.toBytes 16 w)).length = 50 := by
      intro w; rw [wr_length (by rw [Int.toBytes_length, hfl]; omega), hfl]
    have hlds2 : ∀ w : Int,
        ((s₀.dmem.storeInt (s₀.regs.get64 .r8 + s₀.regs.get64 .rdi * 2#64
            + 311892#64) 16 w).loadInt (s₀.regs.get64 .r8 + s₀.regs.get64 .rdi * 2#64
                + 311908#64) 16).isSome = true := by
      intro w
      rw [region_load (o := 2 * (m + 9)) (n := 16) (addr := (s₀.regs.get64 .r8
          + s₀.regs.get64 .rdi * 2#64 + 311908#64))
        (hM1 w) (by rw [h8, hdi]; exact rsG_staddr _ _ _ _ rfl)
        (by rw [hwl]; omega) (by rw [hwl]; omega)]; rfl
    have hstore : ∀ w1 w2 : Int, Int.toBytes 16 w1 = [b0_0, b0_1, b0_4, b0_5, b0_8, b0_9, b0_12,
        b0_13] ++ [b1_0, b1_1, b1_4, b1_5, b1_8, b1_9, b1_12, b1_13] →
        Int.toBytes 16 w2 = [b2_0, b2_1, b2_4, b2_5, b2_8, b2_9, b2_12, b2_13] ++ [b3_0, b3_1,
            b3_4, b3_5, b3_8, b3_9, b3_12, b3_13] →
        (s₀.dmem.storeInt (s₀.regs.get64 .r8 + s₀.regs.get64 .rdi * 2#64
            + 311892#64) 16 w1).storeInt (s₀.regs.get64 .r8 + s₀.regs.get64 .rdi * 2#64
                + 311908#64) 16 w2
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st))
            (xoOf a) (fOf st) (m + 16)) } } : St) fr := by
      intro w1 w2 hw1 hw2
      have h := region_store (o := 2 * (m + 9)) (n := 16) (addr := (s₀.regs.get64 .r8
          + s₀.regs.get64 .rdi * 2#64 + 311908#64))
        (hM1 w1) (by rw [h8, hdi]; exact rsG_staddr _ _ _ _ rfl)
        (by rw [hwl]; omega) (by rw [hwl]; omega) w2
      rw [hw1, hw2, hfl0, rsG_LowM16 _ _ _ (by omega) _ _ _ _ rfl rfl rfl rfl hhi0 hhi1 hhi2 hhi3,
        Mm_upd_ftLow] at h
      exact h
    have hval : ∀ X : BitVec 128, X = C56 → ∀ (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14
        c15 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : UInt8),
        Int.toBytes 16 (BitVec.packedBinOp 128 (fun x y => y.qw 0 ++ x.qw 0)
          (BitVec.packedBinOp 128 BitVec.pshufb128 (BitVec.ofInt 128 (Int.ofBytes
            [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15])) X)
          (BitVec.packedBinOp 128 BitVec.pshufb128 (BitVec.ofInt 128 (Int.ofBytes
            [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15])) X)).toInt
        = [c0, c1, c4, c5, c8, c9, c12, c13] ++ [d0, d1, d4, d5, d8, d9, d12, d13] := by
      intro X hX; subst hX; exact rsG_bytes
    have hx' : ({ st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st))
            (xoOf a) (fOf st) (m + 16)) } } : St).x = dLw a k0 nm (fOf st) (m + 16) := by
      show ({ st.x with ftLow := _ } : Args) = _
      rw [hx]
    have hx0' : s₀.zmms.get (.xmm .mm0) = C56 := by
      have h := hx0; simp only [BitVec.setWidth_eq] at h; exact h
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := PLift.up hx'
    have Pld0 := PLift.up hld0
    have Pld1 := PLift.up hld1
    have Pld2 := PLift.up hld2
    have Pld3 := PLift.up hld3
    have Pst := PLift.up hstore
    have Pval := PLift.up hval
    have Plds2 := PLift.up hlds2
    clear h30 hx hx' hm hld0 hld1 hld2 hld3 hstore hhi0 hhi1 hhi2 hhi3 hfl0 hval hbs0 hbs1 hbs2
      hbs3 hM1 hlds2 hH hwl
    have hW4 : BitVec.ofNat 64 Width.W32.bytes = 4#64 := rfl
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2a30]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hW4, hW2, RegZmms.get_set_xmm_same] at *
    case vc1 => rw [Pld0.down]; rfl
    case vc2 => rw [Pld1.down]; rfl
    case vc3 => rw [Pld2.down]; rfl
    case vc4 => rw [Pld3.down]; rfl
    case vc5 => exact hlds1
    case vc6 => exact Plds2.down _
    case vc7 =>
      rename_i v0 v1 v2 v3 hl0 hl1 hl2 hl3
      have hl0 := hl0.symm.trans Pld0.down
      have hl1 := hl1.symm.trans Pld1.down
      have hl2 := hl2.symm.trans Pld2.down
      have hl3 := hl3.symm.trans Pld3.down
      simp only [Option.some.injEq] at hl0 hl1 hl2 hl3
      subst hl0 hl1 hl2 hl3
      simp (disch := decide) only [RegZmms.get_set_xmm_ne, RegZmms.get_set_xmm_same]
      refine ⟨T.L2a77.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩,
        ({ st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st))
          (xoOf a) (fOf st) (m + 16)) } } : St), fr, nm, k0, hMa, hsp, hfm, hF, h40,
        ⟨hk2, hf64, hbr, P30.down, h38, m + 16, Px.down, by rsE_rs; exact h14,
          by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx, h17,
          by rsE_rs; exact h13, by rsE_rs; exact h8, by rsE_rs; exact hsi, by rsE_rs; exact h9,
          by rsE_rs; exact hdx, by rsE_rs; exact hax, by omega, by omega, h16,
          by rsE_rs; rw [hdi, Nat.add_sub_cancel],
          by simp (disch := decide) only [RegZmms.get_set_xmm_ne]; exact hx0⟩,
        Pst.down _ _ (Pval.down _ hx0' ..) (Pval.down _ hx0' ..)⟩, by var_step⟩

end Kraken.Examples.Sbr.Reset
