import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetELib
import Kraken.X64.Examples.Sbr.Parse.ResetE3
import Kraken.X64.Examples.Sbr.Parse.ResetA1Mem

/-!
# `sbr_reset`: `sbr_make_f_derived`, the 4-wide `f_tablelow` copy (`L2ad6`, shard B, env)

`vmovdqu` loads 16 bytes of `f_tablehigh` (entries `2(m+1)-p ..`), `vpshufb .LCPI5_9` keeps every
other `uint16_t` (`rsF_shuf`), `vmovq` stores the four into `f_tablelow[m+1 .. m+4]`
(`rsF_bytes`, `rsF_LowM_step4`).
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

/-- `vmovdqu m128, %xmm`: 16 readable bytes, at any alignment. -/
@[spec low] theorem MachineWP.rsF_vmovdqu_load_mem_spec (x : AvxReg .W128) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 16 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set x (BitVec.ofInt 128 v) }) ⦄
      (Directive.instr (.avx .W64 .W128
        (.vmovdqu (.avx x) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by mem_rule

/-- `vpshufb %src2, %src1, %dst` (register form). -/
@[spec low] theorem MachineWP.rsF_vpshufb_reg_spec {w : AvxWidth} (dst src1 src2 : AvxReg w)
    (asz : Width) :
    ⦃ fun s => WP.wp p Q E { s with zmms := (s.zmms.set dst
        (BitVec.packedBinOp 128 BitVec.pshufb128 (s.zmms.get src1) (s.zmms.get src2))) } ⦄
      (Directive.instr (.avx asz w (.vpshufb dst src1 (.avx src2))) :: p)
    ⦃ Q; E ⦄ := reg_proof

end Specs

namespace Kraken.Examples.Sbr.Reset

set_option maxRecDepth 100000

open BitVec in
/-- `vpshufb .LCPI5_9`: the low quadword is every other `uint16_t`. -/
theorem rsF_shuf (a : BitVec 128) :
    (BitVec.pshufb128 a 0x0d0c090805040100#128).setWidth 64
      = a.extractLsb' 96 16 ++ a.extractLsb' 64 16 ++ a.extractLsb' 32 16
        ++ a.extractLsb' 0 16 := by
  simp only [BitVec.pshufb128]
  iterate 16 (rw [BitVec.packedBinOp,
    dite_eq_right_of_eq_false (eq_false (by decide))]; simp only [Nat.reduceSub])
  rw [BitVec.packedBinOp, dite_eq_left_of_eq_true (eq_true (by decide))]
  dsimp only [BitVec.take, BitVec.drop]
  have hA : ∀ {m n} (x : BitVec m) (y : BitVec n), BitVec.append x y = x ++ y :=
    fun _ _ => rfl
  simp only [hA]
  simp only [Nat.reduceSub, reduceExtractLsb', extractLsb'_zero, msb_zero, Bool.false_eq_true,
    ↓reduceIte, toNat_ofNat, Nat.reducePow, Nat.zero_mod, Nat.mul_zero, Nat.reduceMod,
    Nat.reduceMul, msb_one, Nat.reduceEqDiff, decide_false, Nat.one_mod, Nat.mul_one,
    show (4#8).msb = false from rfl, show (5#8).msb = false from rfl,
    show (8#8).msb = false from rfl, show (9#8).msb = false from rfl,
    show (12#8).msb = false from rfl, show (13#8).msb = false from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', hi,
    decide_true, Bool.true_and]
  have hc : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40)
      ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) := by omega
  rcases hc with h | h | h | h | h | h | h | h <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, decide_eq_true, Bool.true_and]
    all_goals (congr 1; try omega)

theorem rsF_pk (f : BitVec 128 → BitVec 128 → BitVec 128) (x y : BitVec 128) :
    BitVec.packedBinOp 128 f x y = f x y := by
  rw [BitVec.packedBinOp, dite_eq_right_of_eq_false (eq_false (by decide))]
  have hA : ∀ {m n} (x : BitVec m) (y : BitVec n), BitVec.append x y = x ++ y :=
    fun _ _ => rfl
  simp only [hA]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and,
    ↓reduceIte, BitVec.take, BitVec.extractLsb'_eq_self]

theorem rsF_pick {V : Nat} (lo x hi k : Nat) (hV : V = lo + 2 ^ k * (x + 2 ^ 16 * hi))
    (hlo : lo < 2 ^ k) (hx : x < 2 ^ 16) : V / 2 ^ k % 2 ^ 16 = x := by
  subst hV
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hlo, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

theorem rsF_app {m n : Nat} (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- A little-endian `uint16_t` from two bytes. -/
def q16 (x y : UInt8) : Nat := x.toNat + 256 * y.toNat

theorem q16_lt (x y : UInt8) : q16 x y < 2 ^ 16 := by
  have := x.toNat_lt; have := y.toNat_lt; unfold q16; omega

theorem rsF_ofBytes16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    Int.ofBytes [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15]
      = ((q16 b0 b1 + 2 ^ 16 * (q16 b2 b3 + 2 ^ 16 * (q16 b4 b5 + 2 ^ 16 * (q16 b6 b7
          + 2 ^ 16 * (q16 b8 b9 + 2 ^ 16 * (q16 b10 b11 + 2 ^ 16 * (q16 b12 b13
          + 2 ^ 16 * ((q16 b14 b15)))))))) : Nat) : Int) := by
  simp only [Int.ofBytes, List.foldr, q16]
  omega

theorem rsF_ofBytes8 (b0 b1 b4 b5 b8 b9 b12 b13 : UInt8) :
    Int.ofBytes [b0, b1, b4, b5, b8, b9, b12, b13]
      = ((q16 b0 b1 + 2 ^ 16 * q16 b4 b5 + 2 ^ 32 * q16 b8 b9 + 2 ^ 48 * q16 b12 b13 : Nat)
        : Int) := by
  simp only [Int.ofBytes, List.foldr, q16]
  omega

theorem rsF_V (q0 q1 q2 q3 q4 q5 q6 q7 : Nat) (h0 : q0 < 2 ^ 16) (h1 : q1 < 2 ^ 16)
    (h2 : q2 < 2 ^ 16) (h3 : q3 < 2 ^ 16) (h4 : q4 < 2 ^ 16) (h5 : q5 < 2 ^ 16)
    (h6 : q6 < 2 ^ 16) {V : Nat}
    (hV : V = q0 + 2 ^ 16 * (q1 + 2 ^ 16 * (q2 + 2 ^ 16 * (q3 + 2 ^ 16 * (q4 + 2 ^ 16 * (q5
        + 2 ^ 16 * (q6 + 2 ^ 16 * q7))))))) :
    ((V / 2 ^ 96 % 2 ^ 16 * 2 ^ 16 + V / 2 ^ 64 % 2 ^ 16) * 2 ^ 16 + V / 2 ^ 32 % 2 ^ 16)
      * 2 ^ 16 + V / 2 ^ 0 % 2 ^ 16 = q0 + 2 ^ 16 * q2 + 2 ^ 32 * q4 + 2 ^ 48 * q6 := by
  have p0 : V / 2 ^ 0 % 2 ^ 16 = q0 := by
    rw [Nat.pow_zero, Nat.div_one, hV, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  have p1 : V / 2 ^ 32 % 2 ^ 16 = q2 :=
    rsF_pick (q0 + 2 ^ 16 * q1) q2 (q3 + 2 ^ 16 * (q4 + 2 ^ 16 * (q5 + 2 ^ 16 * (q6
      + 2 ^ 16 * q7)))) 32 (by rw [hV]; omega) (by omega) h2
  have p2 : V / 2 ^ 64 % 2 ^ 16 = q4 :=
    rsF_pick (q0 + 2 ^ 16 * q1 + 2 ^ 32 * q2 + 2 ^ 48 * q3) q4
      (q5 + 2 ^ 16 * (q6 + 2 ^ 16 * q7)) 64 (by rw [hV]; omega) (by omega) h4
  have p3 : V / 2 ^ 96 % 2 ^ 16 = q6 :=
    rsF_pick (q0 + 2 ^ 16 * q1 + 2 ^ 32 * q2 + 2 ^ 48 * q3 + 2 ^ 64 * q4 + 2 ^ 80 * q5)
      q6 q7 96 (by rw [hV]; omega) (by omega) h6
  rw [p0, p1, p2, p3]
  omega

/-- The four `uint16_t`s picked by `.LCPI5_9` from 16 bytes, as 8 bytes. -/
theorem rsF_bytes (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    let a := BitVec.ofInt 128 (Int.ofBytes [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11,
      b12, b13, b14, b15])
    Int.toBytes 8 (a.extractLsb' 96 16 ++ a.extractLsb' 64 16 ++ a.extractLsb' 32 16
        ++ a.extractLsb' 0 16).toInt = [b0, b1, b4, b5, b8, b9, b12, b13] := by
  intro a
  rw [← Int.toBytes_emod]
  have h : (a.extractLsb' 96 16 ++ a.extractLsb' 64 16 ++ a.extractLsb' 32 16
        ++ a.extractLsb' 0 16).toInt.take (8 * 8)
      = Int.ofBytes [b0, b1, b4, b5, b8, b9, b12, b13] := by
    have h128 : q16 b0 b1 + 2 ^ 16 * (q16 b2 b3 + 2 ^ 16 * (q16 b4 b5 + 2 ^ 16 * (q16 b6 b7
        + 2 ^ 16 * (q16 b8 b9 + 2 ^ 16 * (q16 b10 b11 + 2 ^ 16 * (q16 b12 b13
        + 2 ^ 16 * ((q16 b14 b15))))))))
        < 2 ^ 128 := by
      have := q16_lt b0 b1; have := q16_lt b2 b3; have := q16_lt b4 b5; have := q16_lt b6 b7
      have := q16_lt b8 b9; have := q16_lt b10 b11; have := q16_lt b12 b13
      have := q16_lt b14 b15; omega
    rw [BitVec.toInt_eq_toNat_bmod]
    simp only [Int.take, rsF_app, BitVec.extractLsb'_toNat, a, BitVec.toNat_ofInt,
      rsF_ofBytes16, Nat.shiftRight_eq_div_pow]
    rw [← Int.natCast_emod, Int.toNat_natCast, Nat.mod_eq_of_lt h128,
      rsF_V _ _ _ _ _ _ _ _ (q16_lt _ _) (q16_lt _ _) (q16_lt _ _) (q16_lt _ _) (q16_lt _ _)
        (q16_lt _ _) (q16_lt _ _) rfl, rsF_ofBytes8]
    have := q16_lt b0 b1; have := q16_lt b4 b5; have := q16_lt b8 b9; have := q16_lt b12 b13
    simp only [Nat.reduceAdd, Nat.reduceMul, Int.bmod_def]
    split <;> omega
  rw [h, Int.toBytes_ofBytes _ _ (by simp)]
  rfl

/-- An 8-byte store at entry `j` of a `uint16_t` array. -/
theorem rsF_u16_wr8 {l bs : List UInt8} {j : Nat} (hb : bs.length = 8) (h : 2 * j + 8 ≤ l.length)
    (i : Nat) :
    u16 (wr l (2 * j) bs) i = if j ≤ i ∧ i < j + 4 then u16 bs (i - j) else u16 l i := by
  split
  · rename_i hi
    unfold u16
    rw [u8_wr_in (by omega) (by omega) (by omega), u8_wr_in (by omega) (by omega) (by omega),
      show 2 * i - 2 * j = 2 * (i - j) by omega, show 2 * i + 1 - 2 * j = 2 * (i - j) + 1 by omega]
  · rename_i hi
    unfold u16
    rw [u8_wr_out (by omega) (by omega), u8_wr_out (by omega) (by omega)]

/-- Entries `m + 1 .. m + 4` stored: `m + 4` entries copied. -/
theorem rsF_LowM_step4 (x : Args) (xo : Nat) (f : Nat → Nat) {m : Nat} (hm : m + 4 < 25)
    (bs : List UInt8) (hb : bs.length = 8)
    (hv : ∀ t, t < 4 → u16 bs t = f (xo + (2 * (m + 1 + t) - x.n1 % 2)) % 65536) :
    wr (LowM x xo f m) (2 * (m + 1)) bs = LowM x xo f (m + 4) := by
  have hl : (LowM x xo f m).length = 50 := by simp [LowM]
  apply eq_of_u16 (k := 25) (by rw [wr_length (by rw [hb]; omega), hl]) (by simp [LowM])
  intro i hi
  rw [rsF_u16_wr8 hb (by omega)]
  conv => rhs; rw [LowM, u16_mk16 hi]
  split
  · rename_i h1
    rw [hv _ (by omega)]
    simp only [show ¬ i = 0 by omega, show i ≤ m + 4 by omega, ↓reduceIte]
    rw [show m + 1 + (i - (m + 1)) = i by omega]
  · rename_i h1
    rw [LowM, u16_mk16 hi]
    by_cases h0 : i = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      by_cases h2 : i ≤ m
      · simp [h2, show i ≤ m + 4 by omega]
      · simp [h2, show ¬ i ≤ m + 4 by omega]


theorem rsF_l16 (l : List UInt8) (h : l.length = 16) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15,
      l = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7,
    _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15,
    _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> (try simp at h)
    <;> exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem rsF_ldaddr (x : BitVec 64) (b j p : Nat) (hp : p < 2) (hb : b + j < 2 ^ 32) :
    x + BitVec.ofNat 64 (0x4c288 + 4 * b - 2 * p) + BitVec.ofNat 64 j * 4#64 + 0#64
      = x + 0x4c284#64 + BitVec.ofNat 64 (2 * (2 * (b + j + 1) - p)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem rsF_staddr (x : BitVec 64) (b j : Nat) (_hb : b + j < 2 ^ 32) :
    x + BitVec.ofNat 64 (0x4c254 + 2 * b) + BitVec.ofNat 64 j * 2#64 + 0#64
      = x + 0x4c252#64 + BitVec.ofNat 64 (2 * (b + j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

theorem rsF_inc4 (j : Nat) (_h : j < 2 ^ 32) :
    4#64 + BitVec.ofNat 64 j = BitVec.ofNat 64 (j + 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem rsF_ne (n b j : Nat) (h : b + j < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 (n - b) = 4#64 + BitVec.ofNat 64 j) ↔ b + j + 4 = n := by
  rw [rsF_inc4 j (by omega)]
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  · intro e; congr 1; omega

theorem rsF_var (n b j : Nat) (h : b + j + 4 < n) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 64 (n - b)).toNat - (BitVec.ofNat 64 (j + 4)).toNat) % 2 ^ 64
      < ((BitVec.ofNat 64 (n - b)).toNat - (BitVec.ofNat 64 j).toNat) % 2 ^ 64 := by
  simp only [BitVec.toNat_ofNat]; omega

variable [CodeEnv]

/-- The 4-wide copy loop: `f_tablelow[m+1 .. m+4] = f_tablehigh[2(m+1)-p, +2, +4, +6]`. -/
theorem blk_L2ad6 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2ad6" ⟨"sbr_reset.L2ad6", B.L2ad6, some "sbr_reset.L2aef"⟩ := by
  info_off
  measure_hb "L2ad6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, h13, b, j, rfl, hb4, hj4, hlt, hdi,
        hdx, hax, hsi, hr8, hx0⟩, hm⟩ := T.L2ad6.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hlt' : b + j < (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) := hlt
    have hR : ((nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2)) % 4 = 0
        ∧ (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) < (nm - xoOf a + 1) / 2 := by
      simp only [R4]; split <;> omega
    have h4 : b + j + 4 ≤ (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) := by omega
    have hp : (nm - xoOf a) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hfh : st.x.ftHigh.length = 98 := by rw [hx]; simp [derived1]
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; simp [LowM]
    have hfl0 : st.x.ftLow = LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st) (b + j) := by rw [hx]
    have hsl : (slice st.x.ftHigh (2 * (2 * (b + j + 1) - (nm - xoOf a) % 2)) 16).length = 16 :=
      slice_length (by omega)
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, hbs⟩ :=
      rsF_l16 _ hsl
    have hld : s₀.dmem.loadInt (s₀.regs.get64 .r8 + s₀.regs.get64 .rdi * 4#64 + 0#64) 16
        = some (Int.ofBytes [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
          b15]) := by
      rw [← hbs]
      exact region_load (focus (Mm_ftHigh ..) hm)
        (by rw [hr8, hdi]; exact rsF_ldaddr _ _ _ _ hp (by omega)) (by omega) (by omega)
    -- the 16 bytes are entries `2(m+1)-p ..` of `f_tablehigh`
    have hhi : ∀ t, t < 4 → u16 [b0, b1, b4, b5, b8, b9, b12, b13] t
        = fOf st (xoOf a + (2 * (b + j + 1 + t) - (dD1 a k0 nm (fOf st)).n1 % 2)) % 65536 := by
      intro t ht
      have e1 : u16 [b0, b1, b4, b5, b8, b9, b12, b13] t
          = u16 [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] (2 * t) := by
        rcases t with _ | _ | _ | _ | t
        · rfl
        · rfl
        · rfl
        · rfl
        · omega
      have e2 : u16 (slice st.x.ftHigh (2 * (2 * (b + j + 1) - (nm - xoOf a) % 2)) 16) (2 * t)
          = u16 st.x.ftHigh (2 * (b + j + 1 + t) - (nm - xoOf a) % 2) := by
        unfold u16
        rw [u8_slice (by omega), u8_slice (by omega),
          show 2 * (2 * (b + j + 1) - (nm - xoOf a) % 2) + 2 * (2 * t)
            = 2 * (2 * (b + j + 1 + t) - (nm - xoOf a) % 2) by omega,
          show 2 * (2 * (b + j + 1) - (nm - xoOf a) % 2) + (2 * (2 * t) + 1)
            = 2 * (2 * (b + j + 1 + t) - (nm - xoOf a) % 2) + 1 by omega]
      rw [e1, ← hbs, e2, hx]
      refine (u16_mk16 (f := fun i => if i ≤ nm - xoOf a then fOf st (xoOf a + i)
        else u16 (x0D a k0).ftHigh i) (by omega)).trans ?_
      rw [ite_eq_left (by omega)]; rfl
    have hstore : ∀ w : Int, Int.toBytes 8 w = [b0, b1, b4, b5, b8, b9, b12, b13] →
        s₀.dmem.storeInt (s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 2#64 + 0#64) 8 w
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st))
            (xoOf a) (fOf st) (b + j + 4)) } } : St) fr := by
      intro w hw
      have h := region_store (o := 2 * (b + j + 1)) (n := 8)
        (addr := s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 2#64 + 0#64) (focus (Mm_ftLow ..) hm)
        (by rw [hsi, hdi]; exact rsF_staddr _ _ _ (by omega)) (by rw [hfl]; omega)
        (by rw [hfl]; omega) w
      rw [hw, hfl0, rsF_LowM_step4 _ _ _ (by omega) _ rfl hhi, Mm_upd_ftLow] at h
      exact h
    have hlds : (s₀.dmem.loadInt (s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 2#64 + 0#64) 8).isSome
        = true := by
      rw [region_load (o := 2 * (b + j + 1)) (n := 8)
        (addr := s₀.regs.get64 .rsi + s₀.regs.get64 .rdi * 2#64 + 0#64) (focus (Mm_ftLow ..) hm)
        (by rw [hsi, hdi]; exact rsF_staddr _ _ _ (by omega)) (by rw [hfl]; omega)
        (by rw [hfl]; omega)]; rfl
    have hval : ∀ X : BitVec 128, X = C59 →
        Int.toBytes 8 ((BitVec.packedBinOp 128 BitVec.pshufb128 (BitVec.ofInt 128 (Int.ofBytes
          [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15])) X).setWidth
            64).toInt = [b0, b1, b4, b5, b8, b9, b12, b13] := by
      intro X hX
      rw [rsF_pk, hX, rsF_shuf]
      exact rsF_bytes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    have hx' : ({ st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st)
        (b + j + 4)) } } : St).x = dLw a k0 nm (fOf st) (b + j + 4) := by
      show ({ st.x with ftLow := _ } : Args) = _
      rw [hx]
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := PLift.up hx'
    have Pld := PLift.up hld
    have Pst := PLift.up hstore
    have Pval := PLift.up hval
    clear h30 hx hx' hm hld hstore hhi hfl0 hval hbs
    have hne := rsF_ne _ _ _ hlt' (by omega)
    have hstep : ¬ (b + j + 4 = (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2)) →
        b + j + 4 < (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) := by omega
    have hx0' : s₀.zmms.get (.xmm .mm0) = C59 := by
      have h := hx0; simp only [BitVec.setWidth_eq] at h; exact h
    have hW4 : BitVec.ofNat 64 Width.W32.bytes = 4#64 := rfl
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    have hfin : b + j + 4 = (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) →
        b + j + 4 < (nm - xoOf a + 1) / 2 := by omega
    simp only [B.L2ad6]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hW4, hW2, RegZmms.get_set_xmm_same,
      RegZmms.get_set_xmm_ne _ _ _ _ (by decide : RegMm.mm1 ≠ RegMm.mm0)] at *
    case vc1 => rw [Pld.down]; rfl
    case vc2 => exact hlds
    all_goals rename_i v hl hc
    all_goals have hl := hl.symm.trans Pld.down
    all_goals simp only [Option.some.injEq] at hl
    all_goals subst hl
    all_goals simp only [Kraken.Examples.Sbr.Reset.cc_nz_sub, hdx, hdi, hne, Bool.not_eq_true',
      Bool.not_eq_false', decide_eq_false_iff_not, decide_eq_true_eq] at hc
    case vc3 =>
      exact Or.inl (Table.ofLabels_at ⟨S.L2ad6, T.L2ad6.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, { st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st))
          (xoOf a) (fOf st) (b + j + 4)) } }, fr, nm, k0, hMa, hsp, hfm, hF, h40,
        ⟨hk2, hf64, hbr, P30.down, h38, b + j + 4, Px.down, by rsE_rs; exact h14,
          by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx, by rsE_rs; exact h13,
          b, j + 4, by omega, hb4, by omega, hstep hc,
          by rsE_rs; rw [hdi]; exact rsF_inc4 j (by omega), by rsE_rs; exact hdx,
          by rsE_rs; exact hax, by rsE_rs; exact hsi, by rsE_rs; exact hr8,
          by simp only [RegZmms.get_set_xmm_ne _ _ _ _
            (by decide : RegMm.mm1 ≠ RegMm.mm0)]; exact hx0⟩,
        Pst.down _ (Pval.down _ hx0')⟩, by
          left; simp only [lex_var]
          refine Kraken.lex_cons_lt_cons (by lex_len) ?_
          refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
          dsimp only
          simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hdi,
            rsF_inc4 j (by omega)]
          exact rsF_var _ _ _ (hstep hc) (by omega)⟩)
    case vc4 =>
      refine ⟨T.L2aef.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩,
        { st with x := { st.x with ftLow := (LowM (dD1 a k0 nm (fOf st)) (xoOf a) (fOf st)
          (b + j + 4)) } }, fr, nm, k0, hMa, hsp, hfm, hF, h40,
        ⟨hk2, hf64, hbr, P30.down, h38, b + j + 4, Px.down, by rsE_rs; exact h14,
          by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx, hfin hc,
          by rsE_rs; exact h13, by rsE_rs; rw [hax, ← hc]⟩, Pst.down _ (Pval.down _ hx0')⟩,
        by var_step⟩

end Kraken.Examples.Sbr.Reset
