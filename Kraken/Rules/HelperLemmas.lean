import Kraken.MachineWP
import Kraken.Rules.LeafLemmas
import Kraken.Rules.FrameLemmas
import Kraken.Rules.ScalarFloat

/-!
# Instruction rules and memory/flag lemmas for block-by-block proofs

Collected from the proofs of `sbr_lf_gen`, `sbr_hf_inverse_filter`,
`sbr_x_gen` and `sbr_hf_assemble` (FFmpeg `libavcodec/aacsbr_template.c`),
where each was found missing (and several were written more than once).

* Instruction rules: `inc %r64` (`MachineWP.inc_reg_w64_spec`), `shl $i, %r64`
  with a nonzero count (`MachineWP.shl_reg64_imm_spec`), and `ud1` with the
  precondition `False` (`MachineWP.ud1_spec`: a block that falls into a
  compiler-inserted bounds-check trap must show the edge unreachable).
* `Blocks.Inside` for an access at the base of a block placed at a negative
  offset (`Mem.Blocks.Inside.self_off`) and at `p + d` by its offset
  (`Mem.Blocks.Inside.of_sub2`, the two-term counterpart of `of_sub3`).
* Memory: `n` consecutive `w`-byte cells as one predicate with a
  variable-index load (`Mem.CellArr`, `Mem.CellArr.loadInt`); two 8-byte
  stores into unknown cells of a view (`Mem.Block.storeInt_val2`); a load
  below/above an 8-byte store off the same base (`Mem.loadInt_storeInt_sub_lo`,
  `_hi`); a load that succeeded still succeeds after a store
  (`Mem.loadInt_isSome_storeInt`); prefixes of a known cell
  (`Mem.Val.loadInt_prefix`, `Mem.Val.loadInt_lo4`, `Int.toBytes_add`,
  `Int.toBytes_add_take`, `Int.toBytes8_take1`).
* Flags of `cmp` as relations of the operands' values (`BitVec.sub_cf_eq_decide_lt`,
  `BitVec.sub_beq_zero`, `CondCode.interp_l_sub32`/`64`,
  `CondCode.interp_nc_sub8`/`64`, …), and `BitVec.ofNat` offset folding.
* Negative displacements: `BitVec.add_ofNat_eq_sub_ofNat` rewrites
  `x + 18446744073709551584#64` to `x - 32#64`. Prefer this (or
  `rw [BitVec.sub_eq_add_neg]; rfl` on a closed literal) to `toNat`
  arithmetic: `simp [toNat_*]; omega` on a goal containing such a literal can
  exhaust memory.

The `grind` patterns and attributes are scoped:
`open scoped Kraken.HelperLemmas.SelfOff` (`Blocks.Inside.self_off`),
`Kraken.HelperLemmas.Offset2` (`Blocks.Inside.of_sub2`),
`Kraken.HelperLemmas.Bytes16` (`BitVec.ofInt128_ofBytes_toBytes16`), and the `shl` rule
`Kraken.HelperLemmas.Shl64` (`MachineWP.shl_reg64_imm_spec`).
-/

open Kraken Mem Std.WP MachineWP

/-! ## Instruction rules -/

namespace MachineWP

section
variable [CodeEnv] {p : Program} {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- `inc %r` (64-bit): the register plus one; the carry flag is kept, the
other flags as `Semantics.lean` sets them. -/
@[spec] theorem inc_reg_w64_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := s.regs.get64 r
        let v := a + 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r v,
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                    of := v.signed != a.signed + 1 } } ⦄
      (Directive.instr (.regular asz .W64 (.inc (.reg (.low r .W64)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All]
    exact hP)

/-- `ud1` traps (no successor): a block that falls into one must show the
edge unreachable, so the precondition is `False`. -/
@[spec] theorem ud1_spec (asz w : Width) (r : Reg w) (src : RegOrMem w) :
    ⦃ fun _ => False ⦄ (Directive.instr (.regular asz w (.ud1 r src)) :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun _ h => h.elim

set_option linter.unusedSimpArgs false in
open Lean.Order in
/-- `shl $i, %r64` for a nonzero masked count, flags arbitrary (64-bit counterpart of
`MachineWP.shl_reg32_imm_spec`; the generic step keeps an `if count = 0` over the whole state).
Not a global `spec`: proofs written against the generic `shl` rule state the shift as
`<<< c`; `open scoped Kraken.HelperLemmas.Shl64` turns it on. -/
theorem shl_reg64_imm_spec (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a : BitVec 64 := s.regs.get64 r
        let n := i.toBitVec.toNat % 64
        (n ≠ 0) ⊓ (∀ st : StatusFlags, WP.wp p Q E
          { s with regs := s.regs.set64 r (a <<< n), status := st }) ⦄
      (Directive.instr (.regular asz .W64 (.shl (.reg (.low r .W64)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, Operand.interp, RegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All,
      or_false, false_or]
    simp only [meet_prop_eq_and] at h
    obtain ⟨hz, hk⟩ := h
    have hn : ∀ (L : Labels) rng,
        @ShiftCountExpr.interpMasked L (.imm8 (.int64 i)) s rng Width.W64
          = i.toBitVec.toNat % 64 := fun _ _ => by
      show (i.toBitVec.take 8).toNat &&& (2 ^ 6 - 1) = _
      rw [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (by decide)]
    simp only [hn, hz, beq_iff_eq, ite_false]
    repeat (first | exact hk _ _ hpl' | intro _ | split | simp only [Effects.All])

end

end MachineWP

-- `open scoped Kraken.HelperLemmas.Shl64`: `MachineWP.shl_reg64_imm_spec` as a `spec`.
namespace Kraken.HelperLemmas.Shl64
attribute [scoped spec] MachineWP.shl_reg64_imm_spec
end Kraken.HelperLemmas.Shl64

/-! ## `Blocks.Inside` -/

namespace Mem

/-- An access `a` (an operand `(%r)` or `(%r,%i,s)` without displacement)
into the block at `a + c'`: the last store of a run that starts at a negative
displacement. Companion of `Blocks.Inside.add_off`. -/
theorem Blocks.Inside.self_off {w : Nat} {a c' : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (0 - c').toNat + n ≤ len) :
    Blocks.Inside a n ((a + c', len) :: bs) :=
  Or.inl (by
    have e : a - (a + c') = 0 - c' := by grind
    rw [e]; exact h)

/-- An access at `p + d` inside the first block, by its offset from the base:
the two-term counterpart of `Blocks.Inside.of_sub3`, for a `d(%p)` operand
(a local through `rbp` into a block based at `rsp₀ - c`, or a negative
displacement after normalisation). -/
theorem Blocks.Inside.of_sub2 {w : Nat} {a p d : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p + d - a).toNat + n ≤ len) :
    Blocks.Inside (p + d) n ((a, len) :: bs) := Or.inl h

end Mem

-- `open scoped Kraken.HelperLemmas.SelfOff`: `Blocks.Inside.self_off`.
namespace Kraken.HelperLemmas.SelfOff
open Mem
scoped grind_pattern Blocks.Inside.self_off => Blocks.Inside a n ((a + c', len) :: bs)
end Kraken.HelperLemmas.SelfOff

-- `open scoped Kraken.HelperLemmas.Offset2`: `Blocks.Inside.of_sub2` (guarded,
-- as `Kraken.LeafLemmas.Offset`).
namespace Kraken.HelperLemmas.Offset2
open Mem
scoped grind_pattern Blocks.Inside.of_sub2 => Blocks.Inside (p + d) n ((a, len) :: bs) where
  check (p + d - a).toNat + n ≤ len
end Kraken.HelperLemmas.Offset2

/-! ## Cells, loads and stores -/

namespace Mem

/-- `n` consecutive `w`-byte cells holding `f 0, f 1, …` from `base`, then `R`. -/
def CellArr (w : Nat) (base : BitVec 64) (f : Nat → Int) : Nat → (Mem 64 → Prop) → Mem 64 → Prop
  | 0, R => R
  | n + 1, R => Int.toBytes w (f 0) =@ base ⋆ CellArr w (base + BitVec.ofNat 64 w) (fun k => f (k + 1)) n R

/-- Variable-index load from a cell array: cell `i < n` at `base + w*i`
(by induction on `n`, no `grind`). -/
theorem CellArr.loadInt {w n : Nat} {base : BitVec 64} {f : Nat → Int} {X R : Mem 64 → Prop}
    {m : Mem 64} (h : m =⋆ X ⋆ CellArr w base f n R) (hw : w ≤ 2 ^ 64) (i : Nat) (hi : i < n) :
    m.loadInt (base + BitVec.ofNat 64 (w * i)) w = some (Int.ofBytes (Int.toBytes w (f i))) := by
  induction n generalizing base f i X with
  | zero => omega
  | succ n ih =>
    simp only [CellArr] at h
    cases i with
    | zero =>
      simp only [Nat.mul_zero, BitVec.add_zero]
      exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) hw
    | succ j =>
      rw [← Std.ExtHashMap.sep_assoc] at h
      have := ih h j (by omega)
      rw [show base + BitVec.ofNat 64 (w * (j + 1)) = base + BitVec.ofNat 64 w + BitVec.ofNat 64 (w * j) by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; rw [Nat.mul_succ]; omega]
      exact this

/-- Two 8-byte stores into two unknown cells of a view, read back as the view
`H'` with both cells known. -/
theorem Block.storeInt_val2 {m : Mem 64} {H H' R1 R2 Ra : Mem 64 → Prop} {a1 a2 w1 w2 : BitVec 64}
    {v1 v2 : Int}
    (h : m =⋆ H) (s1 : Mem.Split (8 ?@ a1) R1 H) (s2 : Mem.Split (8 ?@ a2) R2 R1)
    (t1 : Mem.Split (Int.toBytes 8 w1.toInt =@ a1) Ra H')
    (t2 : Mem.Split (Int.toBytes 8 w2.toInt =@ a2) R2 Ra)
    (e1 : v1 = w1.toInt) (e2 : v2 = w2.toInt) :
    (m.storeInt a1 8 v1).storeInt a2 8 v2 =⋆ H' := by
  have h1 := Mem.Block.storeInt_val h s1 v1
  have h2 := Mem.Block.storeInt_val h1 (Mem.Split.right s2 _) v2
  unfold Mem.Split at t1 t2
  rw [t1, t2, ← e1, ← e2, Std.ExtHashMap.sep_comm_l]
  exact h2

/-- A load `d` bytes below the base `r` is untouched by an 8-byte store `c`
bytes below it, `c + 8 ≤ d`. -/
theorem loadInt_storeInt_sub_lo (m : Mem 64) (r : BitVec 64) (c d : Nat) (v : Int)
    (h : c + 8 ≤ d) (hd : d + 8 < 2 ^ 64) :
    (m.storeInt (r - BitVec.ofNat 64 c) 8 v).loadInt (r - BitVec.ofNat 64 d) 8
      = m.loadInt (r - BitVec.ofNat 64 d) 8 := by
  apply Mem.loadInt_storeInt_of_above <;>
  · rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (2 ^ 64 - (d - c)) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega, BitVec.toNat_ofNat]
    omega

/-- A load `d` bytes below `r` is untouched by an 8-byte store `c` bytes below
it, `d + 8 ≤ c`. -/
theorem loadInt_storeInt_sub_hi (m : Mem 64) (r : BitVec 64) (c d : Nat) (v : Int)
    (h : d + 8 ≤ c) (hc : c + 8 < 2 ^ 64) :
    (m.storeInt (r - BitVec.ofNat 64 c) 8 v).loadInt (r - BitVec.ofNat 64 d) 8
      = m.loadInt (r - BitVec.ofNat 64 d) 8 := by
  apply Mem.loadInt_storeInt_of_above <;>
  · rw [show r - BitVec.ofNat 64 d - (r - BitVec.ofNat 64 c) = BitVec.ofNat 64 (c - d) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega, BitVec.toNat_ofNat]
    omega

/-- Stores only add or overwrite bytes, so a load that succeeded before a
store still succeeds. -/
theorem loadInt_isSome_storeInt {w} (m : Mem w) (a b : BitVec w) (n k : Nat) (v : Int)
    (h : (m.loadInt b k).isSome = true) : ((m.storeInt a n v).loadInt b k).isSome = true := by
  simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.krakenAllSome_isSome_iff, List.mem_map,
    List.mem_range, forall_exists_index, and_imp] at h ⊢
  rintro o i hi rfl
  have := h _ i hi rfl
  rw [Mem.storeInt, Mem.storeBytes, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.union_eq,
    Std.ExtHashMap.getElem?_union]
  rw [Std.ExtHashMap.get?_eq_getElem?] at this
  cases h' : ((Int.toBytes n v).At a)[b + BitVec.ofNat w i]? <;> simp_all

end Mem

/-- The little-endian image of `v` in `a + b` bytes: the first `a` bytes, then
the image of `v / 256 ^ a`. -/
theorem Int.toBytes_add (a b : Nat) (v : Int) :
    Int.toBytes (a + b) v = Int.toBytes a v ++ Int.toBytes b (v / 256 ^ a) := by
  induction a generalizing v with
  | zero => simp [Int.toBytes]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [Int.toBytes, ih, List.cons_append]
    first
      | rw [Int.ediv_ediv (by decide), Int.pow_succ', Int.mul_comm]
      | rw [Int.ediv_ediv_of_nonneg (by decide), Int.pow_succ', Int.mul_comm]
      | (rw [Int.pow_succ', Int.mul_comm, ← Int.ediv_ediv_eq_ediv_mul])
      | (rw [Int.pow_succ']; exact (Int.ediv_ediv_eq_ediv_mul ..).trans (by rw [Int.mul_comm]))
      | (simp [Int.ediv_ediv, Int.pow_succ, Int.mul_comm])

/-- The first `a` bytes of an `a + b`-byte image. -/
theorem Int.toBytes_add_take (a b : Nat) (v : Int) :
    (Int.toBytes (a + b) v).take a = Int.toBytes a v := by
  induction a generalizing v with
  | zero => simp [Int.toBytes]
  | succ n ih =>
    rw [show n + 1 + b = (n + b) + 1 by omega]
    simp [Int.toBytes, ih]

/-- The low byte of an 8-byte little-endian image. -/
theorem Int.toBytes8_take1 (v : Int) : (Int.toBytes 8 v).take 1 = Int.toBytes 1 v := by
  simp [Int.toBytes]

/-- Loading a prefix of a known cell (`testb` of the low byte of an 8-byte slot). -/
theorem Mem.Val.loadInt_prefix {w : Nat} {H R : Mem w → Prop} {m : Mem w} {a : BitVec w}
    {bs : List UInt8} {k : Nat} (h : m =⋆ H) (hs : Mem.Split (bs =@ a) R H)
    (hk : k ≤ bs.length) (hw : bs.length ≤ 2 ^ w) :
    m.loadInt a k = some (Int.ofBytes (bs.take k)) := by
  rw [hs] at h
  have e : (bs =@ a) = Eq ((bs.take k).At a) ⋆ Eq ((bs.drop k).At (a + .ofNat _ (bs.take k).length)) := by
    rw [Mem.Val.eq, ← Mem.At_append_sep _ _ _ (by simp only [List.length_take, List.length_drop]; omega),
      List.take_append_drop]
  rw [e, Std.ExtHashMap.sep_assoc] at h
  exact Mem.loadInt_sep _ a k _ m h (by simp only [List.length_take]; omega) (by omega)

/-- The low 4 bytes of an 8-byte cell. -/
theorem Mem.Val.loadInt_lo4 {H R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64} {v : Int}
    (h : m =⋆ H) (hs : Mem.Split (Int.toBytes 8 v =@ a) R H) :
    m.loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 v)) := by
  rw [hs] at h
  have := Mem.loadInt_slice (addr := a) (n := 4) h (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [this, BitVec.sub_self, BitVec.toNat_zero, List.drop_zero,
    show (8 : Nat) = 4 + 4 from rfl, Int.toBytes_add_take]

/-- A 16-byte cell read back into an xmm register. -/
theorem BitVec.ofInt128_ofBytes_toBytes16 (v : Int) :
    BitVec.ofInt 128 (Int.ofBytes (Int.toBytes 16 v)) = BitVec.ofInt 128 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 128 16 rfl v

-- `open scoped Kraken.HelperLemmas.Bytes16`: `BitVec.ofInt128_ofBytes_toBytes16`.
namespace Kraken.HelperLemmas.Bytes16
attribute [scoped grind =] BitVec.ofInt128_ofBytes_toBytes16
end Kraken.HelperLemmas.Bytes16

/-- A VEX write to a ymm register leaves the other xmm registers. -/
theorem RegZmms.get_set_ymm_xmm_ne (s : RegZmms) (x y : RegMm) (v : BitVec 256)
    (h : x ≠ y) : (s.set (.ymm x) v).get (.xmm y) = s.get (.xmm y) := by
  simp only [RegZmms.get, RegZmms.set, AvxReg.base]
  rw [RegZmms.get512_set512_ne _ _ _ _ h]

/-! ## Flags of `cmp`, and offsets -/

/-- The carry flag of a `cmp` of any width, as the unsigned order of the operands. -/
theorem BitVec.sub_cf_eq_decide_lt {w : Nat} (a b : BitVec w) :
    ((((a - b).toNat : Int)) != ((a.toNat : Int) - (b.toNat : Int))) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · rw [Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_true, bne_iff_ne, ne_eq]
    omega
  · have e : 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp only [h, decide_false, bne_eq_false_iff_eq]
    omega

/-- `BitVec.sub_cf_eq_decide_lt` at width 32. -/
theorem BitVec.sub_cf32_eq_decide_lt (a b : BitVec 32) :
    ((((a - b).toNat : Int)) != ((a.toNat : Int) - (b.toNat : Int))) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    omega

/-- The carry flag of a 64-bit `cmp` (as `Semantics` computes it), as the
unsigned order of the operands. -/
theorem BitVec.sub_cf64_eq_decide_lt (a b : BitVec 64) :
    ((((a - b).toNat : Int)) != ((a.toNat : Int) - (b.toNat : Int))) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    omega

/-- The zero flag of a result, as an equation of its value. -/
theorem BitVec.beq_zero_eq_decide {w : Nat} (a : BitVec w) :
    (a == BitVec.zero w) = decide (a.toNat = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro rfl; simp [BitVec.zero]
  · intro h; apply BitVec.eq_of_toNat_eq; simp [BitVec.zero, h]

/-- The zero flag of a `cmp` of any width, as an equation of the operands' values. -/
theorem BitVec.sub_beq_zero {w : Nat} (a b : BitVec w) :
    ((a - b) == BitVec.zero w) = decide (a.toNat = b.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have h2 : a - b + b = 0#w + b := congrArg (· + b) h
    simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h2
    rw [h2]
  · intro h; rw [BitVec.eq_of_toNat_eq h]; simp [BitVec.zero]

/-- The zero flag of a 64-bit `cmp`, as an equation of the operands' values. -/
theorem BitVec.sub64_beq_zero (a b : BitVec 64) :
    ((a - b) == BitVec.zero 64) = decide (a.toNat = b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub] at this
    have h0 : (BitVec.zero 64).toNat = 0 := rfl
    omega
  · intro h; rw [BitVec.eq_of_toNat_eq h]; simp

/-- The zero flag of `cmp` between two in-range literals, as a `Nat` equation. -/
theorem BitVec.ofNat64_sub_beq_zero (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) == BitVec.zero 64) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    have h0 : (BitVec.zero 64).toNat = 0 := rfl
    omega
  · rintro rfl; simp

/-- `BitVec.ofNat64_sub_beq_zero` against an immediate in literal form. -/
theorem BitVec.ofNat64_sub_lit_beq_zero (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a - (no_index (OfNat.ofNat b : BitVec 64))) == BitVec.zero 64)
      = decide (a = b) :=
  BitVec.ofNat64_sub_beq_zero a b ha hb

/-- `jl` after a 32-bit `cmp`/`sub`, as the signed order of the operands. -/
theorem CondCode.interp_l_sub32 (a b : BitVec 32) (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((a - b).signed != a.signed - b.signed)) :
    CondCode.l.interp (StatusFlags.from_result (a - b) f) = decide (a.toInt < b.toInt) := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result, hf]
  grind [BitVec.signed_eq]

/-- `jl` after a 64-bit `cmp`/`sub`, as the signed order of the operands. -/
theorem CondCode.interp_l_sub64 (a b : BitVec 64) (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((a - b).signed != a.signed - b.signed)) :
    CondCode.l.interp (StatusFlags.from_result (a - b) f) = decide (a.toInt < b.toInt) := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result, hf]
  grind [BitVec.signed_eq]

/-- `jae`/`jnc` after a 64-bit `cmp`/`sub`, as the unsigned order of the operands. -/
theorem CondCode.interp_nc_sub64 (a b : BitVec 64) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, hf]
  grind [BitVec.unsigned_eq]

/-- `jae`/`jnc` after an 8-bit `cmp`/`sub`, as the unsigned order of the operands. -/
theorem CondCode.interp_nc_sub8 (a b : BitVec 8) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, hf]
  grind [BitVec.unsigned_eq]

/-- A small natural as a signed 64-bit value. -/
theorem BitVec.toInt_ofNat64_of_lt (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_ofNat]; omega
  · simp [BitVec.msb_eq_decide]; omega

/-- A negative displacement as a subtraction: `x + (2^w - c) = x - c`, e.g.
`x + 18446744073709551584#64 = x - 32#64` (`n + c = 2 ^ w` by `decide`). -/
theorem BitVec.add_ofNat_eq_sub_ofNat {w : Nat} (x : BitVec w) (n c : Nat) (h : n + c = 2 ^ w) :
    x + BitVec.ofNat w n = x - BitVec.ofNat w c := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp only [Nat.add_zero] at h; subst h; simp
  · have hn : n < 2 ^ w := by omega
    have hc' : c < 2 ^ w ∨ c = 2 ^ w := by omega
    rcases hc' with hc' | hc'
    · rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hc']
      have : 2 ^ w - c = n := by omega
      rw [this, Nat.add_comm]
    · subst hc'; have : n = 0 := by omega
      subst this; simp

/-- Folding a chain of `push`es: `a - b - c = a - (b + c)`. -/
theorem BitVec.sub_ofNat_sub_ofNat64 (a : BitVec 64) (b c : Nat) :
    a - BitVec.ofNat 64 b - BitVec.ofNat 64 c = a - BitVec.ofNat 64 (b + c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A negative displacement off a pushed-down base: `a - b + c = a - (b + (2^64 - c))`. -/
theorem BitVec.sub_ofNat_add_ofNat64 (a : BitVec 64) (b c : Nat) (hc : c < 2 ^ 64) :
    a - BitVec.ofNat 64 b + BitVec.ofNat 64 c = a - BitVec.ofNat 64 (b + (2 ^ 64 - c)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Folding an immediate into a `BitVec.ofNat` offset. -/
theorem BitVec.ofNat64_add_lit (a b : Nat) :
    BitVec.ofNat 64 a + (no_index (OfNat.ofNat b : BitVec 64)) = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

/-- `BitVec.ofNat64_add_lit` with the immediate first. -/
theorem BitVec.ofNat64_lit_add (a b : Nat) :
    (no_index (OfNat.ofNat b : BitVec 64)) + BitVec.ofNat 64 a = BitVec.ofNat 64 (b + a) :=
  (BitVec.ofNat_add b a).symm

/-- Moving an immediate past a base: `c + (a + m) = a + (m + c)`. -/
theorem BitVec.ofNat64_lit_shift (a : BitVec 64) (m c : Nat) :
    BitVec.ofNat 64 c + (a + BitVec.ofNat 64 m) = a + BitVec.ofNat 64 (m + c) := by
  rw [BitVec.ofNat_add]; ac_rfl

/-- Folding a negative displacement into a positive offset: `m + c` with `c`
the two's-complement image of `-(2^64 - c)` and `m` large enough. Used with
`simp (disch := omega)` to turn `a + K m + (-d)` into `a + K (m - d)`. -/
theorem BitVec.ofNat64_add_wrap (m c : Nat) (hc : c < 2 ^ 64) (hc' : 2 ^ 63 ≤ c)
    (h : 2 ^ 64 - c ≤ m) : BitVec.ofNat 64 (m + c) = BitVec.ofNat 64 (m - (2 ^ 64 - c)) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- Folding a scaled index (`(%r13,%r8,2)`) into a `BitVec.ofNat` offset. -/
theorem BitVec.ofNat64_mul_ofNat (a b : Nat) :
    BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [← Nat.mul_mod]

/-- `BitVec.ofNat64_mul_ofNat` against a literal scale. -/
theorem BitVec.ofNat64_mul_lit (a b : Nat) :
    BitVec.ofNat 64 a * (no_index (OfNat.ofNat b : BitVec 64)) = BitVec.ofNat 64 (a * b) :=
  BitVec.ofNat64_mul_ofNat a b
