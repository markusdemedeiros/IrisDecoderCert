import Kraken.MachineWP
import Kraken.SeparationMem

/-!
# Lemmas for leaf-procedure proofs

Lemmas the proofs of the SSE leaf routines found missing, collected from
their files so that each is stated once. They are not imported by
`MachineWP.lean`, only by the proofs that need them, because several of them
add `grind` patterns that fire on every memory access.

* `Blocks.Inside` for address shapes the rules of `SeparationMem.lean` do not
  match: a moving pointer plus two offsets (`ptr_add_add`), a base plus three
  offsets (`base_add_add_add`), a pointer alone (`ptr`), a negative index
  counting up to 0 (`neg_idx`, `neg_idx_disp`), and any `p + i + d` by its
  offset from the base (`of_sub3`).
* `jl` after `add` (`CondCode.interp_l_add`, the counterpart of
  `CondCode.interp_l_sub`).
* `jl`/`jge`/`jg`/`jle` after `cmp`/`sub` as `slt`/`sle`
  (`CondCode.interp_{l,ge,g,le}_cmp`; at width 32 also as the `toInt` order,
  `…_cmp_toInt32`), and `jl`/`jge` after `add` as the sign of
  the signed sum (`CondCode.interp_{l,ge}_add_toInt`).
* `toNat` of an arithmetic right shift of a value whose top bit is clear, and
  of a masked value.
* `Program.PlacedIn` of a sub-program.
-/

open Kraken

namespace Mem

/-- An access at offsets `c` and `x` from a pointer `p` into a block, given the
pointer's offset `p - a` from the base (`Blocks.Inside.ptr_add` for the
two-offset shape `p + c + x` of a `c(%p)` or `x(%p,%i,s)` operand: through the
generic memory rules a `c(%p)` operand reaches `Blocks.Inside` as `p + 0 + c`,
the empty index contributing the literal `0`, which `grind` does not fold out
of the middle of the sum). -/
theorem Blocks.Inside.ptr_add_add {w : Nat} {a p c x : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p - a).toNat + (c + x).toNat + n ≤ len) :
    Blocks.Inside (p + c + x) n ((a, len) :: bs) := by
  rw [BitVec.add_assoc]; exact Blocks.Inside.ptr_add h

/-- An access `a + c + x + d` into the block at `a`: an indexed operand
`d(%p,%i,s)` whose base register holds a pointer `p = a + c` at a constant
offset `c` into the block, such as `0x10(%rsi,%rcx,2)` with `rsi = src + 256`.
None of the shapes of `SeparationMem.lean` matches the extra displacement `d`. -/
theorem Blocks.Inside.base_add_add_add {w : Nat} {a c x d : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (c + x + d).toNat + n ≤ len) :
    Blocks.Inside (a + c + x + d) n ((a, len) :: bs) := by
  have e : a + c + x + d = a + (c + x + d) := by grind
  rw [e]; exact Blocks.Inside.base_add h

/-- An access at a pointer `p` into a block, given its offset `p - a` from
the base: `Blocks.Inside.ptr_add` at displacement 0, where the operand `(%r)`
leaves the address `p` itself rather than a sum. -/
theorem Blocks.Inside.ptr {w : Nat} {a p : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p - a).toNat + n ≤ len) :
    Blocks.Inside p n ((a, len) :: bs) :=
  Or.inl h

/-- The offset from the block's base of `p + i * c + d`, for a negative index
`i` that does not reach below the base. -/
theorem Blocks.Inside.neg_idx_off_eq {w : Nat} {a p i c d : BitVec w}
    (h : (0 - i).toNat * c.toNat ≤ (p - a).toNat) :
    (p + i * c + d - a).toNat = ((p - a).toNat - (0 - i).toNat * c.toNat + d.toNat) % 2 ^ w := by
  have hlt := (p - a).isLt
  have hm : ((0 - i) * c).toNat = (0 - i).toNat * c.toNat := by
    rw [BitVec.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have e : p + i * c + d - a = ((p - a) - (0 - i) * c) + d := by grind
  rw [e, BitVec.toNat_add, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hm]; exact h), hm]

/-- An access `p + i * c + d` into the block at `a`, where `p` lies `p - a`
bytes into the block and the index `i` is negative: `0 - i` elements of `c`
bytes lie between the access (before `d`) and `p`. The shape of
`movlps (%rdx,%rcx,4)` after `lea (%rdx,%rcx,4),%rdx; neg %rcx`; the rules of
`SeparationMem.lean` need the offset from the base to be a sum of
non-negative `toNat`s. -/
theorem Blocks.Inside.neg_idx_disp {w : Nat} {a p i c d : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (0 - i).toNat * c.toNat ≤ (p - a).toNat)
    (h2 : (p - a).toNat - (0 - i).toNat * c.toNat + d.toNat + n ≤ len) :
    Blocks.Inside (p + i * c + d) n ((a, len) :: bs) := by
  refine Or.inl ?_
  rw [Blocks.Inside.neg_idx_off_eq h]
  have := Nat.mod_le ((p - a).toNat - (0 - i).toNat * c.toNat + d.toNat) (2 ^ w)
  omega

/-- `Blocks.Inside.neg_idx_disp` without a displacement. -/
theorem Blocks.Inside.neg_idx {w : Nat} {a p i c : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (0 - i).toNat * c.toNat ≤ (p - a).toNat)
    (h2 : (p - a).toNat - (0 - i).toNat * c.toNat + n ≤ len) :
    Blocks.Inside (p + i * c) n ((a, len) :: bs) := by
  have := Blocks.Inside.neg_idx_disp (d := 0) (n := n) (len := len) (bs := bs) h
    (by simpa using h2)
  simpa using this

/-- An access at `p + i + d` inside the first block, by its offset from the
base: for addresses whose terms do not line up syntactically with the block's
base, e.g. `296 + rdi + (-296) + 0` (after `add %rdx,%rdi; neg %rdx`) or
`rdi' + (rdx + 8) + 16` with `rdi' = rdi + 296` known only as an equation.
The side condition is the offset from the base, which `grind`'s ring
normalisation simplifies. -/
theorem Blocks.Inside.of_sub3 {w : Nat} {a p i d : BitVec w} {n len : Nat}
    {bs : List (BitVec w × Nat)} (h : (p + i + d - a).toNat + n ≤ len) :
    Blocks.Inside (p + i + d) n ((a, len) :: bs) := Or.inl h

end Mem

/-! ## `grind` patterns, scoped

Each pattern or `grind` attribute of this file is `scoped`: they cost `grind`
time on every access or flag, and a proof that does not need them can time out
or fail where it passed before (measured on the leaf proofs: `ptr_add_add` in
`hf_apply_noise`, `interp_l_add` in `qmf_deint_neg`). A proof opens the
namespaces it needs, e.g. `open scoped Kraken.LeafLemmas.PtrAdd`. -/

-- `open scoped Kraken.LeafLemmas.PtrAdd`: `Blocks.Inside.ptr_add_add`.
namespace Kraken.LeafLemmas.PtrAdd
open Mem
-- As for `Blocks.Inside.ptr_add`, the offset `p - a` must be among the terms.
scoped grind_pattern Blocks.Inside.ptr_add_add =>
  Blocks.Inside (p + c + x) n ((a, len) :: bs), p - a
end Kraken.LeafLemmas.PtrAdd

-- `open scoped Kraken.LeafLemmas.BaseAdd`: `Blocks.Inside.base_add_add_add`.
namespace Kraken.LeafLemmas.BaseAdd
open Mem
scoped grind_pattern Blocks.Inside.base_add_add_add =>
  Blocks.Inside (a + c + x + d) n ((a, len) :: bs)
end Kraken.LeafLemmas.BaseAdd

-- `open scoped Kraken.LeafLemmas.NegIdx`: `Blocks.Inside.ptr`, `neg_idx`,
-- `neg_idx_disp`.
namespace Kraken.LeafLemmas.NegIdx
open Mem
scoped grind_pattern Blocks.Inside.ptr => Blocks.Inside p n ((a, len) :: bs), p - a
scoped grind_pattern Blocks.Inside.neg_idx_disp =>
  Blocks.Inside (p + i * c + d) n ((a, len) :: bs), p - a
scoped grind_pattern Blocks.Inside.neg_idx =>
  Blocks.Inside (p + i * c) n ((a, len) :: bs), p - a
end Kraken.LeafLemmas.NegIdx

-- `open scoped Kraken.LeafLemmas.Offset`: `Blocks.Inside.of_sub3`.
namespace Kraken.LeafLemmas.Offset
open Mem
-- The pattern alone would fire for every block of the list; the guard keeps
-- only the instance whose side condition the solvers can prove.
scoped grind_pattern Blocks.Inside.of_sub3 => Blocks.Inside (p + i + d) n ((a, len) :: bs) where
  check (p + i + d - a).toNat + n ≤ len
end Kraken.LeafLemmas.Offset

/-- The signed sum is negative, as unsigned arithmetic on the operands with
their sign bits flipped (as `BitVec.toInt_lt_toInt_iff_flip`). -/
theorem BitVec.toInt_add_neg_iff_flip (a b : BitVec 64) :
    a.toInt + b.toInt < 0
      ↔ (a.toNat + 2 ^ 63) % 2 ^ 64 + (b.toNat + 2 ^ 63) % 2 ^ 64 < 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

/-- `jl` after `add`: the flags of `a + b` read as "the signed sum is
negative", in the flipped unsigned form (the `add` counterpart of
`CondCode.interp_l_sub`). A loop counter that counts up to 0 by `add $k,%r`
needs it: without it `grind` case-splits on `BitVec.toInt` and fails to bound
the counter on the taken edge. -/
theorem CondCode.interp_l_add (a b : BitVec 64)
    (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((a + b).signed != a.signed + b.signed)) :
    CondCode.l.interp (StatusFlags.from_result (a + b) f)
      = decide ((a.toNat + 2 ^ 63) % 2 ^ 64 + (b.toNat + 2 ^ 63) % 2 ^ 64 < 2 ^ 64) := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result, hf]
  have : ((a + b).msb != ((a + b).signed != a.signed + b.signed))
      = decide (a.toInt + b.toInt < 0) := by
    grind [BitVec.signed_eq]
  simp only [this, BitVec.toInt_add_neg_iff_flip]

/-! ## Signed compares, as `slt`/`sle`

`cmp b,a` (and `sub`) leave the flags of `a - b`, with `of` the signed
overflow; `jl`/`jge`/`jg`/`jle` read them as the signed order of `a` and `b`.
The lemmas below state that reading as `BitVec.slt`/`BitVec.sle`, with no
hypothesis on the operands, at the widths 8, 16, 32 and 64 (the auto-param
`hw` is closed by `decide`, so `rw [CondCode.interp_l_cmp] at h` works at a
concrete width; `simp` does not discharge it). `CondCode.interp_l_sub` and
`_ge_sub` in `Specs.lean` state the same as unsigned arithmetic on flipped
sign bits, which suits `grind`; these suit a hand proof that reasons about
`toInt`. The `add` versions read the flags of `a + b` as the sign of the
signed sum. -/

theorem BitVec.msb_sub_bne_ssub {w} (a b : BitVec w)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    ((a - b).msb != ((a - b).signed != a.signed - b.signed)) = a.slt b := by
  rw [BitVec.slt_eq_decide]
  rcases hw with rfl | rfl | rfl | rfl <;> grind [BitVec.signed_eq]

theorem StatusFlags.zf_from_result_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result (a - b) f).zf = (a == b) := by
  simp only [StatusFlags.from_result, show BitVec.zero w = 0#w from rfl]
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0#w := fun h' => h (by
      have := congrArg (· + b) h'; simpa [BitVec.sub_add_cancel] using this)
    have h1 : (a - b == 0#w) = false := by simpa using this
    have h2 : (a == b) = false := by simpa using h
    rw [h1, h2]

theorem CondCode.interp_l_cmp {w} (a b : BitVec w) (cf af : Bool)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    CondCode.l.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed }) = a.slt b := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result]
  exact BitVec.msb_sub_bne_ssub a b hw

theorem CondCode.interp_ge_cmp {w} (a b : BitVec w) (cf af : Bool)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    CondCode.ge.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed }) = !a.slt b := by
  rw [← BitVec.msb_sub_bne_ssub a b hw, CondCode.interp_ge, StatusFlags.sf_from_result,
    StatusFlags.of_from_result]
  cases (a - b).msb <;> cases ((a - b).signed != a.signed - b.signed) <;> rfl

theorem CondCode.interp_g_cmp {w} (a b : BitVec w) (cf af : Bool)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    CondCode.g.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed }) = b.slt a := by
  have h := CondCode.interp_ge_cmp a b cf af hw
  rw [CondCode.interp_ge] at h
  rw [CondCode.interp_g, h, StatusFlags.zf_from_result_sub, BitVec.slt_eq_decide,
    BitVec.slt_eq_decide]
  by_cases e : a = b
  · subst e; simp
  · have hne : a.toInt ≠ b.toInt := fun h' => e (BitVec.eq_of_toInt_eq h')
    have : (a == b) = false := by simp [e]
    rw [this]
    by_cases hl : a.toInt < b.toInt
    · simp [hl]; omega
    · simp [hl]; omega

theorem CondCode.interp_le_cmp {w} (a b : BitVec w) (cf af : Bool)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    CondCode.le.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed }) = a.sle b := by
  have h := CondCode.interp_l_cmp a b cf af hw
  rw [CondCode.interp_l] at h
  rw [CondCode.interp_le, h, StatusFlags.zf_from_result_sub, BitVec.sle_eq_slt_or_eq]

/-! The same at width 32 as the `int` order of the `toInt`s, with no
auto-param, so that `simp` can use them (a counter compared with `cmpl`). -/

theorem CondCode.interp_l_cmp_toInt32 (a b : BitVec 32) (cf af : Bool) :
    CondCode.l.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (a.toInt < b.toInt) := by
  rw [CondCode.interp_l_cmp, BitVec.slt_eq_decide]

theorem CondCode.interp_ge_cmp_toInt32 (a b : BitVec 32) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (b.toInt ≤ a.toInt) := by
  rw [CondCode.interp_ge_cmp, BitVec.slt_eq_decide]
  by_cases h : a.toInt < b.toInt <;> simp [h] <;> omega

theorem CondCode.interp_g_cmp_toInt32 (a b : BitVec 32) (cf af : Bool) :
    CondCode.g.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (b.toInt < a.toInt) := by
  rw [CondCode.interp_g_cmp, BitVec.slt_eq_decide]

theorem CondCode.interp_le_cmp_toInt32 (a b : BitVec 32) (cf af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := (a - b).signed != a.signed - b.signed })
      = decide (a.toInt ≤ b.toInt) := by
  rw [CondCode.interp_le_cmp, BitVec.sle_eq_decide]

theorem CondCode.interp_l_add_toInt {w} (a b : BitVec w) (cf af : Bool)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    CondCode.l.interp (StatusFlags.from_result (a + b)
      { cf := cf, af := af, of := (a + b).signed != a.signed + b.signed })
      = decide (a.toInt + b.toInt < 0) := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result]
  rcases hw with rfl | rfl | rfl | rfl <;> grind [BitVec.signed_eq]

theorem CondCode.interp_ge_add_toInt {w} (a b : BitVec w) (cf af : Bool)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    CondCode.ge.interp (StatusFlags.from_result (a + b)
      { cf := cf, af := af, of := (a + b).signed != a.signed + b.signed })
      = decide (0 ≤ a.toInt + b.toInt) := by
  have h := CondCode.interp_l_add_toInt a b cf af hw
  rw [CondCode.interp_l] at h
  rw [CondCode.interp_ge]
  revert h
  cases ((StatusFlags.from_result (a + b) _).sf) <;> cases ((StatusFlags.from_result (a + b) _).of) <;>
    simp <;> omega

/-- An arithmetic right shift of a zero-extended 32-bit value is a division
(`mov %esi,%edx; sar $k,%rdx`). -/
theorem BitVec.toNat_sshiftRight_setWidth_32 (v : BitVec 64) (k : Nat) :
    (((v.setWidth 32).setWidth 64).sshiftRight k).toNat = v.toNat % 2 ^ 32 / 2 ^ k := by
  have e : ((v.setWidth 32).setWidth 64).toNat = v.toNat % 2 ^ 32 := by
    simp only [BitVec.toNat_setWidth]; omega
  rw [BitVec.sshiftRight_eq_of_msb_false (by rw [BitVec.msb_eq_decide, e]; simp; omega),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, e]

/-- An arithmetic right shift of the low three bits is a division
(`and $7,%rsi; sar $k,%rsi`). -/
theorem BitVec.toNat_sshiftRight_and_7 (v : BitVec 64) (k : Nat) :
    ((v &&& 7).sshiftRight k).toNat = v.toNat % 8 / 2 ^ k := by
  have h7 : (v &&& 7).toNat = v.toNat % 8 := by
    rw [BitVec.toNat_and]; show v.toNat &&& 7 = _
    exact Nat.and_two_pow_sub_one_eq_mod v.toNat 3
  rw [BitVec.sshiftRight_eq_of_msb_false (by rw [BitVec.msb_eq_decide, h7]; simp; omega),
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, h7]

-- `open scoped Kraken.LeafLemmas.AddFlags`: `CondCode.interp_l_add`.
namespace Kraken.LeafLemmas.AddFlags
attribute [scoped grind =] CondCode.interp_l_add
end Kraken.LeafLemmas.AddFlags

-- `open scoped Kraken.LeafLemmas.SignedCmp`: the `slt`/`sle` readings of `cmp`
-- and `add` flags.
namespace Kraken.LeafLemmas.SignedCmp
attribute [scoped grind =] CondCode.interp_l_cmp CondCode.interp_ge_cmp CondCode.interp_g_cmp
  CondCode.interp_le_cmp CondCode.interp_l_add_toInt CondCode.interp_ge_add_toInt
end Kraken.LeafLemmas.SignedCmp

-- `open scoped Kraken.LeafLemmas.Shift`: the two `toNat_sshiftRight` lemmas.
namespace Kraken.LeafLemmas.Shift
attribute [scoped grind =] BitVec.toNat_sshiftRight_setWidth_32 BitVec.toNat_sshiftRight_and_7
end Kraken.LeafLemmas.Shift

/-- A mask bounds the result: `(x &&& c).toNat ≤ c.toNat`. -/
theorem BitVec.toNat_and_le_right {w : Nat} (x c : BitVec w) : (x &&& c).toNat ≤ c.toNat := by
  rw [BitVec.toNat_and]; exact Nat.and_le_right

-- `open scoped Kraken.LeafLemmas.Mask`: `BitVec.toNat_and_le_right`.
namespace Kraken.LeafLemmas.Mask
scoped grind_pattern BitVec.toNat_and_le_right => (x &&& c).toNat
end Kraken.LeafLemmas.Mask

/-- A fragment whose blocks are among those of a placed fragment is placed
(`Program.PlacedIn.of_placed` with `PlacedIn` for `Placed`: its proof uses
only the `PlacedIn` fields). Lets one placed program carry several entry
points that share code. -/
theorem Program.PlacedIn.of_subBlocksOf [CodeEnv] {p q : Program}
    (hq : Program.PlacedIn q) (h : Program.subBlocksOf p q = true) : Program.PlacedIn p := by
  have key : ∀ l blk, Program.blockAt p l = some blk →
      ∃ blk', Program.blockAt q l = some blk' ∧ blk'.body = blk.body
        ∧ (blk.next.isNone = true ∨ blk'.next = blk.next) := by
    intro l blk hb
    have hmem : l ∈ (Program.view p).2.map (·.1) := by
      rw [← Program.labels_view]
      exact Program.blockAt_mem_labels hb
    obtain ⟨lb, hlb, rfl⟩ := List.mem_map.mp hmem
    have hall := List.all_eq_true.mp h lb hlb
    simp only [hb] at hall
    cases hb' : Program.blockAt q lb.1 with
    | none => rw [hb'] at hall; cases hall
    | some blk' =>
      rw [hb'] at hall
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hall
      exact ⟨blk', rfl, hall.1, hall.2⟩
  refine ⟨?_, ?_⟩
  · intro l blk hb
    obtain ⟨blk', hb', hbody, -⟩ := key l blk hb
    rw [← hbody]
    exact hq.block l blk' hb'
  · intro l blk l' hb hn
    obtain ⟨blk', hb', hbody, hnext⟩ := key l blk hb
    rw [hn] at hnext
    simp only [Option.isNone_some, Bool.false_eq_true, false_or] at hnext
    rw [← hbody]
    exact hq.next l blk' l' hb' hnext
