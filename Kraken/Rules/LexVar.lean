import Kraken.X64.Semantics

/-!
# Lexicographic variants

The control-flow rule (`Program.EdgeLt`) asks a variant `var : Label → MachineData → Nat`
that does not increase along an edge and decreases along a back edge. For a procedure with
nested loops the natural variant is a tuple compared lexicographically: per loop level a
*phase* (where in the enclosing loop body the label sits; it decreases along the text) and the
loop's *measure*. `lex ds` packs a tuple into a number, digit `d` taken modulo `2 ^ 64`, most
significant first; `lex_cmp` decides `lex ds ≤ lex ds'`, `<`, `=` digit by digit, leaving the
first differing digits as an arithmetic goal.

`slot64 s off` / `slot32 s off` read a frame slot (`rbp - off`) of the state `s`, for
measures kept in memory.
-/

/-- The per-label variant equations `var "l" s = lex [...]` of a generated table. -/
register_simp_attr lex_var

namespace Kraken

/-- The digits `ds` (each modulo `2 ^ 64`) as one number, most significant first.
Irreducible: compared only through the lemmas below (never by evaluation). -/
def lex : List Nat → Nat
  | [] => 0
  | d :: ds => d % 2 ^ 64 * 2 ^ (64 * ds.length) + lex ds

theorem lex_nil : lex [] = 0 := rfl
theorem lex_cons (d : Nat) (ds : List Nat) :
    lex (d :: ds) = d % 2 ^ 64 * 2 ^ (64 * ds.length) + lex ds := rfl

attribute [irreducible] lex

theorem lex_lt_pow : ∀ ds : List Nat, lex ds < 2 ^ (64 * ds.length)
  | [] => by simp [lex_nil]
  | d :: ds => by
    have ih := lex_lt_pow ds
    have hd : d % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    simp only [lex_cons, List.length_cons]
    have : 2 ^ (64 * (ds.length + 1)) = 2 ^ 64 * 2 ^ (64 * ds.length) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_comm]
    rw [this]
    have h2 : (d % 2 ^ 64 + 1) * 2 ^ (64 * ds.length) ≤ 2 ^ 64 * 2 ^ (64 * ds.length) :=
      Nat.mul_le_mul_right _ hd
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega

theorem lex_cons_lt_of_lt {a b : Nat} {as bs : List Nat} (hl : as.length = bs.length)
    (h : a % 2 ^ 64 < b % 2 ^ 64) : lex (a :: as) < lex (b :: bs) := by
  simp only [lex_cons]
  have h1 := lex_lt_pow as
  rw [hl] at h1 ⊢
  have h2 : (a % 2 ^ 64 + 1) * 2 ^ (64 * bs.length) ≤ b % 2 ^ 64 * 2 ^ (64 * bs.length) :=
    Nat.mul_le_mul_right _ h
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

theorem lex_cons_le_of_lt {a b : Nat} {as bs : List Nat} (hl : as.length = bs.length)
    (h : a % 2 ^ 64 < b % 2 ^ 64) : lex (a :: as) ≤ lex (b :: bs) :=
  Nat.le_of_lt (lex_cons_lt_of_lt hl h)

theorem lex_cons_lt_cons {a : Nat} {as bs : List Nat} (hl : as.length = bs.length)
    (h : lex as < lex bs) : lex (a :: as) < lex (a :: bs) := by
  simp only [lex_cons]; rw [hl]; omega

theorem lex_cons_le_cons {a : Nat} {as bs : List Nat} (hl : as.length = bs.length)
    (h : lex as ≤ lex bs) : lex (a :: as) ≤ lex (a :: bs) := by
  simp only [lex_cons]; rw [hl]; omega

/-- `lex [] ≤ lex []` and friends. -/
theorem lex_nil_le : lex [] ≤ lex [] := Nat.le_refl _

/-- An 8-byte frame slot `rbp - off` of `s` (`0` if unreadable). -/
def slot64 (s : MachineData) (off : Nat) : BitVec 64 :=
  BitVec.ofInt 64 ((s.dmem.loadInt (s.regs.get64 .rbp - BitVec.ofNat 64 off) 8).getD 0)

/-- A 4-byte frame slot `rbp - off` of `s` (`0` if unreadable). -/
def slot32 (s : MachineData) (off : Nat) : BitVec 32 :=
  BitVec.ofInt 32 ((s.dmem.loadInt (s.regs.get64 .rbp - BitVec.ofNat 64 off) 4).getD 0)

theorem slot64_of_load {s : MachineData} {off : Nat} {v : Int}
    (h : s.dmem.loadInt (s.regs.get64 .rbp - BitVec.ofNat 64 off) 8 = some v) :
    slot64 s off = BitVec.ofInt 64 v := by
  simp only [slot64, h, Option.getD_some]

theorem slot32_of_load {s : MachineData} {off : Nat} {v : Int}
    (h : s.dmem.loadInt (s.regs.get64 .rbp - BitVec.ofNat 64 off) 4 = some v) :
    slot32 s off = BitVec.ofInt 32 v := by
  simp only [slot32, h, Option.getD_some]

end Kraken

/-- Decide a comparison `lex ds ⋈ lex ds'` (`≤`, `<`, `=`) of tuples of one length: equal
leading digits are skipped (syntactically, up to instances), the first differing digit is left
as `a % 2 ^ 64 < b % 2 ^ 64` (try `simp [Nat.mod_eq_of_lt, BitVec.isLt]; omega`). -/
syntax "lex_cmp" : tactic
macro_rules
  | `(tactic| lex_cmp) => `(tactic|
      (repeat (first
        | (with_reducible refine Kraken.lex_cons_le_cons (by rfl) ?_)
        | (with_reducible refine Kraken.lex_cons_lt_cons (by rfl) ?_)
        | (with_reducible refine Kraken.lex_cons_le_of_lt (by rfl) ?_)
        | (with_reducible refine Kraken.lex_cons_lt_of_lt (by rfl) ?_)
        | (with_reducible exact Nat.le_refl _)
        | exact Nat.le_refl _
        | (with_reducible exact rfl)
        | exact rfl)))

namespace Kraken.LexVar
open Lean Elab Tactic Meta

/-- Fail unless the goal is literally `_ < _` (no unfolding of `<` into `≤`). -/
elab "lex_guard_lt" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless t.consumeMData.isAppOfArity ``LT.lt 4 do throwError "lex_guard_lt: not a `<` goal"

/-- Fail unless the goal is literally `_ ≤ _`. -/
elab "lex_guard_le" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless t.consumeMData.isAppOfArity ``LE.le 4 do throwError "lex_guard_le: not a `≤` goal"

/-- Fail unless the goal mentions `Kraken.lex` (the `lex` closers are never tried on other goals:
unifying machine-state terms there evaluates them). -/
elab "lex_guard_lex" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless (t.find? fun e => e.isConstOf ``Kraken.lex).isSome do throwError "lex_guard_lex: no lex"

end Kraken.LexVar

open Lean Elab Tactic Meta in
/-- Succeeds iff the main goal mentions the string literal `l`. Guard for jump-target tactics:
unifying `label "A"` with `label "B"` evaluates `label` and blows the recursion limit, which
`try` does not catch. -/
elab "goal_has_str " l:str : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let s := l.getString
  unless (t.find? fun e => match e with | .lit (.strVal v) => v == s | _ => false).isSome do
    throwError "goal_has_str: no {s}"

/-- The first differing digit `a % 2 ^ 64 < b % 2 ^ 64`: literals, or values of bit-vectors. The
`% 2 ^ 64` are stripped before `omega` (plain `omega` on `(3 * (48 - a) + 0) % 2 ^ 64 < …`
hangs, unbounded by heartbeats). -/
syntax "lex_digit" : tactic
macro_rules
  | `(tactic| lex_digit) => `(tactic| first
      | (simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]; done)
      | (rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
      | (simp only [Nat.reduceMod, Nat.mod_eq_of_lt (BitVec.isLt _)]; omega)
      | omega)

/-- Same-length tuple length side goal of the `lex_cons_*` lemmas. -/
syntax "lex_len" : tactic
macro_rules
  | `(tactic| lex_len) => `(tactic| simp only [List.length_cons, List.length_nil])

/-- A variant obligation of a block exit, closed or failing (`var l' s ≤ n`, `var l' s < n`, with
`hn : var l s₀ = n` in context): unfold the variants (`lex_var` lemmas), substitute `n`, read the
registers, then compare digit by digit by the goal's shape: equal heads skipped (reducible
unification only, so state terms are never evaluated), the first differing digit by `lex_digit`.
No `decide`. -/
syntax "var_step" : tactic
macro_rules
  | `(tactic| var_step) => `(tactic| (
      try simp only [lex_var]
      try subst_vars
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      first
      | done
      | (lex_guard_lex
         lex_guard_lt
         repeat (with_reducible refine Kraken.lex_cons_lt_cons (by lex_len) ?_)
         with_reducible refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
         lex_digit)
      | (lex_guard_lex
         lex_guard_le
         repeat (with_reducible refine Kraken.lex_cons_le_cons (by lex_len) ?_)
         first
         | (with_reducible exact Nat.le_refl _)
         | exact Nat.le_refl _
         | (with_reducible refine Kraken.lex_cons_le_of_lt (by lex_len) ?_
            lex_digit))))

/-- The edge-order obligation `Program.EdgeLt body var l n l' s` of a jump: the variant
decreased (`var_step`), or it is unchanged and the target is later in the text (the
`lex_var` block-index equations, literal comparison). -/
syntax "edge_step" : tactic
macro_rules
  | `(tactic| edge_step) => `(tactic| first
      | (left; var_step)
      | (right; constructor
         · var_step
         · first
           | (simp only [lex_var]; done)
           | (simp only [lex_var]; decide)))
