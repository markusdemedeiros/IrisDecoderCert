import SbrClient.Host.Language
import Iris.ProgramLogic.Lifting

namespace SbrClient.Host
open Kraken Iris Iris.ProgramLogic Iris.ProgramLogic.Language.Notation Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

theorem insert_current {m : Mem 64} {a : BitVec 64} {v : UInt8} (h : m[a]? = some v) :
    m.insert a v = m := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  by_cases heq : a = k
  · subst k
    simp [h]
  · simp [Std.ExtHashMap.getElem?_insert, heq]

structure HeapOp (e : Expr M) (a : BitVec 64) (f : UInt8 → Value × UInt8) : Prop where
  nonvalue : toVal e = none
  step : ∀ m old, m[a]? = some old →
    Step M (e, m) [] (.ret (f old).1, m.insert a (f old).2, [])
  invert : ∀ {m old obs e' m' efs}, m[a]? = some old → Step M (e, m) obs (e', m', efs) →
    obs = [] ∧ e' = .ret (f old).1 ∧ m' = m.insert a (f old).2 ∧ efs = []

theorem wp_heapop {e : Expr M} {a : BitVec 64} {f : UInt8 → Value × UInt8}
    (op : HeapOp e a f) (old : UInt8) {E : CoPset} {Φ : Value → IProp GF} :
    pointsTo a (DFrac.own 1) old ∗
      ▷ (pointsTo a (DFrac.own 1) (f old).2 -∗ Φ (f old).1) ⊢
      WP e @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Ha, HK⟩
  iapply wp_lift_atomic_step op.nonvalue
  iintro %σ %ns %obs %obs' %nt Hσ
  ihave %ha : ⌜σ[a]? = some old⌝ $$ [Hσ Ha]
  · icases genHeap_valid (H := ByteMap) $$ [$Hσ $Ha] with >%ha
    itrivial
  imodintro
  isplit
  · ipureintro
    exact ⟨[], _, _, [], op.step σ old ha⟩
  inext
  iintro %e' %σ' %efs %hs _
  obtain ⟨rfl, rfl, rfl, rfl⟩ := op.invert ha hs
  imod genHeap_update (H := ByteMap) (v₂ := (f old).2) $$ [$Hσ $Ha] with ⟨Hσ, Ha⟩
  imodintro
  simp only [Algebra.BigOpL.bigOpL_nil]
  iframe Hσ
  isplitl [Ha HK]
  · iexists (f old).1
    isplit
    · ipureintro; rfl
    · iapply HK $$ Ha
  · itrivial

theorem load_op (a : BitVec 64) : HeapOp (Expr.load (M := M) a) a (fun v => (.byte v, v)) where
  nonvalue := rfl
  step m v h := by simpa only [insert_current h] using Step.load h
  invert h hs := by
    cases hs with
    | load h' =>
        cases h.symm.trans h'
        exact ⟨rfl, rfl, (insert_current h).symm, rfl⟩

theorem store_op (a : BitVec 64) (v : UInt8) :
    HeapOp (Expr.store (M := M) a v) a (fun _ => (.unit, v)) where
  nonvalue := rfl
  step m old h := Step.store h
  invert _ hs := by cases hs; exact ⟨rfl, rfl, rfl, rfl⟩

theorem cas_op (a : BitVec 64) (expected desired : UInt8) :
    HeapOp (Expr.cas (M := M) a expected desired) a
      (fun old => (.bool (old == expected), if old == expected then desired else old)) where
  nonvalue := rfl
  step m old h := by
    have hs := Step.cas (M := M) (expected := expected) (desired := desired) h
    by_cases heq : old == expected
    · simpa [heq] using hs
    · simpa [heq, insert_current h] using hs
  invert h hs := by
    cases hs with
    | cas h' =>
        cases h.symm.trans h'
        refine ⟨rfl, rfl, ?_, rfl⟩
        split <;> simp_all [insert_current]

theorem wp_load (a : BitVec 64) (v : UInt8) {E : CoPset} {Φ : Value → IProp GF} :
    pointsTo a (DFrac.own 1) v ∗ ▷ (pointsTo a (DFrac.own 1) v -∗ Φ (.byte v)) ⊢
      WP (Expr.load (M := M) a) @ Stuckness.NotStuck; E {{ Φ }} := wp_heapop (load_op a) v

theorem wp_store (a : BitVec 64) (old v : UInt8) {E : CoPset} {Φ : Value → IProp GF} :
    pointsTo a (DFrac.own 1) old ∗ ▷ (pointsTo a (DFrac.own 1) v -∗ Φ .unit) ⊢
      WP (Expr.store (M := M) a v) @ Stuckness.NotStuck; E {{ Φ }} := wp_heapop (store_op a v) old

theorem wp_cas (a : BitVec 64) (old expected desired : UInt8) {E : CoPset} {Φ : Value → IProp GF} :
    pointsTo a (DFrac.own 1) old ∗
      ▷ (pointsTo a (DFrac.own 1) (if old == expected then desired else old) -∗ Φ (.bool (old == expected))) ⊢
      WP (Expr.cas (M := M) a expected desired) @ Stuckness.NotStuck; E {{ Φ }} :=
    wp_heapop (cas_op a expected desired) old

theorem wp_pure {e e' : Expr M} {E : CoPset} {Φ : Value → IProp GF}
    (red : ∀ m, Step M (e, m) [] (e', m, []))
    (det : ∀ {m obs next m' efs}, Step M (e, m) obs (next, m', efs) →
      obs = [] ∧ m' = m ∧ next = e' ∧ efs = []) :
    ▷ (WP e' @ Stuckness.NotStuck; E {{ Φ }}) ⊢ WP e @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro H
  iapply wp_lift_pure_det_step_no_fork (s := Stuckness.NotStuck) (e₁ := e) (e₂ := e')
    E (fun m => ⟨[], e', m, [], red m⟩) det
  iapply step_fupd_intro LawfulSet.subset_refl
  inext
  iintro _
  iexact H

theorem wp_bound (v : Value) (k : Value → Expr M) {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP (k v) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.bind (.ret v) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_pure (fun _ => Step.bound)
  intro m obs next m' efs hs
  cases hs with
  | bound => exact ⟨rfl, rfl, rfl, rfl⟩
  | bind h => cases h

theorem wp_returned (c : CPU) (k : CPU → Expr M) {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP (k c) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.native (.done c) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_pure (fun _ => Step.returned)
  intro m obs next m' efs hs
  cases hs with
  | returned => exact ⟨rfl, rfl, rfl, rfl⟩
  | native h => cases h

theorem wp_native_halt (c : CPU) (k : CPU → Expr M) (hc : c.pc = M.halt)
    {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP (Expr.native (.done c) k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.native (.run c) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_pure (fun _ => Step.native (SbrClient.Step.halt hc))
  intro m obs next m' efs hs
  cases hs with
  | native h =>
      cases h with
      | halt => exact ⟨rfl, rfl, rfl, rfl⟩
      | execute hn _ | fault hn _ => exact (hn hc).elim

theorem wp_native_exit (c : CPU) (k : CPU → Expr M) (hc : c.pc = M.halt)
    {E : CoPset} {Φ : Value → IProp GF} :
    (WP (k c) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.native (.run c) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro H
  iapply wp_native_halt c k hc
  inext
  iapply wp_returned c k
  inext
  iexact H

theorem wp_bind (e : Expr M) (k : Value → Expr M) {E : CoPset} {Φ : Value → IProp GF} :
    (WP e @ Stuckness.NotStuck; E {{ v, WP (k v) @ Stuckness.NotStuck; E {{ Φ }} }}) ⊢
      WP (Expr.bind e k) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro H
  iapply Iris.wp_bind (fun e => Expr.bind e k)
  iapply wp_wand $$ H
  iintro %v H
  iapply wp_bound v k
  inext
  iexact H

theorem wp_acquire_unfold (a : BitVec 64) (next : Expr M) {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP (Expr.bind (.cas a 0 1) (fun v => match v with
        | .bool true => next | .bool false => .acquire a next | _ => .fault))
        @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.acquire a next) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_pure (fun _ => Step.acquire)
  intro m obs e' m' efs hs
  cases hs
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem wp_claim_unfold (a : BitVec 64) (expected : UInt8) (next : Expr M)
    {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP (Expr.bind (.cas a expected 2) (fun v => match v with
        | .bool true => next | .bool false => .claim a expected next | _ => .fault))
        @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.claim a expected next) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_pure (fun _ => Step.claim)
  intro m obs e' m' efs hs
  cases hs
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem wp_await_unfold (a : BitVec 64) (expected : UInt8) (next : Expr M)
    {E : CoPset} {Φ : Value → IProp GF} :
    ▷ (WP (Expr.bind (.load a) (fun v => match v with
        | .byte b => if b == expected then next else .await a expected next | _ => .fault))
        @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.await a expected next) @ Stuckness.NotStuck; E {{ Φ }} := by
  apply wp_pure (fun _ => Step.await)
  intro m obs e' m' efs hs
  cases hs
  exact ⟨rfl, rfl, rfl, rfl⟩

end SbrClient.Host
