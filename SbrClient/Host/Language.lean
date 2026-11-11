import SbrClient.Machine.Ownership
import SbrClient.Machine.Adapter

/-! An explicit host/FFI machine. A native call takes one Kraken instruction
per physical step; other threads may run between instructions. Host loads,
stores and compare/exchanges are atomic byte operations on the SAME heap.
The host controller is a modeled high-level runtime, not claimed verified
x86 machine code. -/
namespace SbrClient.Host
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std

inductive Value where
  | unit
  | byte (v : UInt8)
  | bool (v : Bool)

inductive Expr (M : Model) where
  | ret (v : Value)
  | bind (e : Expr M) (k : Value → Expr M)
  | native (e : SbrClient.Expr M) (k : CPU → Expr M)
  | load (a : BitVec 64)
  | store (a : BitVec 64) (v : UInt8)
  | cas (a : BitVec 64) (expected desired : UInt8)
  | acquire (a : BitVec 64) (next : Expr M)
  | claim (a : BitVec 64) (expected : UInt8) (next : Expr M)
  | await (a : BitVec 64) (expected : UInt8) (next : Expr M)
  | fork (child : Expr M)
  | fault

def Expr.toVal {M : Model} : Expr M → Option Value
  | .ret v => some v
  | _ => none

inductive Step (M : Model) : Expr M × Mem 64 → List Empty → Expr M × Mem 64 × List (Expr M) → Prop
  | bind {e e' k m m' obs efs} (h : Step M (e, m) obs (e', m', efs)) :
      Step M (.bind e k, m) obs (.bind e' k, m', efs)
  | bound {v k m} : Step M (.bind (.ret v) k, m) [] (k v, m, [])
  | native {e e' k m m'} (h : SbrClient.Step M (e, m) [] (e', m', [])) :
      Step M (.native e k, m) [] (.native e' k, m', [])
  | returned {c k m} : Step M (.native (.done c) k, m) [] (k c, m, [])
  | load {a m v} (h : m[a]? = some v) : Step M (.load a, m) [] (.ret (.byte v), m, [])
  | store {a v m old} (h : m[a]? = some old) :
      Step M (.store a v, m) [] (.ret .unit, m.insert a v, [])
  | cas {a expected desired m old} (h : m[a]? = some old) :
      Step M (.cas a expected desired, m) []
        (.ret (.bool (old == expected)), if old == expected then m.insert a desired else m, [])
  | acquire {a next m} : Step M (.acquire a next, m) []
      (.bind (.cas a 0 1) (fun v => match v with
        | .bool true => next | .bool false => .acquire a next | _ => .fault), m, [])
  | claim {a expected next m} : Step M (.claim a expected next, m) []
      (.bind (.cas a expected 2) (fun v => match v with
        | .bool true => next | .bool false => .claim a expected next | _ => .fault), m, [])
  | await {a expected next m} : Step M (.await a expected next, m) []
      (.bind (.load a) (fun v => match v with
        | .byte b => if b == expected then next else .await a expected next
        | _ => .fault), m, [])
  | fork {child m} : Step M (.fork child, m) [] (.ret .unit, m, [child])

instance (M : Model) : Language (Expr M) (Mem 64) Empty Value where
  toVal := Expr.toVal
  ofVal := .ret
  coe_of_toVal_eq_some := by
    intro e v h
    cases e <;> cases h
    rfl
  toVal_coe _ := rfl
  primStep := Step M
  val_stuck h := by cases h <;> rfl

instance bind_context {M : Model} (k : Value → Expr M) : Language.Context (fun e => Expr.bind e k) where
  toVal_eq_none_fill _ := rfl
  primStep_fill := Step.bind
  primStep_fill_inv hn hs := by
    cases hs with
    | bind h => exact ⟨_, rfl, h⟩
    | bound => cases hn

instance load_atomic {M : Model} (a : BitVec 64) : Language.Atomic .StronglyAtomic (Expr.load (M := M) a) where
  atomic h := by cases h; rfl

instance store_atomic {M : Model} (a : BitVec 64) (v : UInt8) : Language.Atomic .StronglyAtomic (Expr.store (M := M) a v) where
  atomic h := by cases h; rfl

instance cas_atomic {M : Model} (a : BitVec 64) (expected desired : UInt8) :
    Language.Atomic .StronglyAtomic (Expr.cas (M := M) a expected desired) where
  atomic h := by cases h; rfl

noncomputable instance hostIrisGS {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
    [MachineGS hlc M GF] : IrisGS_gen hlc (Expr M) GF where
  invGS := MachineGS.invGS M
  stateInterp σ _ _ _ := genHeapInterp (H := ByteMap) σ
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by
    letI := MachineGS.invGS (hlc := hlc) M (GF := GF)
    iintro H
    imodintro
    iexact H

/-- Certificates cover native instruction execution. Host operations use
ordinary Iris lifting, so they need no certificate producer. -/
inductive LocalStep (M : Model) : Expr M × Mem 64 → Expr M × Mem 64 → Prop
  | native {e e' k p p'} (h : SbrClient.LocalStep M (e, p) (e', p')) :
      LocalStep M (.native e k, p) (.native e' k, p')

theorem local_progress {M : Model} {e : Expr M} {p σ : Mem 64}
    (ha : Agrees p σ) (hl : ∃ c, LocalStep M (e, p) c) :
    PrimStep.Reducible (e, σ) := by
  obtain ⟨_, hl⟩ := hl
  cases hl with
  | native h =>
      obtain ⟨obs, e', σ', efs, hs⟩ := SbrClient.local_progress ha ⟨_, h⟩
      have hquiet : obs = [] ∧ efs = [] := by cases hs <;> exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := hquiet
      exact ⟨[], _, σ', [], Step.native hs⟩

theorem local_simulate {M : Model} {e e' : Expr M} {p σ σ' : Mem 64}
    {obs : List Empty} {efs : List (Expr M)}
    (ha : Agrees p σ) (hl : ∃ c, LocalStep M (e, p) c)
    (hs : Step M (e, σ) obs (e', σ', efs)) :
    obs = [] ∧ efs = [] ∧ ∃ p', LocalStep M (e, p) (e', p') ∧ Change p σ p' σ' := by
  obtain ⟨_, hl⟩ := hl
  cases hl with
  | native hlocal =>
      cases hs with
      | native hreal =>
          obtain ⟨_, _, p', hstep, hc⟩ := SbrClient.local_simulate ha ⟨_, hlocal⟩ hreal
          exact ⟨rfl, rfl, p', .native hstep, hc⟩
      | returned => cases hlocal

noncomputable def world {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
    [MachineGS hlc M GF] : BinaryCert.World (Expr := Expr M) (GF := GF) (Mem 64) where
  step := LocalStep M
  owns := SbrClient.owns
  agrees := Agrees
  change := Change
  valid p σ _ _ _ := owns_agrees p σ
  progress := local_progress
  simulate := local_simulate
  update h _ _ _ := owns_change h
  zero_laters _ := rfl

/-- A cut retains the exact host continuation passed at the FFI entry. -/
def cut {M : Model} (k : CPU → Expr M) (Q : SbrClient.Expr M → Mem 64 → Prop)
    (e : Expr M) (p : Mem 64) : Prop := ∃ x, e = .native x k ∧ Q x p

section Certificate
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

theorem lift_safeN (n : Nat) (e : SbrClient.Expr M) (p : Mem 64)
    (Q : SbrClient.Expr M → Mem 64 → Prop) (k : CPU → Expr M)
    (h : BinaryCert.SafeN (machineWorld (M := M) (GF := GF)) Q n e p) :
    BinaryCert.SafeN (world (M := M) (GF := GF)) (cut k Q) n (.native e k) p := by
  induction n generalizing e p with
  | zero => trivial
  | succ n ih =>
      rcases h with h | ⟨_, ⟨⟨e', p'⟩, hs⟩, hk⟩
      · exact .inl ⟨e, rfl, h⟩
      · right
        refine ⟨rfl, ⟨(.native e' k, p'), LocalStep.native hs⟩, ?_⟩
        intro next pnext hs'
        cases hs' with
        | native hlocal => exact ih _ _ (hk _ _ hlocal)

theorem lift_certificate {e p Q} (k : CPU → Expr M)
    (h : BinaryCert.Certificate (machineWorld (M := M) (GF := GF)) e p Q) :
    BinaryCert.Certificate (world (M := M) (GF := GF)) (.native e k) p (cut k Q) :=
  fun n => lift_safeN n e p Q k (h n)

theorem wp_native_certificate {e p Q} (k : CPU → Expr M) {E : CoPset} {Φ : Value → IProp GF}
    (h : BinaryCert.Certificate (machineWorld (M := M) (GF := GF)) e p Q) (hq : ¬ Q e p) :
    SbrClient.owns p ∗ ▷ (∀ x p', ⌜Q x p'⌝ -∗ SbrClient.owns p' -∗
      WP (Expr.native x k) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Expr.native e k) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨Hp, HK⟩
  iapply BinaryCert.wp_certificate (world (M := M)) (lift_certificate k h) (Q := cut k Q)
  · rintro ⟨x, hx, hQ⟩
    cases hx
    exact hq hQ
  simp only [show (world (M := M) (GF := GF)).owns = SbrClient.owns from rfl]
  iframe Hp
  inext
  iintro %next %p' %hcut Hp
  obtain ⟨x, rfl, hQ⟩ := hcut
  iapply HK $$ %x %p' %hQ Hp

end Certificate
end SbrClient.Host
