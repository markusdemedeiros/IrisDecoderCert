import SbrClient.Host.Lock

/-! A one-slot ownership mailbox. Flag 0 makes the free resource available;
flag 1 makes the ready resource available; flag 2 means a worker owns the
resource. Both producer and consumer claim with CAS before touching it. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SbrClient.Host.Mailbox
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std

def code : Option Bool → UInt8
  | none => 2
  | some false => 0
  | some true => 1

theorem code_injective : Function.Injective code := by
  intro p q h
  cases p with
  | none => cases q with
    | none => rfl
    | some b => cases b <;> cases h
  | some b => cases q with
    | none => cases b <;> cases h
    | some c => cases b <;> cases c <;> cases h <;> rfl

def mailboxN : Namespace := ndot nroot "native-output-mailbox"

variable {hlc : HasLC} {GF : BundledGFunctors} [TokenG GF]
local bi (IProp GF)

section Predicates
variable [genHeapGS (BitVec 64) UInt8 GF ByteMap] [InvGS_gen hlc GF]

def slotInv (γ : GName) (a : BitVec 64) (R : Bool → IProp GF) : IProp GF := iprop%
  ∃ p : Option Bool, pointsTo a (DFrac.own 1) (code p) ∗
    (match p with | none => True | some b => token γ ∗ R b)

def isMailbox (γ : GName) (a : BitVec 64) (R : Bool → IProp GF) : IProp GF :=
  inv mailboxN (slotInv γ a R)

instance isMailbox_persistent (γ : GName) (a : BitVec 64) (R : Bool → IProp GF) :
    Persistent (isMailbox γ a R) := by unfold isMailbox; infer_instance
end Predicates

variable {M : Model} [MachineGS hlc M GF]

theorem init (M : Model) [MachineGS hlc M GF] (a : BitVec 64) (R : Bool → IProp GF) :
    letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    pointsTo a (DFrac.own 1) (0 : UInt8) ∗ R false ⊢
      |={⊤}=> ∃ γ, isMailbox γ a R := by
  letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨Ha, HR⟩
  imod token_alloc with ⟨%γ, Hγ⟩
  imod inv_alloc mailboxN ⊤ (slotInv γ a R) $$ [Ha HR Hγ] with H
  · inext
    unfold slotInv
    iexists (some false)
    simp only [code]
    iframe
  imodintro
  iexists γ
  unfold isMailbox
  iexact H

/-- Claim either the free (false) or ready (true) resource. The flag remains
busy until its exclusive owner explicitly publishes a resource. -/
theorem claim (γ : GName) (a : BitVec 64) (R : Bool → IProp GF) (b : Bool)
    (next : Host.Expr M) {Φ : Host.Value → IProp GF} :
    letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    isMailbox γ a R ∗ (token γ ∗ R b -∗ WP next @ Stuckness.NotStuck; ⊤ {{ Φ }}) ⊢
      WP (Host.Expr.claim a (code (some b)) next) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hslot, HK⟩
  iloeb as IH
  iapply wp_claim_unfold
  inext
  iapply Host.wp_bind
  unfold isMailbox
  iinv Hslot with Hinv
  · exact ⟨fun _ _ => CoPset.mem_full, Language.stronglyAtomic_atomic inferInstance⟩
  unfold slotInv
  icases Hinv with ⟨%p, >Ha, HR⟩
  by_cases hp : p = some b
  · subst p
    iapply wp_cas a (code (some b)) (code (some b)) 2
    iframe Ha
    inext
    iintro Ha
    imodintro
    isplitl [Ha]
    · iexists (none : Option Bool)
      simp [code]
      iframe Ha
    · simp
      iapply HK $$ HR
  · have hc : code p ≠ code (some b) := fun h => hp (code_injective h)
    iapply wp_cas a (code p) (code (some b)) 2
    iframe Ha
    inext
    iintro Ha
    imodintro
    isplitl [Ha HR]
    · iexists p
      simp [beq_false_of_ne hc]
      iframe
    · simp only [beq_false_of_ne hc]
      iapply IH $$ HK

/-- Publish ready output (true), or return free buffers after consuming them
(false). The exclusive token prevents either role from publishing twice. -/
theorem publish (γ : GName) (a : BitVec 64) (R : Bool → IProp GF) (b : Bool)
    {Φ : Host.Value → IProp GF} :
    letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    isMailbox γ a R ∗ token γ ∗ R b ∗ Φ .unit ⊢
      WP (Host.Expr.store (M := M) a (code (some b))) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hslot, Hγ, HR, HΦ⟩
  unfold isMailbox
  iinv Hslot with Hinv
  · exact ⟨fun _ _ => CoPset.mem_full, Language.stronglyAtomic_atomic inferInstance⟩
  unfold slotInv
  icases Hinv with ⟨%p, >Ha, _⟩
  iapply wp_store a (code p) (code (some b))
  iframe Ha
  inext
  iintro Ha
  imodintro
  isplitl [Ha Hγ HR]
  · iexists (some b)
    simp
    iframe
  · iexact HΦ

end SbrClient.Host.Mailbox
