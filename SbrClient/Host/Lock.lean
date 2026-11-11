import SbrClient.Host.Rules
import Iris.Instances.Lib.Token
import Iris.Instances.Lib.Invariants
import Iris.Std.Namespaces

/-! A lock implemented by the host machine's atomic byte CAS and store.
The protected resource can include native decoder state or output buffers. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace SbrClient.Host.Lock
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {GF : BundledGFunctors} [TokenG GF]
section Predicates
variable [genHeapGS (BitVec 64) UInt8 GF ByteMap] [InvGS_gen hlc GF]
local bi (IProp GF)

def lockN : Namespace := ndot nroot "native-service-lock"

def lockInv (γ : GName) (a : BitVec 64) (R : IProp GF) : IProp GF := iprop%
  ∃ b : Bool, pointsTo a (DFrac.own 1) (if b then (1 : UInt8) else 0) ∗
    (if b then True else token γ ∗ R)

def isLock (γ : GName) (a : BitVec 64) (R : IProp GF) : IProp GF := inv lockN (lockInv γ a R)

instance isLock_persistent (γ : GName) (a : BitVec 64) (R : IProp GF) :
    Persistent (isLock γ a R) := by unfold isLock; infer_instance

end Predicates
local bi (IProp GF)

variable {M : Model} [MachineGS hlc M GF]

theorem init (M : Model) [MachineGS hlc M GF] (a : BitVec 64) (R : IProp GF) :
    letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    pointsTo a (DFrac.own 1) (0 : UInt8) ∗ R ⊢ |={⊤}=> ∃ γ, isLock γ a R := by
  letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨Ha, HR⟩
  imod token_alloc with ⟨%γ, Hγ⟩
  imod inv_alloc lockN ⊤ (lockInv γ a R) $$ [Ha HR Hγ] with H
  · inext
    unfold lockInv
    iexists false
    simp only [Bool.false_eq_true, ite_false]
    iframe
  imodintro
  iexists γ
  unfold isLock
  iexact H

theorem acquire (γ : GName) (a : BitVec 64) (R : IProp GF) (next : Host.Expr M)
    {Φ : Host.Value → IProp GF} :
    letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    isLock γ a R ∗ (token γ ∗ R -∗ WP next @ Stuckness.NotStuck; ⊤ {{ Φ }}) ⊢
      WP (Host.Expr.acquire a next) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, HK⟩
  iloeb as IH
  iapply wp_acquire_unfold
  inext
  iapply Host.wp_bind
  unfold isLock
  iinv Hlock with Hinv
  · exact ⟨fun _ _ => CoPset.mem_full, Language.stronglyAtomic_atomic inferInstance⟩
  unfold lockInv
  icases Hinv with ⟨%b, >Ha, HR⟩
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    iapply wp_cas a 0 0 1
    iframe Ha
    inext
    iintro Ha
    imodintro
    isplitl [Ha]
    · iexists true
      simp
      iframe Ha
    · simp
      iapply HK $$ HR
  · simp only [ite_true]
    iapply wp_cas a 1 0 1
    iframe Ha
    inext
    iintro Ha
    imodintro
    isplitl [Ha]
    · iexists true
      simp
      iframe Ha
    · simp
      iapply IH $$ HK

theorem release (γ : GName) (a : BitVec 64) (R : IProp GF)
    {Φ : Host.Value → IProp GF} :
    letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
    isLock γ a R ∗ token γ ∗ R ∗ Φ .unit ⊢
      WP (Host.Expr.store (M := M) a 0) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  letI := (hostIrisGS (hlc := hlc) (GF := GF) (M := M)).invGS
  iintro ⟨#Hlock, Hγ, HR, HΦ⟩
  unfold isLock
  iinv Hlock with Hinv
  · exact ⟨fun _ _ => CoPset.mem_full, Language.stronglyAtomic_atomic inferInstance⟩
  unfold lockInv
  icases Hinv with ⟨%b, >Ha, _⟩
  iapply wp_store a (if b then 1 else 0) 0
  iframe Ha
  inext
  iintro Ha
  imodintro
  isplitl [Ha Hγ HR]
  · iexists false
    simp only [Bool.false_eq_true, ite_false]
    iframe
  · iexact HΦ

end SbrClient.Host.Lock
