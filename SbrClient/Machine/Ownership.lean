import SbrClient.Machine.Language
import SbrClient.Machine.MapInstances
import SbrClient.Logic.CertifiedWP
import Iris.BI.Lib.GenHeap

noncomputable section
namespace SbrClient
open Iris Iris.BI Iris.Std Iris.Std.PartialMap Iris.ProofMode

abbrev ByteMap (V : Type) : Type := Std.ExtHashMap (BitVec 64) V

class MachineGS (hlc : outParam HasLC) (M : Model) (GF : BundledGFunctors) where
  [invGS : InvGS_gen hlc GF]
  heap : genHeapGS (BitVec 64) UInt8 GF ByteMap

attribute [reducible, instance] MachineGS.heap

instance machineIrisGS {hlc : HasLC} {M : Model} {GF : BundledGFunctors}
    [MachineGS hlc M GF] : Iris.IrisGS_gen hlc (Expr M) GF where
  invGS := MachineGS.invGS M
  stateInterp σ _ _ _ := genHeapInterp (H := ByteMap) σ
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := by
    letI := MachineGS.invGS (hlc := hlc) (M := M) (GF := GF)
    iintro H
    imodintro
    iexact H

section Owns
variable {GF : BundledGFunctors} [genHeapGS (BitVec 64) UInt8 GF ByteMap]
local bi (IProp GF)

def owns (p : Mem 64) : IProp GF := Iris.BI.bigSepM (M := ByteMap) (fun k v => pointsTo k (DFrac.own 1) v) p

theorem owns_valid (σ p : Mem 64) :
    genHeapInterp (H := ByteMap) σ ∗ owns p ==∗ ⌜PartialMap.submap (M := ByteMap) p σ⌝ := by
  unfold owns
  induction p using (LawfulFiniteMap.induction_on (M := ByteMap)) with
  | hemp =>
    iintro -
    imodintro
    ipureintro
    exact LawfulPartialMap.empty_subset (M := ByteMap) σ
  | hins l v p hl ih =>
    iintro ⟨Hσ, Hp⟩
    icases (BigSepM.bigSepM_insert (M := ByteMap) (x := v)
      (Φ := fun k v => pointsTo k (DFrac.own 1) v) hl).1 $$ Hp with ⟨Hl, Hp⟩
    ihave %hv : ⌜get? (M := ByteMap) σ l = some v⌝ $$ [Hσ Hl]
    · icases genHeap_valid $$ [$Hσ $Hl] with >%hv
      itrivial
    ihave %hsub : ⌜PartialMap.submap (M := ByteMap) p σ⌝ $$ [Hσ Hp]
    · icases ih $$ [$Hσ $Hp] with >%hsub
      itrivial
    imodintro
    ipureintro
    intro k x hk
    rw [LawfulPartialMap.get?_insert] at hk
    split at hk
    · next heq => subst heq; cases hk; exact hv
    · exact hsub k x hk

private theorem union_empty (m : Mem 64) : m.union ∅ = m := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]

private theorem union_insert (m w : Mem 64) (k : BitVec 64) (v : UInt8) :
    m.union (insert (M := ByteMap) w k v) = insert (M := ByteMap) (m.union w) k v := by
  apply Std.ExtHashMap.ext_getElem?
  intro a
  simp only [Iris.Std.insert, Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union,
    Std.ExtHashMap.getElem?_insert]
  split <;> rfl

/-- Replace mapped bytes without allocating or deleting locations. -/
theorem owns_write (w p σ : Mem 64)
    (hw : ∀ k v, get? (M := ByteMap) w k = some v → (get? (M := ByteMap) p k).isSome = true) :
    genHeapInterp (H := ByteMap) σ ∗ owns p ==∗ genHeapInterp (H := ByteMap) (σ.union w) ∗ owns (p.union w) := by
  induction w using (LawfulFiniteMap.induction_on (M := ByteMap)) with
  | hemp =>
    rw [union_empty, union_empty]
    iintro H
    iexact H
  | hins l v w hl ih =>
    have hw' : ∀ k v, get? (M := ByteMap) w k = some v → (get? (M := ByteMap) p k).isSome = true := by
      intro k x hk
      by_cases heq : k = l
      · subst k
        rw [hl] at hk
        cases hk
      · exact hw k x (by simpa [LawfulPartialMap.get?_insert, heq, Ne.symm heq] using hk)
    have hp : (get? (M := ByteMap) p l).isSome = true := hw l v (LawfulPartialMap.get?_insert_eq rfl)
    cases hh : get? (M := ByteMap) p l with
    | none => simp only [hh, Option.isSome_none, Bool.false_eq_true] at hp
    | some x =>
      rw [union_insert, union_insert]
      iintro H
      imod ih hw' $$ H with ⟨Hσ, Hp⟩
      have hwp : get? (M := ByteMap) (p.union w) l = some x := by
        change (p.union w)[l]? = some x
        simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
        change w[l]? = none at hl
        change p[l]? = some x at hh
        rw [hl, hh]
        rfl
      unfold owns
      icases BigSepM.bigSepM_insert_acc hwp $$ Hp with ⟨Hl, Hp⟩
      imod genHeap_update (v₂ := v) $$ [$Hσ $Hl] with ⟨Hσ, Hl⟩
      iframe Hσ
      iapply Hp $$ Hl

end Owns

private theorem submap_agrees {p σ : Mem 64} (h : PartialMap.submap (M := ByteMap) p σ) : Agrees p σ := by
  refine ⟨σ.diff p, ?_, ?_⟩
  · simp only [Disjoint, Std.ExtHashMap.eq_empty_iff_forall_not_mem,
      Std.ExtHashMap.inter_eq, Std.ExtHashMap.mem_inter_iff,
      Std.ExtHashMap.diff_eq, Std.ExtHashMap.mem_diff_iff]
    intro k hk
    exact hk.2.2 hk.1
  · apply Std.ExtHashMap.ext_getElem?
    intro k
    rw [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
    have hdiff : (σ.diff p)[k]? = if k ∈ p then none else σ[k]? :=
      Std.ExtHashMap.get?_diff
    rw [hdiff]
    cases hp : p[k]? with
    | none =>
      have hk : ¬ k ∈ p := by
        simp only [Std.ExtHashMap.mem_iff_isSome_getElem?, hp, Option.isSome_none,
          Bool.false_eq_true, not_false_eq_true]
      rw [ite_eq_right hk]
      simp only [Option.or_none]
    | some b =>
      have hs := h k b hp
      change σ[k]? = some b at hs
      have hk : k ∈ p := Std.ExtHashMap.mem_iff_isSome_getElem?.mpr (by simp only [hp]; rfl)
      rw [ite_eq_left hk]
      simpa only [Option.none_or, hp] using hs

private theorem domain_none {p p' : Mem 64} (h : SameDomain p p') {k : BitVec 64}
    (hp : p'[k]? = none) : p[k]? = none := by
  apply Std.ExtHashMap.getElem?_eq_none
  intro hm
  have hm' := (h k).mpr hm
  simp only [Std.ExtHashMap.mem_iff_isSome_getElem?, hp, Option.isSome_none,
    Bool.false_eq_true] at hm'

private theorem full_overlay {p p' : Mem 64} (h : SameDomain p p') : p.union p' = p' := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases hp : p'[k]? with
  | none => simp [domain_none h hp]
  | some b => rfl

private theorem replace_frame {p p' f : Mem 64} (h : SameDomain p p')
    (hd : Disjoint p' f) : (p.union f).union p' = p'.union f := by
  apply Std.ExtHashMap.ext_getElem?
  intro k
  simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases hp : p'[k]? with
  | none => simp [domain_none h hp]
  | some b =>
    have hf : f[k]? = none := by
      apply Std.ExtHashMap.getElem?_eq_none
      intro hf
      have hm : k ∈ p' := Std.ExtHashMap.mem_iff_isSome_getElem?.mpr (by simp [hp])
      have hi : k ∈ p'.inter f := Std.ExtHashMap.mem_inter_iff.mpr ⟨hm, hf⟩
      rw [show p'.inter f = ∅ from hd] at hi
      exact Std.ExtHashMap.not_mem_empty hi
    simp [hf]

section World
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

theorem owns_agrees (p σ : Mem 64) :
    owns p ∗ genHeapInterp (H := ByteMap) σ ==∗ ⌜Agrees p σ⌝ := by
  iintro ⟨Hp, Hσ⟩
  imod owns_valid σ p $$ [$Hσ $Hp] with %h
  ipureintro
  exact submap_agrees h

theorem owns_change {p σ p' σ' : Mem 64} (h : Change p σ p' σ') :
    owns p ∗ genHeapInterp (H := ByteMap) σ ==∗ owns p' ∗ genHeapInterp (H := ByteMap) σ' := by
  obtain ⟨f, hd, rfl, hd', rfl, hdom⟩ := h
  have hw : ∀ k v, get? (M := ByteMap) p' k = some v → (get? (M := ByteMap) p k).isSome = true := by
    intro k v hv
    change p'[k]? = some v at hv
    have hm : k ∈ p' := Std.ExtHashMap.mem_iff_isSome_getElem?.mpr (by simp [hv])
    exact Std.ExtHashMap.mem_iff_isSome_getElem?.mp ((hdom k).mp hm)
  iintro ⟨Hp, Hσ⟩
  imod owns_write p' p (p.union f) hw $$ [$Hσ $Hp] with ⟨Hσ, Hp⟩
  rw [full_overlay hdom]
  rw [replace_frame hdom hd']
  iframe

def machineWorld : BinaryCert.World (Expr := Expr M) (GF := GF) (Mem 64) where
  step := LocalStep M
  owns := owns
  agrees := Agrees
  change := Change
  valid p σ _ _ _ := owns_agrees p σ
  progress := local_progress
  simulate := local_simulate
  update h _ _ _ := owns_change h
  zero_laters _ := rfl

end World
end SbrClient
