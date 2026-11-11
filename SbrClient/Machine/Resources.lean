import SbrClient.Machine.Ownership

noncomputable section
namespace SbrClient
open Iris Iris.BI Iris.Std Iris.ProofMode

private theorem disjoint_iris {p q : Mem 64} (h : Disjoint p q) :
    PartialMap.disjoint (M := ByteMap) p q := by
  intro k ⟨hp, hq⟩
  have hp' : k ∈ p := Std.ExtHashMap.mem_iff_isSome_getElem?.mpr hp
  have hq' : k ∈ q := Std.ExtHashMap.mem_iff_isSome_getElem?.mpr hq
  have hi : k ∈ p.inter q := Std.ExtHashMap.mem_inter_iff.mpr ⟨hp', hq'⟩
  rw [show p.inter q = ∅ from h] at hi
  exact Std.ExtHashMap.not_mem_empty hi

private theorem union_as_iris {p q : Mem 64} (h : Disjoint p q) :
    p.union q = PartialMap.union (M := ByteMap) p q := by
  rw [Std.ExtHashMap.union_comm_of_disjoint p q h]
  apply Std.ExtHashMap.ext_getElem?
  intro k
  change (q.union p)[k]? = get? (M := ByteMap) (PartialMap.union p q) k
  simp only [PartialMap.union, LawfulPartialMap.get?_merge]
  change (q.union p)[k]? = Option.merge (fun v _ => v) p[k]? q[k]?
  rw [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  cases p[k]? <;> cases q[k]? <;> rfl

variable {GF : BundledGFunctors} [genHeapGS (BitVec 64) UInt8 GF ByteMap]
local bi (IProp GF)

theorem owns_union {p q : Mem 64} (h : Disjoint p q) :
    owns (GF := GF) (p.union q) ⊣⊢ owns p ∗ owns q := by
  rw [union_as_iris h]
  exact BigSepM.bigSepM_union (M := ByteMap) (disjoint_iris h)

theorem owns_disjoint (p q : Mem 64) :
    owns (GF := GF) p ∗ owns q ⊢ ⌜Disjoint p q⌝ := by
  classical
  by_cases hd : Disjoint p q
  · iintro -
    ipureintro
    exact hd
  · have hex : ∃ k, k ∈ p.inter q := by
      apply Classical.byContradiction
      intro hn
      apply hd
      apply Std.ExtHashMap.eq_empty_iff_forall_not_mem.mpr
      intro k hk
      exact hn ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hex
    obtain ⟨hp, hq⟩ := Std.ExtHashMap.mem_inter_iff.mp hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Std.ExtHashMap.mem_iff_isSome_getElem?.mp hp)
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (Std.ExtHashMap.mem_iff_isSome_getElem?.mp hq)
    unfold owns
    iintro ⟨Hp, Hq⟩
    ihave Hkp := BigSepM.bigSepM_lookup (M := ByteMap)
      (Φ := fun k v => pointsTo k (DFrac.own 1) v) hv $$ Hp
    ihave Hkq := BigSepM.bigSepM_lookup (M := ByteMap)
      (Φ := fun k v => pointsTo k (DFrac.own 1) v) hw $$ Hq
    ihave %hne := pointsTo_ne $$ Hkp Hkq
    exact (hne rfl).elim

/-- Interpret an externally verified memory predicate with actual Iris byte
ownership. The predicate itself remains a pure Kraken proposition. -/
def ownsPred (P : Mem 64 → Prop) : IProp GF := iprop% ∃ p, ⌜P p⌝ ∗ owns p

theorem ownsPred_mono {P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) :
    ownsPred (GF := GF) P ⊢ ownsPred Q := by
  unfold ownsPred
  iintro ⟨%p, %hp, Hp⟩
  iexists p
  iframe Hp
  ipureintro
  exact h p hp

/-- A Kraken separating conjunction returns independently transferable Iris
resources, including the two output buffers and the reusable decoder state. -/
theorem ownsPred_sep {P Q : Mem 64 → Prop} :
    ownsPred (GF := GF) (Std.ExtHashMap.sep P Q) ⊢ ownsPred P ∗ ownsPred Q := by
  unfold ownsPred
  iintro ⟨%m, %hm, Hm⟩
  obtain ⟨p, q, rfl, hd, hp, hq⟩ := hm
  icases (owns_union hd).1 $$ Hm with ⟨Hp, Hq⟩
  isplitl [Hp]
  · iexists p
    iframe Hp
    itrivial
  · iexists q
    iframe Hq
    itrivial

theorem ownsPred_sep_intro {P Q : Mem 64 → Prop} :
    ownsPred (GF := GF) P ∗ ownsPred Q ⊢ ownsPred (Std.ExtHashMap.sep P Q) := by
  unfold ownsPred
  iintro ⟨⟨%p, %hp, Hp⟩, ⟨%q, %hq, Hq⟩⟩
  ihave %hd : ⌜Disjoint p q⌝ $$ [Hp Hq]
  · iapply owns_disjoint p q $$ [$Hp $Hq]
  iexists p.union q
  isplitr
  · ipureintro
    exact ⟨p, q, rfl, hd, hp, hq⟩
  · iapply (owns_union hd).2 $$ [$Hp $Hq]


end SbrClient
