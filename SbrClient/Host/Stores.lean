import SbrClient.Host.Rules
import SbrClient.Machine.Resources

/-! Explicit host initialization of native-call memory. Each byte write is a
separate physical host step; this is used to reinstall the eight-byte return
address before reusing a native call stack. -/
namespace SbrClient.Host
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

def writePairs (xs : List (BitVec 64 × UInt8)) : Expr M :=
  match xs with
  | [] => .ret .unit
  | (a, v) :: xs => .bind (.store a v) (fun _ => writePairs xs)

def written (xs : List (BitVec 64 × UInt8)) (m : Mem 64) : Mem 64 :=
  xs.foldl (fun m p => Std.ExtHashMap.insert m p.1 p.2) m

def writeBytes (a : BitVec 64) (bs : List UInt8) : Expr M :=
  writePairs (bs.mapIdx (fun i b => (a + BitVec.ofNat 64 i, b)))

theorem wp_store_owned {p : Mem 64} {a : BitVec 64} {old v : UInt8}
    (h : p[a]? = some old) {E : CoPset} {Φ : Value → IProp GF} :
    owns p ∗ ▷ (owns (p.insert a v) -∗ Φ .unit) ⊢
      WP (Expr.store (M := M) a v) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold owns
  iintro ⟨Hp, HK⟩
  icases BigSepM.bigSepM_insert_acc (M := ByteMap)
    (Φ := fun k v => pointsTo k (DFrac.own 1) v) h $$ Hp with ⟨Ha, Hrestore⟩
  iapply wp_store a old v
  iframe Ha
  inext
  iintro Ha
  iapply HK
  iapply Hrestore $$ %v Ha

theorem wp_writePairs (xs : List (BitVec 64 × UInt8)) (p : Mem 64)
    (hm : ∀ a v, (a, v) ∈ xs → a ∈ p)
    {E : CoPset} {Φ : Value → IProp GF} :
    owns p ∗ (owns (written xs p) -∗ Φ .unit) ⊢
      WP (writePairs (M := M) xs) @ Stuckness.NotStuck; E {{ Φ }} := by
  induction xs generalizing p with
  | nil =>
      simp only [writePairs, written, List.foldl_nil]
      iintro ⟨Hp, HK⟩
      iapply Iris.wp_value' (v := Value.unit)
      iapply HK $$ Hp
  | cons av xs ih =>
      obtain ⟨a, v⟩ := av
      have ha : a ∈ p := hm a v (by simp)
      have htail : ∀ b w, (b, w) ∈ xs → b ∈ p.insert a v := by
        intro b w hb
        exact Std.ExtHashMap.mem_insert.mpr (.inr (hm b w (by simp [hb])))
      obtain ⟨old, hold⟩ := Option.isSome_iff_exists.mp
        (Std.ExtHashMap.mem_iff_isSome_getElem?.mp ha)
      simp only [writePairs, written, List.foldl_cons] at *
      iintro ⟨Hp, HK⟩
      iapply wp_bind
      iapply wp_store_owned hold
      iframe Hp
      inext
      iintro Hp
      iapply ih (p.insert a v) htail
      iframe Hp
      iexact HK

private theorem written_union (xs : List (BitVec 64 × UInt8)) (p q : Mem 64) :
    written xs (p.union q) = p.union (written xs q) := by
  induction xs generalizing q with
  | nil => rfl
  | cons av xs ih =>
      unfold written at *
      simp only [List.foldl_cons]
      have hu : (p.union q).insert av.1 av.2 = p.union (q.insert av.1 av.2) := by
        apply Std.ExtHashMap.ext_getElem?
        intro k
        simp only [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union,
          Std.ExtHashMap.getElem?_insert]
        split <;> simp_all
      rw [hu]
      exact ih _

theorem written_eq_storeBytes (a : BitVec 64) (bs : List UInt8) (p : Mem 64) :
    written (bs.mapIdx (fun i b => (a + BitVec.ofNat 64 i, b))) p = p.storeBytes a bs := by
  unfold Mem.storeBytes List.At
  rw [Std.ExtHashMap.ofList_eq_foldl]
  have hpempty : p.union ∅ = p := by
    apply Std.ExtHashMap.ext_getElem?
    intro k
    simp [Std.ExtHashMap.union_eq, Std.ExtHashMap.getElem?_union]
  simpa only [hpempty, written] using
    written_union (bs.mapIdx (fun i b => (a + BitVec.ofNat 64 i, b))) p ∅

theorem wp_writeBytes (a : BitVec 64) (bs : List UInt8) (p : Mem 64)
    (hm : ∀ i, i < bs.length → a + BitVec.ofNat 64 i ∈ p)
    {E : CoPset} {Φ : Value → IProp GF} :
    owns p ∗ (owns (p.storeBytes a bs) -∗ Φ .unit) ⊢
      WP (writeBytes (M := M) a bs) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold writeBytes
  rw [← written_eq_storeBytes]
  apply wp_writePairs
  intro k v hv
  simp only [List.mem_mapIdx] at hv
  obtain ⟨i, hi, heq⟩ := hv
  cases heq
  exact hm i hi

/-- Overwriting an owned block initializes its bytes, with no allocation and
no assumption about its former contents. -/
theorem wp_initializeBlock (a : BitVec 64) (bs : List UInt8)
    {E : CoPset} {Φ : Value → IProp GF} :
    ownsPred (Mem.Block a bs.length) ∗
      (ownsPred (Eq (bs.At a)) -∗ Φ .unit) ⊢
      WP (writeBytes (M := M) a bs) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold ownsPred
  iintro ⟨⟨%p, %hp, Hp⟩, HK⟩
  obtain ⟨hw, old, hlen, rfl⟩ := hp
  iapply wp_writeBytes a bs (old.At a)
  · intro i hi
    apply (mem_At_iff old a _).mpr
    exact ⟨i, by omega, rfl⟩
  iframe Hp
  iintro Hp
  iapply HK
  iexists (Mem.storeBytes (old.At a) a bs)
  iframe Hp
  ipureintro
  have hs := Mem.storeBytes_sep a bs.length old bs Std.ExtHashMap.emp (old.At a)
    ⟨by simpa only [Std.ExtHashMap.sep_emp], hlen, rfl⟩
  simpa only [Std.ExtHashMap.sep_emp] using hs

end SbrClient.Host
