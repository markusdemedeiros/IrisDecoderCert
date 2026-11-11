import SbrClient.Host.Rules
import SbrClient.Machine.Resources

/-! A real host consumer reads every byte of an owned output block and
computes an XOR checksum. The checksum is related to the bytes actually
owned/read, with no assumption about FFmpeg's audio-level output values. -/
namespace SbrClient.Host
open Kraken Iris Iris.ProgramLogic Iris.BI Iris.ProofMode Iris.Std
variable {hlc : HasLC} {M : Model} {GF : BundledGFunctors} [MachineGS hlc M GF]
local bi (IProp GF)

def scan (xs : List (BitVec 64)) (acc : UInt8) : Expr M :=
  match xs with
  | [] => .ret (.byte acc)
  | a :: xs => .bind (.load a) (fun v => match v with
      | .byte b => scan xs (acc ^^^ b)
      | _ => .fault)

def scanValue (xs : List (BitVec 64)) (p : Mem 64) (acc : UInt8) : UInt8 :=
  xs.foldl (fun acc a => acc ^^^ p[a]?.getD 0) acc

def addresses (a : BitVec 64) (n : Nat) : List (BitVec 64) :=
  (List.range n).map (fun i => a + BitVec.ofNat 64 i)

def scanBlock (a : BitVec 64) (n : Nat) (acc : UInt8 := 0) : Expr M := scan (addresses a n) acc

theorem wp_load_owned {p : Mem 64} {a : BitVec 64} {v : UInt8}
    (h : p[a]? = some v) {E : CoPset} {Φ : Value → IProp GF} :
    owns p ∗ ▷ (owns p -∗ Φ (.byte v)) ⊢
      WP (Expr.load (M := M) a) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold owns
  iintro ⟨Hp, HK⟩
  icases BigSepM.bigSepM_lookup_acc (M := ByteMap)
    (Φ := fun k v => pointsTo k (DFrac.own 1) v) h $$ Hp with ⟨Ha, Hrestore⟩
  iapply wp_load a v
  iframe Ha
  inext
  iintro Ha
  iapply HK
  iapply Hrestore $$ Ha

theorem wp_scan (xs : List (BitVec 64)) (p : Mem 64) (acc : UInt8)
    (hm : ∀ a, a ∈ xs → a ∈ p)
    {E : CoPset} {Φ : Value → IProp GF} :
    owns p ∗ (owns p -∗ Φ (.byte (scanValue xs p acc))) ⊢
      WP (scan (M := M) xs acc) @ Stuckness.NotStuck; E {{ Φ }} := by
  induction xs generalizing acc with
  | nil =>
      simp only [scan, scanValue, List.foldl_nil]
      iintro ⟨Hp, HK⟩
      iapply Iris.wp_value' (v := Value.byte acc)
      iapply HK $$ Hp
  | cons a xs ih =>
      have ha := hm a (by simp)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp
        (Std.ExtHashMap.mem_iff_isSome_getElem?.mp ha)
      have ht : ∀ b, b ∈ xs → b ∈ p := fun b hb => hm b (by simp [hb])
      simp only [scan, scanValue, List.foldl_cons, hv, Option.getD_some] at ih ⊢
      iintro ⟨Hp, HK⟩
      iapply wp_bind
      iapply wp_load_owned hv
      iframe Hp
      inext
      iintro Hp
      iapply ih (acc ^^^ v) ht
      iframe Hp
      iexact HK

/-- Every byte is read, and the same block ownership is returned together
with the checksum of its exact pre-call memory. -/
theorem wp_scanBlock (a : BitVec 64) (n : Nat) (acc : UInt8)
    {E : CoPset} {Φ : Value → IProp GF} :
    ownsPred (Mem.Block a n) ∗
      (∀ p, ⌜Mem.Block a n p⌝ -∗ owns p -∗
        Φ (.byte (scanValue (addresses a n) p acc))) ⊢
      WP (scanBlock (M := M) a n acc) @ Stuckness.NotStuck; E {{ Φ }} := by
  unfold ownsPred
  iintro ⟨⟨%p, %hp, Hp⟩, HK⟩
  unfold scanBlock
  iapply wp_scan (addresses a n) p acc
  · intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' : i < n := List.mem_range.mp hi
    obtain ⟨_, bs, hlen, rfl⟩ := hp
    exact (mem_At_iff bs a _).mpr ⟨i, by omega, rfl⟩
  iframe Hp
  iintro Hp
  iapply HK $$ %p %hp Hp

end SbrClient.Host
