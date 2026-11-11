import Kraken.X64.Examples.Sbr.SessionBin.Defs

/-!
# A decoding session over the binary: the values

The views of the session's values (`toDS`, `toUSt`, `hidOf`) and the values a parser result
gives (`ofDS`, `ofUSt`) agree; I1 on the bytes (`ParseModel.I1` with `hidOf`) is apply's
`Args.I1`; every reachable value satisfies `SInv`, and the live clauses when its flag is set
(`sreach_inv`), hence `SbrWF` (`sreach_wf`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## The bytes of `spectrum_params` -/

theorem spBytes_length (x : Args) : (spBytes x).length = 6 := by
  simp [spBytes, Int.toBytes_length]

theorem uint8_ofNat_toNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]

/-- Byte 0 of `spectrum_params` is the low byte of `spLo`. -/
theorem u8_spBytes_zero (x : Args) : u8 (spBytes x) 0 = x.spLo.toNat % 256 := by
  simp only [spBytes, u8, Int.toBytes, List.cons_append, List.getD_cons_zero, Int.take]
  simp only [Nat.toUInt8, uint8_ofNat_toNat]
  rw [BitVec.toInt_eq_toNat_cond]
  have := x.spLo.isLt
  split <;> omega

/-- I1 on the bytes is apply's I1. -/
theorem i1_iff (x : Args) (h : Hid) (hs : h.start = u8 (spBytes x) 0) : I1 x h ↔ x.I1 := by
  unfold I1 Args.I1
  rw [hs, u8_spBytes_zero]
  constructor
  · intro h h0
    have := h h0
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    simpa using this
  · intro h h0
    have := congrArg BitVec.toNat (h h0)
    simpa using this

/-- `Int.toBytes` of the value read from `n` bytes gives the bytes back. -/
theorem toBytes_ofBytes (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt, ← Int.toBytes_emod, Int.take]
  have e : (Int.ofBytes bs).bmod (2 ^ (8 * n)) % (2 ^ (8 * n) : Int)
      = Int.ofBytes bs % 2 ^ (8 * n) := Int.bmod_emod
  rw [e, show Int.ofBytes bs % 2 ^ (8 * n) = (Int.ofBytes bs).take (8 * n) from rfl,
    Int.toBytes_emod, ← h, Int.toBytes_ofBytes_all]

/-- The bytes put into `spLo`/`spHi` read back. -/
theorem spBytes_withSp (x : Args) {sp : List UInt8} (h : sp.length = 6) :
    spBytes (withSp x sp) = sp := by
  unfold spBytes withSp
  simp only
  rw [toBytes_ofBytes 4 _ (by simp [h]), toBytes_ofBytes 2 _ (by simp [h])]
  exact List.take_append_drop 4 sp

/-! ## Parser results -/

theorem hidOf_ofDS {d : DecExt.DS} (h : d.ok) : hidOf (ofDS d) = d.h := by
  obtain ⟨hl, hs, hx, -⟩ := h
  unfold hidOf ofDS
  simp only [spBytes_withSp _ hl]
  rw [← hs, ← hx]

theorem hidOf_ofUSt {st : Usac.USt} (it : BitVec 32) (h : Usac.SpOk st) :
    hidOf (ofUSt st it) = st.h := by
  obtain ⟨hl, hs, hx, -⟩ := h
  unfold hidOf ofUSt
  simp only [spBytes_withSp _ hl]
  rw [hs, hx]

/-- `MI`, `LiveC` and `Lens` do not read `spectrum_params`' fields of `Args`. -/
theorem mi_withSp {x : Args} {sp : List UInt8} {h : Hid} : MI (withSp x sp, h) ↔ MI (x, h) :=
  Iff.rfl

theorem liveC_withSp {x : Args} {sp : List UInt8} : LiveC (withSp x sp) ↔ LiveC x := Iff.rfl

theorem lens_withSp {x : Args} {sp : List UInt8} : DecExt.Lens (withSp x sp) ↔ DecExt.Lens x :=
  Iff.rfl

/-! ## The invariant -/

/-- The pieces of `AI` the transfer needs. -/
theorem ai_gridInv {x : Args} (h : AI x) : GridInv x := h.2.2.2.2.2

theorem ai_inv2 {x : Args} (h : AI x) : Inv2 x := fun hs => (h.2.1 hs).2

variable [CodeEnv]

omit [CodeEnv] in
theorem psInv_zero : Ps.PsInv (zs 764) := by
  unfold Ps.PsInv
  simp only [zs, List.length_replicate]
  decide

theorem sinv_init (i : InitIn) : SInv (σInit i) := by
  have hs : (hidOf (σInit i)).start = u8 (spBytes (σInit i).1) 0 := rfl
  have hi1 : (σInit i).1.I1 := fun _ => by
    show (BitVec.allOnes 32).setWidth 8 = 0xFF#8
    decide
  refine ⟨mi_of_wf (sbrWF_xInit i) (gridInv_init i) ((i1_iff _ _ hs).mpr hi1) (inv2_init i),
    psInv_zero, Nat.zero_le 3, ?_⟩
  simp only [DecExt.Lens, σInit, xInit, zs, List.length_replicate, and_self]

omit [CodeEnv] in
/-- The live clauses of `SbrWF`. -/
theorem liveC_of_wf {x : Args} (h : SbrWF x) : LiveC x :=
  ⟨(dwf_iff.mp h.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2, (dwf_iff.mp h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).2⟩

/-- **The session invariant**, from any start with `SInv` and the live clauses. -/
theorem sreach_inv {σ₀ : SV} (h₀ : SInv σ₀ ∧ LiveC σ₀.1) {σ : SV} {ok : Bool}
    (h : SReach σ₀ σ ok) : SInv σ ∧ (ok = true → LiveC σ.1) := by
  induction h with
  | init => exact ⟨h₀.1, fun _ => h₀.2⟩
  | @step σ σ' ok ok' ev _ hap hfr hs ih =>
    obtain ⟨⟨hmi, hpi, hlb, hlens⟩, hlive⟩ := ih
    cases hs with
    | dec d hd =>
      obtain ⟨m, l, hok, pi, -, si⟩ := hd
      have hh := hidOf_ofDS hok
      refine ⟨⟨?_, pi, si, hok.2.2.2⟩, fun _ => l⟩
      show MI (withSp d.a d.sp, hidOf (ofDS d))
      rw [hh]; exact m
    | usac st ret it hm hl hk hsp hlb' hlens' =>
      refine ⟨⟨?_, ?_, hlb', hlens'⟩, fun h => hl (of_decide_eq_true h)⟩
      · show MI (withSp st.x st.sp, hidOf (ofUSt st it))
        rw [hidOf_ofUSt it hsp]; exact hm
      · show Ps.PsInv st.x.psc
        rw [hk.1]; exact hpi
    | config st it hst hsp hk =>
      have hx : st.x = σ.1.turnoff := congrArg Prod.fst hst
      have hhd : st.h = (hidOf σ).turnoff := congrArg Prod.snd hst
      obtain ⟨m, l⟩ := mi_turnoff (s := (σ.1, hidOf σ)) hmi.1
      refine ⟨⟨?_, ?_, ?_, ?_⟩, fun _ => ?_⟩
      · show MI (withSp st.x st.sp, hidOf (ofUSt st it))
        rw [hidOf_ofUSt it hsp, hx, hhd]; exact m
      · show Ps.PsInv st.x.psc
        rw [hk.1]; exact hpi
      · show st.h.lb ≤ 3
        rw [hhd]; exact hlb
      · show DecExt.Lens st.x
        rw [hx]; exact hlens
      · show LiveC st.x
        rw [hx]; exact l
    | @apply _ y u hr =>
      obtain ⟨-, -, -, -, -, hkd, hwf, -⟩ := hr
      have hs0 : ∀ z : SV, (hidOf z).start = u8 (spBytes z.1) 0 := fun _ => rfl
      have hi1 : I1 y (hidOf (y, { σ.2 with usac := u })) :=
        (i1_iff _ _ (hs0 (y, { σ.2 with usac := u }))).mpr (hkd.i1 ((i1_iff _ _ (hs0 σ)).mp hmi.2))
      refine ⟨⟨mi_of_wf hwf (gridInv_stable hkd (ai_gridInv hmi.1)) hi1
        (inv2_stable hkd (ai_inv2 hmi.1)), ?_, hlb, ?_⟩, fun _ => liveC_of_wf hwf⟩
      · show Ps.PsInv y.psc
        rw [hkd.2.2.2.2.2.2.2.2.1]; exact hpi
      · obtain ⟨-, -, -, -, -, -, -, -, hpsc, h2⟩ := hkd
        unfold Args.KeepT at h2
        obtain ⟨-, -, -, -, -, -, p1, p2, t1, t2, t3, t4, -⟩ := h2
        obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hlens
        exact ⟨t1 ▸ l1, t2 ▸ l2, t3 ▸ l3, t4 ▸ l4, p1 ▸ l5, p2 ▸ l6, hpsc ▸ l7⟩
    | @frame _ x' ok'' hf =>
      have hok : ok' = ok := hfr rfl
      subst hok
      rw [hf]
      exact ⟨⟨hmi, hpi, hlb, hlens⟩, hlive⟩

/-- Every value reachable from init satisfies `SInv`, and the live clauses with the flag. -/
theorem sreach_init_inv {i : InitIn} {σ : SV} {ok : Bool} (h : SReach (σInit i) σ ok) :
    SInv σ ∧ (ok = true → LiveC σ.1) :=
  sreach_inv ⟨sinv_init i, fun h => absurd rfl h, fun h => absurd rfl h.1⟩ h

/-- `SbrWF` at every apply call. -/
theorem sreach_wf {i : InitIn} {σ : SV} (h : SReach (σInit i) σ true) : SbrWF σ.1 :=
  (wf_of_mi (sreach_init_inv h).1.1 ((sreach_init_inv h).2 rfl)).1

end Kraken.Examples.Sbr.SessionBin
