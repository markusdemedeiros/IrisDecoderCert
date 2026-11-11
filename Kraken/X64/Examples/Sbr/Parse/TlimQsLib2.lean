import Kraken.X64.Examples.Sbr.Parse.TlimQsLib

/-!
# `sbr_make_f_tablelim`: `AV_QSORT` helpers for stores and 16-bit compares
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Parse.Qsort

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

omit [CodeEnv] in
theorem sw64_16 (u : Nat) : BitVec.setWidth 16 (BitVec.ofNat 64 u) = BitVec.ofNat 16 u := by
  apply BitVec.eq_of_toNat_eq; simp

omit [CodeEnv] in
theorem zx32_64 (u : Nat) (hu : u < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 u)) = BitVec.ofNat 64 u := by
  apply BitVec.eq_of_toNat_eq; simp; omega

omit [CodeEnv] in
/-- The value of a 2-byte store of a 64-bit register holding `u`. -/
theorem sv16 (u : Nat) (hu : u < 65536) :
    ((BitVec.setWidth 16 (BitVec.ofNat 64 u)).toInt % 65536).toNat = u := by
  rw [sw64_16, BitVec.toInt_eq_toNat_bmod]
  simp [Int.bmod]
  omega

/-- A 2-byte store into element `q` of `f_tablelim`. -/
theorem st_fl {m : Mem 64} {k : Nat} {x : TArgs} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {fl : List UInt8} {nl : Nat} {stk pb : List UInt8}
    (hm : m =⋆ T k x ra t₀ FR ⟨fl, nl, stk, pb⟩) (hl : fl.length = 60) (q : Nat) (hq : q < 30)
    {addr : BitVec 64} (ha : addr = pA t₀ + BitVec.ofNat 64 (2 * q)) (v : Int) :
    m.storeInt addr 2 v =⋆ T k x ra t₀ FR ⟨setW2 fl q v, nl, stk, pb⟩ :=
  focus (T_fl k x ra t₀ FR ⟨setW2 fl q v, nl, stk, pb⟩).symm
    (st16 (focus (T_fl k x ra t₀ FR ⟨fl, nl, stk, pb⟩) hm) q ha (by simp only; omega)
      (by simp only; omega) v)

omit [CodeEnv] in
theorem Lens_set {fl stk pb : List UInt8} {nl : Nat} (h : Lens ⟨fl, nl, stk, pb⟩) (q : Nat)
    (hq : q < 30) (v : Int) : Lens ⟨setW2 fl q v, nl, stk, pb⟩ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by rw [setW2_length _ _ _ (by simp only at h1; omega)]; exact h1, h2, h3⟩

omit [CodeEnv] in
/-- The array after storing a register holding `u` at `q`. -/
theorem AV_set {fl : List UInt8} (hl : fl.length = 60) (q : Nat) (hq : q < 30) (u : Nat)
    (hu : u < 65536) (r : Nat) :
    AV (setW2 fl q (BitVec.setWidth 16 (BitVec.ofNat 64 u)).toInt) r = Qsort.upd (AV fl) q u r := by
  simp only [AV, Qsort.upd]
  rw [u16_setW2 _ _ _ (by omega), sv16 u hu]

omit [CodeEnv] in
/-- The second store of an exchange (`upd` of an `upd`). -/
theorem upd_swap_of {A B : Nat → Nat} {i j : Nat} (hB : ∀ q, B q = Qsort.upd A j (A i) q)
    (q : Nat) : Qsort.upd B i (A j) q = swap A i j q := by
  unfold Qsort.upd; rw [hB q, ← upd_upd_swap]; rfl

omit [CodeEnv] in
theorem qi_congr {N : Nat} {A B A0 : Nat → Nat} {P : List Iv} (h : QI N A A0 P)
    (e : ∀ q, B q = A q) : QI N B A0 P := funext e ▸ h

end Kraken.Examples.Sbr.Tlim
