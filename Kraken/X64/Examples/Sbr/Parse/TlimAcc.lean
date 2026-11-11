import Kraken.X64.Examples.Sbr.Parse.TlimMem

/-!
# `sbr_make_f_tablelim`: accesses to the read-only fields, `mk16` extensionality
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim

/-- A list of `2 k` bytes is the `mk16` of its elements. -/
theorem mk16_ext {l : List UInt8} {k : Nat} {f : Nat → Nat} (hl : l.length = 2 * k)
    (h : ∀ i, i < k → u16 l i = f i % 65536) : l = mk16 k f := by
  apply List.ext_getElem (by simp [hl])
  intro n h1 h2
  obtain ⟨j, hj⟩ : ∃ j, n = 2 * j ∨ n = 2 * j + 1 := ⟨n / 2, by omega⟩
  have hi := h j (by omega)
  unfold u16 u8 at hi
  have g : ∀ i (hi : i < l.length), l.getD i 0 = l[i] := fun i hi => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rw [g _ (by omega), g _ (by omega)] at hi
  have b1 := (l[2 * j]'(by omega)).toNat_lt
  have b2 := (l[2 * j + 1]'(by omega)).toNat_lt
  simp only [mk16, mk, List.getElem_map, List.getElem_range]
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat']
  rcases hj with rfl | rfl
  · simp only [show 2 * j % 2 = 0 by omega, show 2 * j / 2 = j by omega, ↓reduceIte]
    omega
  · simp only [show ¬ ((2 * j + 1) % 2 = 0) by omega, show (2 * j + 1) / 2 = j by omega,
      ↓reduceIte]
    omega

/-- The low half of a 4-byte cell. -/
theorem u16_toBytes4 (v : Nat) : u16 (Int.toBytes 4 (v : Int)) 0 = v % 65536 := by
  unfold u16 u8
  simp only [Int.toBytes, Int.take, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero,
    List.getD_cons_succ]
  simp only [Nat.toUInt8, UInt8.toNat, UInt8.ofNat, BitVec.toNat_ofNat]
  omega

theorem toBytes2_congr {v w : Int} (h : v % 65536 = w % 65536) :
    Int.toBytes 2 v = Int.toBytes 2 w := by
  have e1 : v % 2 ^ 8 = w % 2 ^ 8 := by omega
  have e2 : v / 256 % 2 ^ 8 = w / 256 % 2 ^ 8 := by omega
  simp only [Int.toBytes, Int.take, Nat.toUInt8, UInt8.ofNat]
  rw [e1, e2]

theorem setW2_congr (l : List UInt8) (q : Nat) {v w : Int} (h : v % 65536 = w % 65536) :
    setW2 l q v = setW2 l q w := by
  simp only [setW2, toBytes2_congr h]

/-- A `movzwl` load stored back with a 2-byte `mov`. -/
theorem sw16_val (u : Nat) (hu : u < 65536) :
    (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u : Int))))).toInt
      % 65536 = (u : Int) % 65536 := by
  have : BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u : Int))))
      = BitVec.ofNat 16 u := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [this, BitVec.toInt_eq_toNat_bmod]
  simp [Int.bmod]
  omega

theorem ofBytes_one (a : UInt8) : Int.ofBytes [a] = (a.toNat : Int) := by
  simp only [Int.ofBytes, List.foldr_cons, List.foldr_nil]; omega

/-- A 1-byte load of byte `j` of the list at `p`. -/
theorem ld8b {m : Mem 64} {l : List UInt8} {p addr : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ l =@ p ⋆ F) (j : Nat) (ha : addr = p + BitVec.ofNat 64 j)
    (hj : j + 1 ≤ l.length) (hl : l.length < 2 ^ 32) :
    m.loadInt addr 1 = some (u8 l j : Int) := by
  have e : (addr - p).toNat = j := by
    rw [ha, BitVec.add_comm, BitVec.add_sub_cancel, ofNat_toNat_small _ (by omega)]
  rw [loadInt_slice h (by rw [e]; omega) (by omega), e]
  have : (l.drop j).take 1 = [l.getD j 0] := by
    rw [show l.getD j 0 = l[j] by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < l.length by omega)]]
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    rcases (by omega : i = 0) with rfl
    simp
  rw [this, ofBytes_one]

section RO

variable [CodeEnv] {m : Mem 64} {x : TArgs} {t₀ : MachineData} {F : Mem 64 → Prop}

theorem RO_kx1h (h : m =⋆ RO x t₀ ⋆ F) :
    m.loadInt (sA t₀ + 0x58#64) 2 = some ((x.a.kx1 % 65536 : Nat) : Int) := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_ll h
  rw [ld16 h 0 (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length]),
    u16_toBytes4]

theorem RO_ftLow (h : m =⋆ RO x t₀ ⋆ F) (hlen : x.a.ftLow.length = 50) (q : Nat)
    (hq : 2 * q + 2 ≤ 50) {addr : BitVec 64}
    (ha : addr = sA t₀ + 0x4c252#64 + BitVec.ofNat 64 (2 * q)) :
    m.loadInt addr 2 = some (u16 x.a.ftLow q : Int) := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_ll h
  exact ld16 h q ha (by omega) (by omega)

theorem RO_np (h : m =⋆ RO x t₀ ⋆ F) :
    m.loadInt (sA t₀ + 0x4c330#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.a.npatch : Int))) := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_ll h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem RO_pnum (h : m =⋆ RO x t₀ ⋆ F) (hlen : x.a.pnum.length = 6) (j : Nat) (hj : j < 6)
    {addr : BitVec 64} (ha : addr = sA t₀ + 0x4c334#64 + BitVec.ofNat 64 j) :
    m.loadInt addr 1 = some (u8 x.a.pnum j : Int) := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_ll h
  exact ld8b h j ha (by omega) (by omega)

theorem RO_bw (h : m =⋆ RO x t₀ ⋆ F) {off : BitVec 64} (hoff : off.toNat + 4 ≤ 12) :
    (m.loadInt (BW + off) 4).isSome = true := by
  simp only [RO] at h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  obtain ⟨F, h⟩ := pick_lr h
  exact blocks_load h hoff

end RO

end Kraken.Examples.Sbr.Tlim
