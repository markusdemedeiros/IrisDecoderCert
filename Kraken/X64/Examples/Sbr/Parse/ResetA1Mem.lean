import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib
import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib

/-!
# `sbr_reset`, shard A1: memory access

* `a1_sp_load`: a byte of `spectrum_params`.
* `a1_cst_load`: a byte of the row `sbr_offset[r]`.
* `a1_k0_store`: the store of `k[0]`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

section Mem

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

omit [CodeEnv] in
theorem a1_pick_ll {A B F : Mem 64 → Prop} (h : m =⋆ (A ⋆ B) ⋆ F) : ∃ F', m =⋆ A ⋆ F' :=
  ⟨B ⋆ F, by rw [Std.ExtHashMap.sep_assoc] at h; exact h⟩

omit [CodeEnv] in
theorem a1_pick_lr {A B F : Mem 64 → Prop} (h : m =⋆ (A ⋆ B) ⋆ F) : ∃ F', m =⋆ B ⋆ F' :=
  ⟨A ⋆ F, by rw [Std.ExtHashMap.sep_comm A B, Std.ExtHashMap.sep_assoc] at h; exact h⟩

/-- Byte `i` of `spectrum_params`. -/
theorem a1_sp_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.sp.length = 6) {i : Nat} (hi : i < 6) :
    m.loadInt (arg1 t₀ + BitVec.ofNat 64 (0x1c + i)) 1 = some (Int.ofBytes (slice st.sp i 1)) :=
  region_load (focus (Mm_sp ..) hm) (by simp only [BitVec.ofNat_add]; bv_omega) (by omega)
    (by omega)

omit [CodeEnv] in
theorem a1_rateRow_le {x : Int} {r : Nat} (h : rateRow x = some r) : r ≤ 5 := by
  unfold rateRow at h
  repeat' (split at h)
  all_goals first | (cases h; omega) | cases h

omit [CodeEnv] in
theorem a1_sbrOffsetBytes_length {r : Nat} (hr : r ≤ 5) : (sbrOffsetBytes r).length = 16 := by
  rcases r with _|_|_|_|_|_|r <;> first | rfl | omega

omit [CodeEnv] in
theorem a1_slice_one {l : List UInt8} {i : Nat} (h : i < l.length) : slice l i 1 = [l.getD i 0] := by
  unfold slice
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

omit [CodeEnv] in
theorem a1_ofBytes_one (b : UInt8) : Int.ofBytes [b] = ((b.toNat : Nat) : Int) := by
  simp only [Int.ofBytes, List.foldr]; push_cast; omega

omit [CodeEnv] in
theorem a1_zx_byte (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 ((b.toNat : Nat) : Int)))
      = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem a1_zx_byte32 (b : UInt8) :
    BitVec.setWidth 32 (BitVec.ofInt 8 ((b.toNat : Nat) : Int)) = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
/-- The sample rate is a positive `int`. -/
theorem a1_sr_toInt {x : BitVec 32} (h : x.toInt ∈ rates) : x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split
  · rfl
  · rename_i hc
    simp only [hc, ↓reduceIte] at h
    have := x.isLt
    simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
    omega

/-- The check of `a1_k0_bv` at one rate and start. -/
def a1_k0chk (n i : Nat) : Bool :=
  match rateRow (n : Int) with
  | some row => BitVec.ofNat 32 ((tmpOf n * 128 + n / 2) / n)
      + (BitVec.ofInt 8 ((((sbrOffsetBytes row).getD i 0).toNat : Nat) : Int)).signExtend 32
      == BitVec.ofNat 32 (k0Of (n : Int) row i).toNat
  | none => true

omit [CodeEnv] in
theorem a1_k0chk_all : ∀ n ∈ [16000, 22050, 24000, 32000, 44100, 48000, 64000, 88200, 96000, 128000,
    176400, 192000], ∀ i, i < 16 → a1_k0chk n i = true := by decide +kernel

omit [CodeEnv] in
/-- `k[0]` as computed by the code: `(temp * 128 + sr / 2) / sr` plus the sign-extended offset. -/
theorem a1_k0_bv {n row : Nat} (hr : rateRow (n : Int) = some row) {i : Nat} (hi : i < 16) :
    BitVec.ofNat 32 ((tmpOf n * 128 + n / 2) / n)
      + (BitVec.ofInt 8 ((((sbrOffsetBytes row).getD i 0).toNat : Nat) : Int)).signExtend 32
      = BitVec.ofNat 32 (k0Of (n : Int) row i).toNat := by
  have hm := rateRow_mem hr
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hm
  have hn : n ∈ [16000, 22050, 24000, 32000, 44100, 48000, 64000, 88200, 96000, 128000,
      176400, 192000] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
  have := a1_k0chk_all n hn i hi
  simp only [a1_k0chk, hr] at this
  exact beq_iff_eq.mp this

omit [CodeEnv] in
theorem a1_sw_ofNat64 (q : Nat) : (BitVec.ofNat 64 q).setWidth 32 = BitVec.ofNat 32 q := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd q (by decide)

omit [CodeEnv] in
theorem a1_toInt_ofNat32 {v : Nat} (h : v < 2 ^ 31) : (BitVec.ofNat 32 v).toInt = (v : Int) := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 2 * v < 2 ^ 32 by omega, ↓reduceIte]

omit [CodeEnv] in
theorem a1_sw64_ofNat32 {v : Nat} (h : v < 2 ^ 32) :
    (BitVec.ofNat 32 v).setWidth 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- The row `sbr_offset[r]` out of the memory. -/
theorem a1_cst_row (hm : m =⋆ Mm k e a ra t₀ st fr) {r : Nat} (hr : r ≤ 5) :
    ∃ F, m =⋆ sbrOffsetBytes r =@ offLab r ⋆ F := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  rcases r with _|_|_|_|_|_|r
  · exact a1_pick_ll h
  · obtain ⟨F, h⟩ := a1_pick_lr h; exact a1_pick_ll h
  · obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; exact a1_pick_ll h
  · obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
    obtain ⟨F, h⟩ := a1_pick_lr h; exact a1_pick_ll h
  · obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
    obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; exact a1_pick_ll h
  · obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
    obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
    obtain ⟨F, h⟩ := a1_pick_lr h; exact a1_pick_ll h
  · omega

/-- Byte `i` of the row `sbr_offset[r]`. -/
theorem a1_cst_load (hm : m =⋆ Mm k e a ra t₀ st fr) {r i : Nat} (hr : r ≤ 5) (hi : i < 16) :
    m.loadInt (offLab r + BitVec.ofNat 64 i) 1 = some (Int.ofBytes (slice (sbrOffsetBytes r) i 1)) := by
  obtain ⟨F, h⟩ := a1_cst_row hm hr
  exact region_load h rfl (by rw [a1_sbrOffsetBytes_length hr]; omega)
    (by rw [a1_sbrOffsetBytes_length hr]; omega)

/-- `k[0]` is readable (the check of a store). -/
theorem a1_k0_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x40#64) 4 = some (Int.ofBytes (slice (Int.toBytes 4 (st.x.k0 : Int)) 0 4)) :=
  region_load (focus (Mm_k0 ..) hm) (by simp) (by rw [Int.toBytes_length]; omega)
    (by rw [Int.toBytes_length]; decide)

/-- The constants `LCPI5_0`, `LCPI5_1` are readable. -/
theorem a1_lcpi0_isSome (hm : m =⋆ Mm k e a ra t₀ st fr) : (m.loadInt (lab "LCPI5_0") 4).isSome = true := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_ll h
  exact cell4_isSome h

theorem a1_lcpi1_isSome (hm : m =⋆ Mm k e a ra t₀ st fr) : (m.loadInt (lab "LCPI5_1") 4).isSome = true := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_ll h
  exact cell4_isSome h

/-- A store of `k[2]`. -/
theorem a1_k2_store (hm : m =⋆ Mm k e a ra t₀ st fr) (v : BitVec 32) :
    m.storeInt (arg1 t₀ + 0x48#64) 4 v.toInt =⋆ Mm k e a ra t₀ { st with k2 := v } fr :=
  Mm_upd_k2 .. ▸ cell4_store' (focus (Mm_k2 ..) hm) v.toInt v rfl

theorem a1_k2_isSome (hm : m =⋆ Mm k e a ra t₀ st fr) :
    (m.loadInt (arg1 t₀ + 0x48#64) 4).isSome = true :=
  cell4_isSome (focus (Mm_k2 ..) hm)

/-- The store of `k[0]`. -/
theorem a1_k0_store (hm : m =⋆ Mm k e a ra t₀ st fr) (v : Nat) :
    m.storeInt (arg1 t₀ + 0x40#64) 4 (v : Int)
      =⋆ Mm k e a ra t₀ { st with x := { st.x with k0 := v } } fr := by
  have h := region_store (addr := arg1 t₀ + 0x40#64) (o := 0) (n := 4) (focus (Mm_k0 ..) hm)
    (by simp) (by rw [Int.toBytes_length]; omega) (by rw [Int.toBytes_length]; decide) (v : Int)
  have hw : wr (Int.toBytes 4 (st.x.k0 : Int)) 0 (Int.toBytes 4 (v : Int)) = Int.toBytes 4 (v : Int) := by
    simp [wr, Int.toBytes_length]
  rw [hw] at h
  rw [← Mm_upd_k0]
  exact h

end Mem

end Kraken.Examples.Sbr.Reset
