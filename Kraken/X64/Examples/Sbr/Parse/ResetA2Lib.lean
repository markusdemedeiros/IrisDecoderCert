import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetIface

/-!
# `sbr_reset`, shard A2: frame and array access

The frame region `fr` (`rbp - 0x570`, `0x548` bytes) is one byte-list cell of `Mm`. A load or a
store at `rbp - d` reads / writes `fr` at offset `rb d = 0x570 - d` (`region_load`,
`region_store`); the slots and the `int16` arrays `vk0` (`rbp - 0x170`), `vk1` (`rbp - 0xf0`)
are views of `fr` (`frSlot32`, `frSlot64`, `A2.fv`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

section Frame

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

omit [CodeEnv] in
/-- The address of `rbp - d` inside the frame region. -/
theorem fr_addr (r : BitVec 64) (d : Nat) (hd : d ≤ 0x570) :
    r - 8#64 - BitVec.ofNat 64 d = r - 0x578#64 + BitVec.ofNat 64 (rb d) := by
  simp only [rb]; bv_omega

/-- A load of `n` bytes at `rbp - d` reads the frame there. -/
theorem fr_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {d n : Nat}
    (hn : n + 0x28 ≤ d) (hd : d ≤ 0x570) :
    m.loadInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 d) n
      = some (Int.ofBytes (slice fr (rb d) n)) :=
  region_load (focus (Mm_fr ..) hm) (fr_addr _ d hd) (by simp only [rb]; omega)
    (by rw [hF]; decide)

/-- A store of `n` bytes at `rbp - d` writes the frame there. -/
theorem fr_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {d n : Nat}
    (hn : n + 0x28 ≤ d) (hd : d ≤ 0x570) (v : Int) :
    m.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 d) n v
      =⋆ Mm k e a ra t₀ st (wr fr (rb d) (Int.toBytes n v)) :=
  Mm_upd_fr .. ▸ region_store (focus (Mm_fr ..) hm) (fr_addr _ d hd) (by simp only [rb]; omega)
    (by rw [hF]; decide) v

omit [CodeEnv] in
theorem fr_wr_len (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int) :
    FrOk (wr fr o (Int.toBytes n v)) := by
  unfold FrOk at *
  rw [wr_length (by rw [Int.toBytes_length, hF]; omega), hF]

omit [CodeEnv] in
/-- A slot read back after a store to it. -/
theorem slice_wr_toBytes (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int) :
    slice (wr fr o (Int.toBytes n v)) o n = Int.toBytes n v := by
  have := slice_wr_same (l := fr) (o := o) (v := Int.toBytes n v)
    (by rw [Int.toBytes_length, hF]; omega)
  rwa [Int.toBytes_length] at this

omit [CodeEnv] in
/-- A slot elsewhere is unchanged by a store. -/
theorem slice_wr_other (hF : FrOk fr) {o n : Nat} (h : o + n ≤ 0x548) (v : Int) {o' n' : Nat}
    (hd : o' + n' ≤ o ∨ o + n ≤ o') :
    slice (wr fr o (Int.toBytes n v)) o' n' = slice fr o' n' :=
  slice_wr_disj (by rw [Int.toBytes_length, hF]; omega) (by rw [Int.toBytes_length]; exact hd)

omit [CodeEnv] in
theorem frSlot32_wr_same (hF : FrOk fr) {d : Nat} (h : 0x2c ≤ d) (hd : d ≤ 0x570) (v : Int) :
    frSlot32 (wr fr (rb d) (Int.toBytes 4 v)) d = BitVec.ofInt 32 v := by
  simp only [frSlot32]
  rw [slice_wr_toBytes hF (by simp only [rb]; omega), BitVec.ofInt32_ofBytes_toBytes4]

omit [CodeEnv] in
theorem frSlot64_wr_same (hF : FrOk fr) {d : Nat} (h : 0x30 ≤ d) (hd : d ≤ 0x570) (v : Int) :
    frSlot64 (wr fr (rb d) (Int.toBytes 8 v)) d = BitVec.ofInt 64 v := by
  simp only [frSlot64]
  rw [slice_wr_toBytes hF (by simp only [rb]; omega), BitVec.ofInt64_ofBytes_toBytes8]

omit [CodeEnv] in
theorem frSlot32_wr_other (hF : FrOk fr) {d n : Nat} (h : n + 0x28 ≤ d) (hd : d ≤ 0x570) (v : Int)
    {d' : Nat} (h' : 0x2c ≤ d') (hd' : d' ≤ 0x570) (hne : d' + n ≤ d ∨ d + 4 ≤ d') :
    frSlot32 (wr fr (rb d) (Int.toBytes n v)) d' = frSlot32 fr d' := by
  simp only [frSlot32]
  rw [slice_wr_other hF (by simp only [rb]; omega) v (by simp only [rb]; omega)]

omit [CodeEnv] in
theorem frSlot64_wr_other (hF : FrOk fr) {d n : Nat} (h : n + 0x28 ≤ d) (hd : d ≤ 0x570) (v : Int)
    {d' : Nat} (h' : 0x30 ≤ d') (hd' : d' ≤ 0x570) (hne : d' + n ≤ d ∨ d + 8 ≤ d') :
    frSlot64 (wr fr (rb d) (Int.toBytes n v)) d' = frSlot64 fr d' := by
  simp only [frSlot64]
  rw [slice_wr_other hF (by simp only [rb]; omega) v (by simp only [rb]; omega)]

end Frame

end Kraken.Examples.Sbr.Reset

/-! ## Values: bytes, conversions, flags, the band counts -/

namespace Kraken.Examples.Sbr.Reset

theorem a2_ex0_eq_sw (x : BitVec 128) : x.extractLsb' 0 32 = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_setWidth]

theorem a2_lea2 (X : BitVec 64) : (X + X).setWidth 32 = BitVec.ofInt 32 (2 * X.toInt) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_setWidth, BitVec.toNat_add]
  rw [BitVec.toInt_eq_toNat_bmod]
  simp only [Int.bmod_def]
  split <;> split <;> omega

theorem a2_even_nb (x : Int) : (BitVec.ofInt 32 (2 * x)).toInt % 2 = 0 := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod_def]; split <;> omega

theorem a2_cc_le_test (V : BitVec 32) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (V &&& V) { cf := false, af := af, of := false })
      = decide (V.toInt ≤ 0) := by
  rw [BitVec.and_self]
  simp only [CondCode.interp_le, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
    StatusFlags.of_from_result]
  have hz : (V == BitVec.zero 32) = decide (V.toNat = 0) := by
    by_cases h : V.toNat = 0
    · have : V = BitVec.zero 32 := BitVec.eq_of_toNat_eq (by simp [h])
      simp [this]
    · have : V ≠ 0#32 := fun h' => h (by simp [h'])
      simpa [h] using this
  rw [hz, BitVec.toInt_eq_msb_cond]
  have := V.isLt
  cases hm : V.msb <;> simp <;> omega

theorem a2_take4_toBytes8 (v : Int) : (Int.toBytes 8 v).take 4 = Int.toBytes 4 v := by
  simp [Int.toBytes]

theorem a2_frSlot32_wr8_same {fr : List UInt8} (hF : FrOk fr) {d : Nat} (h : 0x30 ≤ d) (hd : d ≤ 0x570)
    (v : Int) : frSlot32 (wr fr (rb d) (Int.toBytes 8 v)) d = BitVec.ofInt 32 v := by
  have h8 := slice_wr_toBytes hF (o := rb d) (n := 8) (by simp only [rb]; omega) v
  have : slice (wr fr (rb d) (Int.toBytes 8 v)) (rb d) 4
      = (slice (wr fr (rb d) (Int.toBytes 8 v)) (rb d) 8).take 4 := by
    simp only [slice, List.take_take]; rfl
  simp only [frSlot32]
  rw [this, h8, a2_take4_toBytes8, BitVec.ofInt32_ofBytes_toBytes4]


theorem a2_k0Of_nonneg {sr : Int} {row st : Nat} (hrow : rateRow sr = some row) (h0 : st < 16) :
    0 ≤ k0Of sr row st := by
  have hm := rateRow_mem hrow
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at hm
  revert h0 st
  rcases hm with h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp [rateRow] at hrow <;> subst hrow <;>
    decide

variable [CodeEnv]

theorem a2_bands_of {e : REnv} {a : RArgs} {t₀ : MachineData} {row k2 : Nat} (hB : BandsOK e.lg e.pw)
    (hC : ResetCI a t₀) (hrow : rateRow (srI a) = some row) (hk2 : k2 ≤ 64) (hk02 : k0N a row ≤ k2)
    (hkq : (k2 : Int) - k0A a row ≤ maxQ (srI a)) (hu : 1 ≤ u8 a.sp 3) :
    (0 < A2.n0I e a (k0N a row) k2 → A2.n0I e a (k0N a row) k2 ≤ 48
        ∧ BandsAt e.pw (k0N a row) (A2.k1Of (k0N a row) k2) (A2.n0N e a (k0N a row) k2))
    ∧ (110 * k0N a row < 49 * k2 → 2 ≤ A2.n1I e a (k0N a row) k2 ∧ A2.n1I e a (k0N a row) k2 ≤ 48
        ∧ BandsAt e.pw (A2.k1Of (k0N a row) k2) k2 (A2.n1N e a (k0N a row) k2)) := by
  have h := hB.1 (srI a) (rateRow_mem hrow) (u8 a.sp 0) hC.2.1 k2 hk2 (u8 a.sp 3) hu hC.2.2.1
    (u8 a.sp 4) hC.2.2.2.1
  rw [hrow] at h
  have hk0 := a2_k0Of_nonneg hrow hC.2.1
  exact h hk02 (by simp only [k0A] at hkq; rw [Int.toNat_of_nonneg hk0]; exact hkq)


section Moved

variable [CodeEnv]

omit [CodeEnv] in
theorem a2_ofBytes_slice1 (l : List UInt8) (i : Nat) (h : i < l.length) :
    Int.ofBytes (slice l i 1) = (u8 l i : Int) := by
  have hd := List.drop_eq_getElem_cons h
  unfold slice u8 Int.ofBytes
  rw [hd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [List.take_succ_cons, List.take_zero, List.foldr_cons, List.foldr_nil, Option.getD_some]
  omega

/-- A byte of `spectrum_params`. -/
theorem a2_sp_load {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.sp.length = 6)
    {i : Nat} (hi : i < 6) :
    m.loadInt (arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 i) 1 = some (u8 st.sp i : Int) := by
  rw [region_load (n := 1) (focus (Mm_sp ..) hm) rfl (by omega) (by omega),
    a2_ofBytes_slice1 _ _ (by omega)]

end Moved

end Kraken.Examples.Sbr.Reset
