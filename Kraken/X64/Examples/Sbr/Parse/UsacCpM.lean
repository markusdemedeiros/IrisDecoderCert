import Kraken.X64.Examples.Sbr.Parse.UsacBase
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option linter.unusedSimpArgs false
/-! # `ff_aac_sbr_decode_usac_data`: the inlined `copy_sbr_grid` and the `bs_invf_mode` copies
(model facts)

The byte copies `cpA`..`cpE` are `copyGrid`; `invfShift` then `invfCouple` keeps `SE01`. -/
namespace Kraken.Examples.Sbr.Usac

theorem old_eq (l : List UInt8) (j : Nat) (h : j < l.length) : old l j = l[j] := by
  simp [old, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- The five copies are `copy_sbr_grid(&data[1], &data[0])`. -/
theorem cpE_eq {d0 d1 : DV} (hd0 : DWF False d0) (hd1 : DWF False d1) :
    cpE d0 d1 = copyGrid d1 d0 := by
  obtain ⟨a1, -, a3, a4, -⟩ := hd0
  obtain ⟨b1, -, b3, b4, b5, -⟩ := hd1
  have f : ((d1.freqRes.set 0 (d1.freqRes.getD d1.nenv 0)).take 1 ++ (d0.freqRes.drop 1).take 8)
      = mk 9 (fun j => if j = 0 then old d1.freqRes d1.nenv else old d0.freqRes j) := by
    apply List.ext_getElem
    · simp [mk, a1, b1]
    · intro i h₁ h₂
      simp only [mk, List.getElem_map, List.getElem_range]
      simp only [List.length_append, List.length_take, List.length_set, List.length_drop, a1,
        b1] at h₁
      by_cases hi : i = 0
      · subst hi
        rw [List.getElem_append_left (by simp [b1])]
        simp [List.getElem_take, List.getElem_set, old]
      · rw [List.getElem_append_right (by simp [b1]; omega)]
        simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_set, b1,
          hi, ↓reduceIte]
        rw [old_eq _ _ (by omega)]
        congr 1; omega
  have t : ((d0.te.take 8 ++ (d1.te.set 9 (d1.te.getD d1.nenv 0)).drop 8).set 8 (d0.te.getD 8 0))
      = mk 10 (fun j => if j = 9 then old d1.te d1.nenv else old d0.te j) := by
    apply List.ext_getElem
    · simp [mk, a3, b3]
    · intro i h₁ h₂
      simp only [mk, List.getElem_map, List.getElem_range]
      simp only [List.length_set, List.length_append, List.length_take, List.length_drop, a3,
        b3] at h₁
      rw [List.getElem_set]
      by_cases h8 : i = 8
      · subst h8; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm h8)]
        by_cases hlt : i < 8
        · rw [List.getElem_append_left (by simp [a3]; omega)]
          simp [List.getElem_take, show i ≠ 9 by omega,
            List.getElem?_eq_getElem (show i < d0.te.length by omega)]
        · have h9 : i = 9 := by omega
          subst h9
          rw [List.getElem_append_right (by simp [a3])]
          simp [List.getElem_drop, List.getElem_set, a3]
  have q : (d0.tq.take 2 ++ d1.tq.drop 2).set 2 (d0.tq.getD 2 0) = mk 3 (fun j => old d0.tq j) := by
    apply List.ext_getElem
    · simp [mk, a4, b4]
    · intro i h₁ h₂
      simp only [mk, List.getElem_map, List.getElem_range]
      simp only [List.length_set, List.length_append, List.length_take, List.length_drop, a4,
        b4] at h₁
      rw [List.getElem_set]
      by_cases h2 : i = 2
      · subst h2; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm h2),
          List.getElem_append_left (by simp [a4]; omega)]
        simp [List.getElem_take, List.getElem?_eq_getElem (show i < d0.tq.length by omega)]
  unfold cpE cpD cpC cpB cpA copyGrid
  simp only [List.take_set_of_le, f, t, q]

/-- The copy keeps `SE01`'s parts: `MI` (`copy_wf`), a live channel 1. -/
theorem se01_cp {t₀ : MachineData} {st : USt} (hS : SE0 t₀ st) :
    SE01 t₀ (st.wd1 (cpE st.x.d0 st.x.d1)) := by
  obtain ⟨⟨⟨⟨a1, a2, a3, a4, a5, g0, g1⟩, i1⟩, hid, hu⟩, hl0⟩ := hS
  rw [cpE_eq a3 a4]
  obtain ⟨c1, c2, c3, -⟩ := copy_wf a3 g0 a4 g1
  exact ⟨⟨⟨⟨a1, a2, a3, c1, a5, g0, c2⟩, i1⟩, hid, hu⟩, hl0, c3 hl0⟩

theorem dwf_invfShift {v : DV} (h : DWF False v) : DWF False (invfShift v) := by
  unfold invfShift
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, -⟩ := h
  refine ⟨b1, mk_length _ _, b3, b4, b5, b6, b7, fun i hi => ?_, b9, b10, b11, b12, b13, b14, b15,
    False.elim⟩
  rw [u8_mk]; have := b8 i hi; (repeat' split) <;> bnd

/-- The two `memcpy` of `bs_invf_mode` keep `SE01`. -/
theorem se01_inv {t₀ : MachineData} {st : USt} (hS : SE01 t₀ st) :
    SE01 t₀ (st.wd1 (invfCouple st.x.d0 (invfShift st.x.d1))) := by
  obtain ⟨⟨⟨⟨a1, a2, a3, a4, a5, g0, g1⟩, i1⟩, hid, hu⟩, hl0, hl1⟩ := hS
  exact ⟨⟨⟨⟨a1, a2, a3, dwf_invfCouple a3 (dwf_invfShift a4), a5, g0, g1⟩, i1⟩, hid, hu⟩, hl0,
    live_invfCouple hl1⟩

/-- Bytes loaded into a register and stored back. -/
theorem tb_of (n : Nat) (bs : List UInt8) (h : bs.length = n) :
    Int.toBytes n (BitVec.ofInt (8 * n) (Int.ofBytes bs)).toInt = bs := by
  rw [BitVec.toInt_ofInt]
  have e : (2 ^ (8 * n) : Nat) = 256 ^ n := by
    rw [Nat.pow_mul]
  rw [e]
  exact Int.toBytes_bmod_ofBytes n bs h

end Kraken.Examples.Sbr.Usac
