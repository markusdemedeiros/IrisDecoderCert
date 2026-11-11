import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# The SBR Huffman tables (`ff_aac_sbr_vlc`) and the inlined `get_vlc2` walk

`ff_aac_sbr_vlc[10]` (`libavcodec/aacsbr.h`) holds pointers to ten `VLCElem` tables
(`libavcodec/vlc.h`: `int16_t sym; int16_t len;`, 4 bytes per entry). The parsers inline
`get_vlc2(gb, table, 9, max_depth)`:

* level 1: `idx = show_bits(gb, 9)`, so `idx < 512`;
* if `len < 0` (a subtable): skip 9 bits, `idx = (window >> (len & 31)) + sym` (32-bit, the
  window shifted by `-len` bits from the top), and read the entry there; a third level
  repeats the step.

The table contents are not constrained, except that every subtable index stays inside the
table (`VlcOk`). The tables and the pointer array are read only.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

namespace Kraken.Examples.Sbr.Vlc

instance VWalk.dec (es : List UInt8) : ∀ d i, Decidable (VWalk es d i)
  | 0, _ => isFalse (fun h => h)
  | d + 1, i => by
    have := fun j => VWalk.dec es d (vnext es i j)
    unfold VWalk; exact inferInstance

instance (nb d : Nat) (t : VlcTab) : Decidable (VlcOk nb d t) := by
  unfold VlcOk; exact inferInstance

variable [CodeEnv]

omit [CodeEnv] in
theorem VPtrs_pick (V : BitVec 64) (v : Nat → VlcTab) :
    ∀ n k, k < n → ∃ F, VPtrs V v n = c8 (V + BitVec.ofNat 64 (8 * k)) (v k).p ⋆ F
  | 0, k, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    by_cases hk : k = n
    · subst hk; exact ⟨_, rfl⟩
    · obtain ⟨F, hF⟩ := VPtrs_pick V v n k (by omega)
      refine ⟨c8 (V + BitVec.ofNat 64 (8 * n)) (v n).p ⋆ F, ?_⟩
      simp only [VPtrs]; rw [hF, Std.ExtHashMap.sep_comm_l]

omit [CodeEnv] in
theorem VTabs_pick (v : Nat → VlcTab) :
    ∀ n k, k < n → ∃ F, VTabs v n = (v k).es =@ (v k).p ⋆ F
  | 0, k, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    by_cases hk : k = n
    · subst hk; exact ⟨_, rfl⟩
    · obtain ⟨F, hF⟩ := VTabs_pick v n k (by omega)
      refine ⟨(v n).es =@ (v n).p ⋆ F, ?_⟩
      simp only [VTabs]; rw [hF, Std.ExtHashMap.sep_comm_l]

/-- Pointer `k` at the head. -/
theorem VlcW_ptr (v : Nat → VlcTab) (k : Nat) (hk : k < 10) :
    ∃ F, VlcW v = c8 (VA + BitVec.ofNat 64 (8 * k)) (v k).p ⋆ F := by
  obtain ⟨F, hF⟩ := VPtrs_pick VA v 10 k hk
  exact ⟨F ⋆ VTabs v 10, by simp only [VlcW]; rw [hF, Std.ExtHashMap.sep_assoc]⟩

/-- Table `k` at the head. -/
theorem VlcW_tab (v : Nat → VlcTab) (k : Nat) (hk : k < 10) :
    ∃ F, VlcW v = (v k).es =@ (v k).p ⋆ F := by
  obtain ⟨F, hF⟩ := VTabs_pick v 10 k hk
  exact ⟨VPtrs VA v 10 ⋆ F, by simp only [VlcW]; rw [hF, Std.ExtHashMap.sep_comm_l]⟩

/-- Loading pointer `k`. -/
theorem vlc_load_ptr {m : Mem 64} {v : Nat → VlcTab} {F : Mem 64 → Prop}
    (h : m =⋆ VlcW v ⋆ F) (k : Nat) (hk : k < 10) :
    m.loadInt (VA + BitVec.ofNat 64 (8 * k)) 8
      = some (Int.ofBytes (Int.toBytes 8 (v k).p.toInt)) := by
  obtain ⟨G, hG⟩ := VlcW_ptr v k hk
  rw [hG, Std.ExtHashMap.sep_assoc] at h
  exact loadInt_sep _ _ 8 _ m h (Int.toBytes_length 8 _) (by omega)

omit [CodeEnv] in
/-- Two bytes inside a table. -/
theorem vlc_load2 {m : Mem 64} {t : VlcTab} {F : Mem 64 → Prop} (h : m =⋆ t.es =@ t.p ⋆ F)
    {nb d : Nat} (hok : VlcOk nb d t) {addr : BitVec 64} {o : Nat} (ha : (addr - t.p).toNat = o)
    (hin : o + 2 ≤ t.es.length) :
    m.loadInt addr 2 = some (Int.ofBytes ((t.es.drop o).take 2)) := by
  have hw : t.es.length ≤ 2 ^ 64 := by
    have := hok.2.1; have := hok.1; simp only [VlcTab.N] at *; omega
  rw [← ha]
  exact loadInt_slice h (by omega) hw

/-- `table[i].sym` (as loaded: the bytes at `4 * i`). -/
theorem vlc_load_sym {m : Mem 64} {v : Nat → VlcTab} {F : Mem 64 → Prop}
    (h : m =⋆ VlcW v ⋆ F) (hC : VlcC v) (k : Nat) (hk : k < 10) {i : Nat} (hi : i < (v k).N)
    {addr : BitVec 64} (ha : (addr - (v k).p).toNat = 4 * i) :
    m.loadInt addr 2 = some (Int.ofBytes (((v k).es.drop (4 * i)).take 2)) := by
  obtain ⟨G, hG⟩ := VlcW_tab v k hk
  rw [hG, Std.ExtHashMap.sep_assoc] at h
  have hok := hC k hk
  have := hok.1
  exact vlc_load2 h hok ha (by simp only [VlcTab.N] at hi; omega)

/-- `table[i].len` (the bytes at `4 * i + 2`). -/
theorem vlc_load_len {m : Mem 64} {v : Nat → VlcTab} {F : Mem 64 → Prop}
    (h : m =⋆ VlcW v ⋆ F) (hC : VlcC v) (k : Nat) (hk : k < 10) {i : Nat} (hi : i < (v k).N)
    {addr : BitVec 64} (ha : (addr - (v k).p).toNat = 4 * i + 2) :
    m.loadInt addr 2 = some (Int.ofBytes (((v k).es.drop (4 * i + 2)).take 2)) := by
  obtain ⟨G, hG⟩ := VlcW_tab v k hk
  rw [hG, Std.ExtHashMap.sep_assoc] at h
  have hok := hC k hk
  have := hok.1
  exact vlc_load2 h hok ha (by simp only [VlcTab.N] at hi; omega)

/-! ## Index arithmetic -/

omit [CodeEnv] in
/-- The address of entry `j` (a zero-extended 32-bit index, scale 4). -/
theorem vlc_addr (p : BitVec 64) (j : BitVec 32) (hj : j.toNat < 2 ^ 28) :
    (p + j.setWidth 64 * 4#64 - p).toNat = 4 * j.toNat := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_mul, BitVec.toNat_setWidth]
  simp only [BitVec.toNat_ofNat]
  have := j.isLt
  rw [Nat.mod_eq_of_lt (a := j.toNat) (by omega)]
  omega

omit [CodeEnv] in
theorem vlc_addr2 (p : BitVec 64) (j : BitVec 32) (hj : j.toNat < 2 ^ 28) :
    (p + j.setWidth 64 * 4#64 + 2#64 - p).toNat = 4 * j.toNat + 2 := by
  rw [BitVec.add_assoc, BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_add,
    BitVec.toNat_mul, BitVec.toNat_setWidth]
  simp only [BitVec.toNat_ofNat]
  have := j.isLt
  rw [Nat.mod_eq_of_lt (a := j.toNat) (by omega)]
  omega

omit [CodeEnv] in
/-- Level 1: the 9-bit window. -/
theorem vlc_idx1 (w : BitVec 32) : (w.ushiftRight 23).toNat < 512 := by
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

omit [CodeEnv] in
/-- The shift count of `mov %r10d,%ecx; shr %cl,…` with `r10d` the sign-extended `len`. -/
theorem vlc_sh (len : BitVec 16) :
    ((len.signExtend 32).setWidth 64).toNat % 256 % 32 = len.toNat % 32 := by
  have h1 : ((len.signExtend 32).setWidth 64).toNat = (len.signExtend 32).toNat := by
    rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := (len.signExtend 32).isLt; omega)
  have h2 : (len.signExtend 32).setWidth 16 = len := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
    simp [hi, show i < 32 by omega]
  have h3 : ((len.signExtend 32).setWidth 16).toNat = (len.signExtend 32).toNat % 2 ^ 16 := by
    rw [BitVec.toNat_setWidth]
  rw [h2] at h3
  rw [h1, h3]
  omega

omit [CodeEnv] in
/-- An entry on a walk is an entry of the table. -/
theorem VWalk.lt {es : List UInt8} : ∀ {d i : Nat}, VWalk es d i → i < es.length / 4
  | 0, _, h => h.elim
  | _ + 1, _, h => h.1

omit [CodeEnv] in
/-- Level 1: the first-level index (`< 2 ^ nb`) starts a walk. -/
theorem vlc_walk1 {nb d : Nat} {t : VlcTab} (hok : VlcOk nb d t) {i : Nat} (hi : i < 2 ^ nb) :
    VWalk t.es d i :=
  hok.2.2 i hi

omit [CodeEnv] in
/-- Levels 2 and 3: a subtable entry `i` sends the window `w` to the rest of the walk. -/
theorem vlc_walk_next {es : List UInt8} {d i : Nat} (h : VWalk es (d + 1) i)
    (hneg : (vlen es i).msb = true) (w : BitVec 32) :
    VWalk es d ((w.ushiftRight ((vlen es i).toNat % 32)) + (vsym es i).signExtend 32).toNat := by
  rcases h.2 with h' | h'
  · rw [hneg] at h'; exact absurd h' (by decide)
  · have hj : (w.ushiftRight ((vlen es i).toNat % 32)).toNat
        < 2 ^ (32 - (vlen es i).toNat % 32) := by
      rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have := w.isLt
      have h1 : (vlen es i).toNat % 32 < 32 := Nat.mod_lt _ (by omega)
      apply Nat.div_lt_of_lt_mul
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
      exact this
    have := h' _ hj
    simp only [vnext, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    exact this

end Kraken.Examples.Sbr.Vlc
