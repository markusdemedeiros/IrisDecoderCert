import Kraken.X64.Examples.Sbr.Parse.PsBase

/-!
# `ff_ps_read_data`: access lemmas for the frame `Fr`

Loads and stores at an offset of `*ps` (`c`) or of the locals (`f`), the bitstream buffer, the
Huffman tables; `i32`/`i8` after a store elsewhere.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-! ## Stores into a byte list -/

theorem getD_win (l : List UInt8) (j : Nat) : l.getD j 0 = ((l.drop j).take 1).getD 0 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  simp

theorem i32_wr (c : List UInt8) (o n o' : Nat) (v : Int) (h : o + n ≤ c.length)
    (hd : o' + 4 ≤ o ∨ o + n ≤ o') : i32 (wr c o n v) o' = i32 c o' := by
  simp only [i32, wr_drop_take_disj c o n o' 4 v h hd]

theorem i8_wr (c : List UInt8) (o n j : Nat) (v : Int) (h : o + n ≤ c.length)
    (hd : j + 1 ≤ o ∨ o + n ≤ j) : i8 (wr c o n v) j = i8 c j := by
  simp only [i8, getD_win _ j, wr_drop_take_disj c o n j 1 v h hd]

theorem i8_wr_same (c : List UInt8) (o : Nat) (b : BitVec 8) (h : o + 1 ≤ c.length)
    (hb : b.toNat < 8) : i8 (wr c o 1 b.toInt) o = b.toNat := by
  simp only [i8, getD_win _ o, wr_drop_take_same c o 1 _ h]
  have : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem rd_wr (c : List UInt8) (o n o' n' : Nat) (v : Int) (h : o + n ≤ c.length)
    (hd : o' + n' ≤ o ∨ o + n ≤ o') : rd (wr c o n v) o' n' = rd c o' n' :=
  rd_wr_disj c o n o' n' v h hd

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-! ## Focus on the frame -/

variable [CodeEnv]

/-- `Fr` without `*ps`. -/
def FrC (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f : List UInt8) (i : BitVec 32) : Mem 64 → Prop :=
  f =@ (rsp0 t₀ - 0xa8#64) ⋆ (Sv t₀ ⋆ (8 ?@ (rsp0 t₀ - 0xb0#64)
    ⋆ (Reserve k (rsp0 t₀ - 0xb0#64) ⋆ ((GbW (arg1 t₀) x i ⋆ (Blocks [(x.buf, x.L)]
      ⋆ (PsTabs x.v ⋆ Ext))) ⋆ (RetCell ra (rsp0 t₀) ⋆ x.R)))))

theorem Fr_c (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f c : List UInt8) (i : BitVec 32) :
    Fr k Ext x ra t₀ f c i = c =@ arg2 t₀ ⋆ FrC k Ext x ra t₀ f i := by
  simp only [Fr, PF, FrC]
  exact eq_r (eq_r (eq_r (eq_r (eq_l eq_h))))

theorem Fr_c_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hc : c.length = 764) (o n : Nat) (hin : o + n ≤ 764) :
    m.loadInt (arg2 t₀ + BitVec.ofNat 64 o) n = some (rd c o n) := by
  rw [Fr_c] at h
  exact lc_load h o n (by omega) (by omega)

theorem Fr_c_store {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hc : c.length = 764) (o n : Nat) (hin : o + n ≤ 764) (v : Int) :
    m.storeInt (arg2 t₀ + BitVec.ofNat 64 o) n v =⋆ Fr k Ext x ra t₀ f (wr c o n v) i := by
  rw [Fr_c] at h ⊢
  exact lc_store h o n (by omega) (by omega) v

theorem Fr_f_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hf : f.length = 0x78) (o n : Nat) (hin : o + n ≤ 0x78) :
    m.loadInt (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o) n = some (rd f o n) :=
  lc_load h o n (by omega) (by omega)

theorem Fr_f_store {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hf : f.length = 0x78) (o n : Nat) (hin : o + n ≤ 0x78) (v : Int) :
    m.storeInt (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o) n v =⋆ Fr k Ext x ra t₀ (wr f o n v) c i :=
  lc_store h o n (by omega) (by omega) v

theorem Fr_buf {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    ∃ F, m =⋆ Blocks [(x.buf, x.L)] ⋆ F := by
  simp only [Fr, PF] at h
  exact ⟨_, focus (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r eq_h))))))) h⟩

/-- A load from the bitstream buffer. -/
theorem Fr_buf_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (off : BitVec 64) (n : Nat) (hin : off.toNat + n ≤ x.L) :
    (m.loadInt (x.buf + off) n).isSome = true := by
  obtain ⟨F, hB⟩ := Fr_buf h
  exact Blocks.loadInt_isSome hB (Blocks.Inside.base_add hin)

theorem Fr_tabs {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    ∃ F, m =⋆ PsTabs x.v ⋆ F := by
  simp only [Fr, PF] at h
  exact ⟨_, focus (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r eq_h)))))))) h⟩

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

theorem VPtrs_pick (v : Nat → VlcTab) :
    ∀ n k, k < n → ∃ F, VPtrs v n
      = Int.toBytes 8 (v k).p.toInt =@ (lab "vlc_ps" + BitVec.ofNat 64 (8 * k)) ⋆ F
  | 0, k, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k, h => by
    by_cases hk : k = n
    · subst hk; exact ⟨_, rfl⟩
    · obtain ⟨F, hF⟩ := VPtrs_pick v n k (by omega)
      refine ⟨Int.toBytes 8 (v n).p.toInt =@ (lab "vlc_ps" + BitVec.ofNat 64 (8 * n)) ⋆ F, ?_⟩
      simp only [VPtrs]; rw [hF, Std.ExtHashMap.sep_comm_l]

/-- Loading the pointer `vlc_ps[k]`. -/
theorem Fr_vptr_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 10) :
    m.loadInt (lab "vlc_ps" + BitVec.ofNat 64 (8 * j)) 8
      = some (Int.ofBytes (Int.toBytes 8 (x.v j).p.toInt)) := by
  obtain ⟨F, hF⟩ := Fr_tabs h
  obtain ⟨G, hG⟩ := VPtrs_pick x.v 10 j hj
  simp only [PsTabs] at hF
  rw [hG, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc] at hF
  exact loadInt_sep _ _ 8 _ m hF (Int.toBytes_length 8 _) (by omega)

/-- `n` bytes at offset `o` of table `j`. -/
theorem Fr_vtab_load {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 10) (hw : (x.v j).es.length < 2 ^ 32) (o n : Nat)
    (hin : o + n ≤ (x.v j).es.length) :
    m.loadInt ((x.v j).p + BitVec.ofNat 64 o) n = some (rd (x.v j).es o n) := by
  obtain ⟨F, hF⟩ := Fr_tabs h
  obtain ⟨G, hG⟩ := VTabs_pick x.v 10 j hj
  simp only [PsTabs] at hF
  rw [Std.ExtHashMap.sep_comm_l, hG, Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_assoc] at hF
  exact lc_load hF o n hin hw

end Kraken.Examples.Sbr.Ps
