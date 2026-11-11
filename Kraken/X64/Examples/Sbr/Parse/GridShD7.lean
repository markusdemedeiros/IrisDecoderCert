import Kraken.X64.Examples.Sbr.Parse.GridShD6

/-!
# `read_sbr_grid`: the entry and exit conversions (shard D, part 7)

`GridPre` → the table's entry assertion and `Post'` → `GridPost`: the frame (as in `LfGen`), and
`ChW` (the arrays as byte lists, `e_a` as one 8-byte block) ↔ `ChB` (one cell per byte).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Grid

theorem shD_tb1 (b : UInt8) : Int.toBytes 1 b.toBitVec.toInt = [b] := by
  have h := UInt8.toBytes_ofBytes [b] (by simp)
  have e : UInt8.ofBytes [b] = b := by
    cases b with
    | ofBitVec v =>
      simp only [UInt8.ofBytes, Int.ofBytes, List.foldr_cons, List.foldr_nil, Int.zero_mul,
        Int.zero_add, UInt8.toNat, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e] at h
  simpa only [UInt8.toBytes, List.take_succ_cons, List.take_zero] using h

theorem shD_val_cons (b c : UInt8) (l : List UInt8) (a : BitVec 64)
    (h : l.length + 2 ≤ 2 ^ 64) :
    (b :: c :: l) =@ a = cell1 a b.toBitVec ⋆ (c :: l) =@ (a + 1#64) := by
  simp only [cell1, shD_tb1, Val.eq]
  rw [show b :: c :: l = [b] ++ (c :: l) from rfl,
    At_append_sep [b] (c :: l) a (by simp only [List.length_cons, List.length_nil]; omega)]
  rfl

theorem shD_val_one (b : UInt8) (a : BitVec 64) : [b] =@ a = cell1 a b.toBitVec := by
  simp only [cell1, shD_tb1]

theorem shD_FrB (d : BitVec 64) (l : List UInt8) (hl : l.length = 9) :
    FrB d l = l =@ (d + 0xc#64) := by
  match l, hl with
  | [_, _, _, _, _, _, _, _, _], _ =>
    simp only [FrB, bv, shD_val_cons, shD_val_one, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reducePow, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd,
      List.getD_cons_zero, List.getD_cons_succ]

theorem shD_TeB (d : BitVec 64) (l : List UInt8) (hl : l.length = 10) :
    TeB d l = l =@ (d + 0x15a9c#64) := by
  match l, hl with
  | [_, _, _, _, _, _, _, _, _, _], _ =>
    simp only [TeB, bv, shD_val_cons, shD_val_one, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reducePow, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd,
      List.getD_cons_zero, List.getD_cons_succ]

theorem shD_TqB (d : BitVec 64) (l : List UInt8) (hl : l.length = 3) :
    TqB d l = l =@ (d + 0x15aa6#64) := by
  match l, hl with
  | [_, _, _], _ =>
    simp only [TqB, bv, shD_val_cons, shD_val_one, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reducePow, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd,
      List.getD_cons_zero, List.getD_cons_succ]

theorem shD_ea (d : BitVec 64) :
    8 ?@ (d + 0x3904#64) = 4 ?@ (d + 0x3904#64) ⋆ 4 ?@ (d + 0x3908#64) := by
  rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide), BitVec.add_assoc]
  rfl

theorem shD_ChW (d : BitVec 64) (st : GSt) (hf : st.fr.length = 9) (ht : st.te.length = 10)
    (hq : st.tq.length = 3) : ChW d st = ChB d st := by
  simp only [ChW, ChB, shD_FrB d _ hf, shD_TeB d _ ht, shD_TqB d _ hq, shD_ea,
    Std.ExtHashMap.sep_assoc]

theorem shD_reserve_frame (k : Nat) (r : BitVec 64) (hw : 0x30 ≤ r.toNat)
    (K : Mem 64 → Prop) :
    Reserve (0x30 + k) r ⋆ K
      = 8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ (0x28 ?@ (r - 0x28#64) ⋆ K)) :=
  Reserve_split_frame 0x30 k (by decide) r hw K

theorem shD_split8 (a : BitVec 64) (n : Nat) (hw : n + 8 ≤ 2 ^ 64) :
    (n + 8) ?@ a = 8 ?@ a ⋆ n ?@ (a + 8#64) := by
  rw [Nat.add_comm, Mem.Block.split a 8 n (by omega)]

theorem shD_frame_cells (r : BitVec 64) (K : Mem 64 → Prop) :
    0x28 ?@ (r - 0x28#64) ⋆ K = BlankS r K := by
  rw [show (40 ?@ (r - 0x28#64) : Mem 64 → Prop) = (32 + 8) ?@ (r - 0x28#64) from rfl,
    shD_split8 _ 32 (by decide), show r - 0x28#64 + 8#64 = r - 0x20#64 by bv_omega]
  rw [show (32 ?@ (r - 0x20#64) : Mem 64 → Prop) = (24 + 8) ?@ (r - 0x20#64) from rfl,
    shD_split8 _ 24 (by decide), show r - 0x20#64 + 8#64 = r - 0x18#64 by bv_omega]
  rw [show (24 ?@ (r - 0x18#64) : Mem 64 → Prop) = (16 + 8) ?@ (r - 0x18#64) from rfl,
    shD_split8 _ 16 (by decide), show r - 0x18#64 + 8#64 = r - 0x10#64 by bv_omega]
  rw [show (16 ?@ (r - 0x10#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x10#64) from rfl,
    shD_split8 _ 8 (by decide), show r - 0x10#64 + 8#64 = r - 0x8#64 by bv_omega]
  simp only [BlankS, Std.ExtHashMap.sep_assoc]

theorem shD_Saved_blank (t₀ : MachineData) (K : Mem 64 → Prop) :
    Mem.Entails (Saved t₀ K) (BlankS (t₀.regs.get64 .rsp) K) :=
  Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.refl _)))))

variable [CodeEnv]

theorem shD_GF (Ext : Mem 64 → Prop) (x : GArgs) (t : MachineData) (st : GSt)
    (hf : st.fr.length = 9) (ht : st.te.length = 10) (hq : st.tq.length = 3) (K : Mem 64 → Prop) :
    GF Ext x t st ⋆ K = GFB Ext x t st ⋆ K := by
  unfold GFB
  rw [← shD_ChW _ st hf ht hq]

/-- `GridPre` → the table's entry assertion. -/
theorem grid_pre (k : Nat) (Ext : Mem 64 → Prop) :
    ∀ x ra t, GridPre k Ext x ra t → table k Ext x ra t "read_sbr_grid" t := by
  rintro x ra t ⟨hm, hC⟩
  have hw : 0x30 ≤ (t.regs.get64 .rsp).toNat := by
    have := CallPre.le hm; unfold gridNeed at this; omega
  dsimp only [reduceTable]
  refine ⟨rfl, hC, ?_⟩
  have hD := hC.1
  rw [shD_GF Ext x t x.st hD.1 hD.2.2.1 hD.2.2.2.1] at hm
  simp only [CallPre, gridNeed] at hm
  rw [shD_reserve_frame k _ hw] at hm
  simp only [T, Rest]
  rw [← shD_frame_cells]
  exact Mem.ac hm

/-- `Post'` → `GridPost`. -/
theorem grid_post (k : Nat) (Ext : Mem 64 → Prop) :
    ∀ x ra t₀ s, GridPre k Ext x ra t₀ → Post' k Ext x ra t₀ s → GridPost k Ext x ra t₀ s := by
  rintro x ra t₀ s hp ⟨st, hO, h1, h2, h3, hm⟩
  have hw : 0x30 ≤ (t₀.regs.get64 .rsp).toNat := by
    have := CallPre.le hp.1; unfold gridNeed at this; omega
  have hD := hO.1
  refine ⟨st, hO, h1, h2, h3, ?_⟩
  have hm' := Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (shD_Saved_blank t₀ _))) _ hm
  rw [← shD_frame_cells] at hm'
  rw [shD_GF Ext x t₀ st hD.1 hD.2.2.1 hD.2.2.2.1]
  rw [show gridNeed k = 0x30 + k from rfl, shD_reserve_frame k _ hw]
  exact Mem.ac hm'

end Kraken.Examples.Sbr.Grid
