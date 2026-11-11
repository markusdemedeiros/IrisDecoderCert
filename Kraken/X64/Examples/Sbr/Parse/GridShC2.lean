import Kraken.X64.Examples.Sbr.Parse.GridShC1
import Kraken.X64.Examples.Sbr.Parse.LibCall

/-!
# `read_sbr_grid`: the `FIXFIX` `bs_freq_res` fill

`memset(bs_freq_res + 2, bs_freq_res[1], n - 1)`: `FrB` is one byte list, cut at `2` and
`n + 1`; the middle is the callee's block, filled with copies of the flag.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem shC_tb1 (a : UInt8) : Int.toBytes 1 a.toBitVec.toInt = [a] := by
  simp only [Int.toBytes, List.cons.injEq, and_true]
  apply UInt8.toNat_inj.mp
  have h1 : (a.toBitVec.toInt % 256) = a.toNat := by
    rw [BitVec.toInt_eq_toNat_bmod]; simp only [Int.bmod, UInt8.toNat_toBitVec]
    have := a.toNat_lt; split <;> omega
  simp only [Int.take, Int.reducePow, h1, Int.toNat_natCast, Nat.toUInt8_eq, UInt8.ofNat_toNat]

theorem shC_val_cons (a : UInt8) (l : List UInt8) (p : BitVec 64) (h : l.length + 1 ≤ 2 ^ 64) :
    (a :: l) =@ p = [a] =@ p ⋆ l =@ (p + 1#64) := by
  rw [Val.eq, Val.eq, Val.eq, show a :: l = [a] ++ l from rfl, At_append_sep _ _ _ (by simp; omega)]
  rfl

theorem shC_frB_val (d : BitVec 64) (l : List UInt8) (hl : l.length = 9) :
    FrB d l = l =@ (d + 0xc#64) := by
  match l, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8], _ =>
    simp only [FrB, cell1, bv, List.getD_cons_zero, List.getD_cons_succ, shC_tb1]
    rw [shC_val_cons a0 [a1, a2, a3, a4, a5, a6, a7, a8] _ (by simp),
      shC_val_cons a1 [a2, a3, a4, a5, a6, a7, a8] _ (by simp),
      shC_val_cons a2 [a3, a4, a5, a6, a7, a8] _ (by simp),
      shC_val_cons a3 [a4, a5, a6, a7, a8] _ (by simp),
      shC_val_cons a4 [a5, a6, a7, a8] _ (by simp), shC_val_cons a5 [a6, a7, a8] _ (by simp),
      shC_val_cons a6 [a7, a8] _ (by simp), shC_val_cons a7 [a8] _ (by simp)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem shC_val_app3 (a b c : List UInt8) (p : BitVec 64)
    (h : a.length + b.length + c.length ≤ 2 ^ 64) :
    (a ++ b ++ c) =@ p = a =@ p ⋆ (b =@ (p + BitVec.ofNat 64 a.length)
      ⋆ c =@ (p + BitVec.ofNat 64 a.length + BitVec.ofNat 64 b.length)) := by
  rw [Val.eq, Val.eq, Val.eq, Val.eq, List.append_assoc,
    At_append_sep a (b ++ c) _ (by simp only [List.length_append]; omega),
    At_append_sep b c _ (by omega)]

theorem shC_split3 (l : List UInt8) (n : Nat) (h1 : 1 ≤ n) :
    l = l.take 2 ++ (l.drop 2).take (n - 1) ++ l.drop (n + 1) := by
  rw [List.append_assoc, show l.drop (n + 1) = (l.drop 2).drop (n - 1) by
    rw [List.drop_drop]; congr 1; omega, List.take_append_drop, List.take_append_drop]

/-- The frame of the `bs_freq_res[2..n]` fill. -/
abbrev shC_MsR (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (st : GSt) (n : Nat) : Mem 64 → Prop :=
  (st.fr.take 2 =@ (arg3 t₀ + 0xc#64) ⋆ st.fr.drop (n + 1) =@ (arg3 t₀ + 0xe#64 + BitVec.ofNat 64 (n - 1)))
  ⋆ (4 ?@ (arg3 t₀) ⋆ (cell4 ((arg3 t₀) + 8#64) st.n ⋆ (cell4 ((arg3 t₀) + 0x18#64) st.nn
    ⋆ (4 ?@ ((arg3 t₀) + 0x64#64) ⋆ (4 ?@ ((arg3 t₀) + 0x3904#64) ⋆ (4 ?@ ((arg3 t₀) + 0x3908#64)
    ⋆ (TeB (arg3 t₀) st.te ⋆ (TqB (arg3 t₀) st.tq ⋆ (GbW (arg2 t₀) x st.i ⋆ (InW Ext x t₀
    ⋆ FR (Rest x.R ra t₀)))))))))))

theorem shC_T_msPre {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt}
    (h : m =⋆ T k Ext x ra t₀ FR st) (hl : st.fr.length = 9) (n : Nat) (h2 : 2 ≤ n) (h8 : n ≤ 8) :
    m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ ((n - 1) ?@ (arg3 t₀ + 0xe#64) ⋆ shC_MsR k Ext x ra t₀ FR st n)) := by
  rw [T_fr, shC_frB_val _ _ hl, shC_split3 st.fr n (by omega),
    shC_val_app3 _ _ _ _ (by simp only [List.length_take, List.length_drop, hl]; omega)] at h
  have e1 : (st.fr.take 2).length = 2 := by simp only [List.length_take, hl]; omega
  have e2 : ((st.fr.drop 2).take (n - 1)).length = n - 1 := by
    simp only [List.length_take, List.length_drop, hl]; omega
  have ea : arg3 t₀ + 0xc#64 + BitVec.ofNat 64 2 = arg3 t₀ + 0xe#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [e1, e2, ea] at h
  have h' := Mem.ac (H₂ := ((st.fr.drop 2).take (n - 1)) =@ (arg3 t₀ + 0xe#64)
    ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ shC_MsR k Ext x ra t₀ FR st n))) h (by simp only [TxFr, shC_MsR]; ac_rfl)
  have h'' := Block.sep_intro e2 (by omega) h'
  exact Mem.ac h'' (by ac_rfl)

/-- `bs_freq_res[2..n] = b` (the `memset`). -/
abbrev shC_fill (st : GSt) (n : Nat) (b : UInt8) : GSt :=
  { st with fr := st.fr.take 2 ++ List.replicate (n - 1) b ++ st.fr.drop (n + 1) }

theorem shC_T_msPost {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : GArgs} {ra : Int64}
    {t₀ : MachineData} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : GSt} {n : Nat} {b : UInt8}
    (h : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (List.replicate (n - 1) b =@ (arg3 t₀ + 0xe#64) ⋆ shC_MsR k Ext x ra t₀ FR st n)))
    (hl : st.fr.length = 9) (h2 : 2 ≤ n) (h8 : n ≤ 8) :
    m =⋆ T k Ext x ra t₀ FR (shC_fill st n b) := by
  have hl' : (st.fr.take 2 ++ List.replicate (n - 1) b ++ st.fr.drop (n + 1)).length = 9 := by
    simp only [List.length_append, List.length_take, List.length_replicate, List.length_drop, hl]
    omega
  rw [T_fr]
  dsimp only
  rw [shC_frB_val _ _ hl', shC_val_app3 _ _ _ _ (by
    simp only [List.length_take, List.length_replicate, List.length_drop, hl]; omega)]
  have e1 : (st.fr.take 2).length = 2 := by simp only [List.length_take, hl]; omega
  have ea : arg3 t₀ + 0xc#64 + BitVec.ofNat 64 2 = arg3 t₀ + 0xe#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [e1, List.length_replicate, ea]
  exact Mem.ac h (by simp only [TxFr, shC_MsR]; ac_rfl)

theorem shC_fill_get (l : List UInt8) (n e : Nat) (b : UInt8) (hl : l.length = 9) (hn : n ≤ 8)
    (h1 : 1 ≤ n) :
    (l.take 2 ++ List.replicate (n - 1) b ++ l.drop (n + 1)).getD e 0
      = if e < 2 then l.getD e 0 else if e ≤ n then b else l.getD e 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_take,
    List.getElem?_replicate, List.getElem?_drop, List.length_append, List.length_take,
    List.length_replicate, hl, show min 2 9 = 2 from rfl]
  by_cases ha : e < 2
  · simp [ha, show e < 2 + (n - 1) by omega]
  · by_cases hb : e ≤ n
    · simp [ha, hb, show e < 2 + (n - 1) by omega, show e - 2 < n - 1 by omega]
    · simp [ha, hb, show ¬ e < 2 + (n - 1) by omega, show n + 1 + (e - (2 + (n - 1))) = e by omega]

theorem shC_fill_ok {x : GArgs} {st : GSt} {b : UInt8} (hC : GridC x) (hF : SInvF x st)
    (hL : Live st) (h1 : u8 st.fr 1 ≤ 1) (h2 : 2 ≤ st.n.toNat) (hb : b.toNat ≤ 1) :
    SInv x (shC_fill st st.n.toNat b) ∧ Live (shC_fill st st.n.toNat b) := by
  obtain ⟨⟨-, hil, -, -, -, -, -, hinv, hy, -, -, hidx1, hidx2, hv1, hv2, -⟩, -⟩ := hC
  obtain ⟨hfl, htl, hql, hn8, hnn, hte9, htq, hi, hf0⟩ := hF
  have hl' : (st.fr.take 2 ++ List.replicate (st.n.toNat - 1) b
      ++ st.fr.drop (st.n.toNat + 1)).length = 9 := by
    simp only [List.length_append, List.length_take, List.length_replicate, List.length_drop, hfl]
    omega
  refine ⟨⟨⟨hl', hil, htl, hql, hn8, ?_, hnn, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, hL.2.1 _ (Nat.le_refl _), hi⟩, hL⟩
  intro e he
  simp only [GSt.dv] at he
  show ((st.fr.take 2 ++ List.replicate (st.n.toNat - 1) b
      ++ st.fr.drop (st.n.toNat + 1)).getD e 0).toNat ≤ 1
  rw [shC_fill_get _ _ _ _ hfl hn8 (by omega)]
  by_cases ha : e < 2
  · simp only [ha, ↓reduceIte]
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · exact hf0
    · exact h1
  · simp only [ha, he, ↓reduceIte]; exact hb

theorem blk_L4dcb (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop) (hMs : MemsetValSpec k)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4dcb" := by
  cfg_block
  measure_hb "L4dcb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hRB, st, ⟨hF, hL, h1, h2, hdx⟩, hm⟩, hdi, hal⟩, hn⟩ := hs₀
    subst hn
    have hpre := shC_T_msPre hm hF.1 st.n.toNat h2 hF.2.2.2.1
    have hsp : s₀.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64 := hRB.1
    have hbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hpre (by simp)
    have hpush := fun v => Block.storeInt_val hpre (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 48#64 := by
      rw [hsp]; show _ - 40#64 - 8#64 = _; bv_omega
    have hn1 : (s₀.regs.get64 .rdx - 1).toNat = st.n.toNat - 1 := by
      have := hF.2.2.2.1
      rw [hdx]; bv_omega
    have ha : s₀.regs.get64 .rbx + Int64.toBitVec 14 = arg3 t₀ + 0xe#64 := by rw [hbx]; rfl
    have hmT : Hide _ := hm
    clear hm
    vcgen [MachineWP.call_proc_spec_at (⟨shC_MsR k Ext x ra t₀ (Saved t₀) st st.n.toNat⟩ : MsA)
      "memset" hMs]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨?_, fun s' hpost => ?_⟩, hld⟩
    · rw [e48, hn1, ha]; exact hpush _
    · rw [e48, hn1, ha] at hpost
      obtain ⟨-, hsp', hbp', ⟨hbx', h12', h13', -, -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_, ?_⟩, _, shC_fill_ok hC hF hL h1 h2 ?_,
        shC_T_msPost hm' hF.1 h2 hF.2.2.2.1⟩, ?_⟩, Nat.le_refl _⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hRB.2.1]
      · rw [h13', hRB.2.2.1]
      · rw [hbx', hbx]
      · simp only [UInt8.toNat, BitVec.toNat_setWidth] at hal ⊢; omega
      · rw [h12', hdi]

end Kraken.Examples.Sbr.Grid
