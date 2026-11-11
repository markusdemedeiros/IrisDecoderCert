import Kraken.X64.Examples.Sbr.Parse.DecExtCpF

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the copy blocks with partial-array moves (coupled path)

`L5e1`, `L5fd`, `L614` of the inlined `copy_sbr_grid(&data[1], &data[0])` move parts of the arrays
`bs_freq_res`, `t_env`, `t_q`. Each array cell is split at the moved bytes first (`fr_split`,
`te_split`, `split1`, `tq_split`); a moved part is a cell of its bytes read as an integer, so the
loads and stores are whole-cell accesses.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem app_split1 (l1 l2 : List UInt8) (a : BitVec 64) (h1 : l1.length = 1) (h2 : l2.length = 8) :
    (l1 ++ l2) =@ a
      = l1 =@ a ⋆ Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes l2)).toInt =@ (a + 1#64) := by
  rw [Val.append_eq l1 l2 a (a + 1#64) (by rw [h1]) (by rw [h1, h2]; decide),
    tb_ofInt 8 l2 h2]

omit [CodeEnv] in
theorem app_split8 (l1 l2 : List UInt8) (a : BitVec 64) (h1 : l1.length = 8) (h2 : l2.length = 2) :
    (l1 ++ l2) =@ a
      = Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes l1)).toInt =@ a ⋆ l2 =@ (a + 8#64) := by
  rw [Val.append_eq l1 l2 a (a + 8#64) (by rw [h1]) (by rw [h1, h2]; decide),
    tb_ofInt 8 l1 h1]

omit [CodeEnv] in
theorem fr_split (l : List UInt8) (a : BitVec 64) (h : l.length = 9) :
    l =@ a = l.take 1 =@ a ⋆ Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes (l.drop 1))).toInt
      =@ (a + 1#64) := by
  have e := app_split1 (l.take 1) (l.drop 1) a (by simp [h]) (by simp [h])
  rw [List.take_append_drop] at e
  exact e

omit [CodeEnv] in
theorem te_split (l : List UInt8) (a : BitVec 64) (h : l.length = 10) :
    l =@ a = Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes (l.take 8))).toInt =@ a
      ⋆ l.drop 8 =@ (a + 8#64) := by
  have e := app_split8 (l.take 8) (l.drop 8) a (by simp [h]) (by simp [h])
  rw [List.take_append_drop] at e
  exact e

omit [CodeEnv] in
theorem ofInt16_ofBytes_toBytes2 (v : Int) :
    BitVec.ofInt 16 (Int.ofBytes (Int.toBytes 2 v)) = BitVec.ofInt 16 v :=
  BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl v

omit [CodeEnv] in
theorem sw16 (x : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x := by
  bv_omega

omit [CodeEnv] in
theorem app3 (l1 l2 : List UInt8) (b : UInt8) (a : BitVec 64) (k : Nat) (hk : l1.length = k)
    (hl : k + 1 + l2.length ≤ 2 ^ 32) :
    (l1 ++ [b] ++ l2) =@ a = l1 =@ a ⋆ (Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [b])).toInt
      =@ (a + BitVec.ofNat 64 k) ⋆ l2 =@ (a + BitVec.ofNat 64 (k + 1))) := by
  rw [List.append_assoc, Val.append_eq l1 ([b] ++ l2) a (a + BitVec.ofNat 64 k) (by rw [hk])
      (by simp only [List.length_append, List.length_singleton]; omega),
    Val.append_eq [b] l2 (a + BitVec.ofNat 64 k) (a + BitVec.ofNat 64 (k + 1))
      (by rw [List.length_singleton, BitVec.add_assoc, BitVec.ofNat_add])
      (by simp only [List.length_singleton]; omega),
    tb_ofInt 1 [b] rfl]

omit [CodeEnv] in
/-- A byte inside a cell, as its own cell. -/
theorem split1 (l : List UInt8) (k : Nat) (a : BitVec 64) (h : k < l.length)
    (hl : l.length ≤ 2 ^ 32) :
    l =@ a = l.take k =@ a ⋆ (Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [l.getD k 0])).toInt
      =@ (a + BitVec.ofNat 64 k) ⋆ l.drop (k + 1) =@ (a + BitVec.ofNat 64 (k + 1))) := by
  have e : l.set k (l.getD k 0) = l := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
      List.set_getElem_self]
  rw [← app3 _ _ _ a k (by simp; omega) (by simp; omega), ← splice1 l k _ h, e]

omit [CodeEnv] in
/-- A stored byte inside a cell. -/
theorem set_split1 (l : List UInt8) (k : Nat) (b : UInt8) (a : BitVec 64) (h : k < l.length)
    (hl : l.length ≤ 2 ^ 32) :
    l.set k b =@ a = l.take k =@ a ⋆ (Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [b])).toInt
      =@ (a + BitVec.ofNat 64 k) ⋆ l.drop (k + 1) =@ (a + BitVec.ofNat 64 (k + 1))) := by
  rw [← app3 _ _ _ a k (by simp; omega) (by simp; omega), ← splice1 l k _ h]

omit [CodeEnv] in
/-- The three bytes of `t_q` as a 2-byte and a 1-byte cell. -/
theorem tq_split (l : List UInt8) (a : BitVec 64) (h : l.length = 3) :
    l =@ a = Int.toBytes 2 (BitVec.ofInt 16 (Int.ofBytes (l.take 2))).toInt =@ a
      ⋆ Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [l.getD 2 0])).toInt =@ (a + 2#64) := by
  have e : l.take 2 ++ [l.getD 2 0] = l := by
    match l, h with
    | [_, _, _], _ => rfl
  rw [← tb_ofInt 2 (l.take 2) (by simp [h]), ← tb_ofInt 1 [l.getD 2 0] rfl]
  conv => lhs; rw [← e]
  rw [Val.append_eq _ _ a (a + 2#64) (by simp [h]) (by simp [h])]
  simp only [tb_ofInt 2 (l.take 2) (by simp [h]), tb_ofInt 1 [l.getD 2 0] rfl]

theorem blk_L5e1 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L5e1" := by
  cfg_block
  measure_hb "L5e1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨e, hCe, rfl⟩, hrb, hm⟩, h12, hdx, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at h12 hdx hbx
    have hD0 : DWF False e.a.d0 := hCe.1.1.2.2.1
    have hD1 : DWF False e.a.d1 := hCe.1.1.2.2.2.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
      c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have l1 : (cpA e.a.d1).freqRes.length = 9 := by simp [cpA, hD1.1]
    have l2 : (cpA e.a.d1).te.length = 10 := by simp [cpA, hD1.2.2.1]
    rw [fr_split e.a.d0.freqRes _ hD0.1, fr_split (cpA e.a.d1).freqRes _ l1,
      te_split e.a.d0.te _ hD0.2.2.1, te_split (cpA e.a.d1).te _ l2] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt,
      BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_40
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, e.setCh true (cpB e.a.d0 e.a.d1), ih,
        ⟨e, hCe, rfl⟩, hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩, Nat.le_of_eq (var_L5fd _)⟩
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, cpB, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [List.take_of_length_le (l := e.a.d0.freqRes.drop 1) (by simp [hD0.1]),
        app_split1 _ _ _ (by simp [l1]) (by simp [hD0.1]),
        app_split8 _ _ _ (by simp [hD0.2.2.1]) (by simp [l2]),
        fr_split e.a.d0.freqRes _ hD0.1, te_split e.a.d0.te _ hD0.2.2.1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm

omit [CodeEnv] in
theorem tq_eq (l m : List UInt8) (hl : l.length = 3) (hm : m.length = 3) :
    (l.take 2 ++ m.drop 2).set 2 (l.getD 2 0) = l := by
  match l, m, hl, hm with
  | [_, _, _], [_, _, _], _, _ => rfl

theorem blk_L5fd (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L5fd" := by
  cfg_block
  measure_hb "L5fd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨e, hCe, rfl⟩, hrb, hm⟩, h12, hdx, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at h12 hdx hbx
    have hD0 : DWF False e.a.d0 := hCe.1.1.2.2.1
    have hD1 : DWF False e.a.d1 := hCe.1.1.2.2.2.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
      c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have l2 : (cpB e.a.d0 e.a.d1).te.length = 10 := by simp [cpB, cpA, hD0.2.2.1, hD1.2.2.1]
    rw [split1 e.a.d0.te 8 _ (by rw [hD0.2.2.1]; omega) (by rw [hD0.2.2.1]; omega),
      split1 (cpB e.a.d0 e.a.d1).te 8 _ (by omega) (by omega),
      tq_split e.a.d0.tq _ hD0.2.2.2.1] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.ofInt8_ofBytes_toBytes1, ofInt16_ofBytes_toBytes2,
      BitVec.ofInt_toInt, sw8, sw16, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_41
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, e.setCh true (cpB2 e.a.d0 e.a.d1), ih,
        ⟨⟨e, hCe, rfl⟩, ?_⟩, hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩, Nat.le_of_eq (var_L614 _)⟩
      · simp only [Reg64s.get64_set64, ite_true, c1_d0]
        bv_omega
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, cpB2, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [set_split1 _ 8 _ _ (by omega) (by omega),
        split1 e.a.d0.te 8 _ (by rw [hD0.2.2.1]; omega) (by rw [hD0.2.2.1]; omega),
        tq_split e.a.d0.tq _ hD0.2.2.2.1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm

theorem blk_L614 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L614" := by
  cfg_block
  measure_hb "L614"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨⟨e, hCe, rfl⟩, hax⟩, hrb, hm⟩, h12, hdx, hbx⟩,
      hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at h12 hdx hbx
    simp only [c1_d0] at hax
    have hD0 : DWF False e.a.d0 := hCe.1.1.2.2.1
    have hD1 : DWF False e.a.d1 := hCe.1.1.2.2.2.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
      c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have l3 : (cpB2 e.a.d0 e.a.d1).tq.length = 3 := by simp [cpB2, cpB, cpA, hD1.2.2.2.1]
    rw [tq_split (cpB2 e.a.d0 e.a.d1).tq _ l3, tq_split e.a.d0.tq _ hD0.2.2.2.1] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hax, BitVec.ofInt8_ofBytes_toBytes1, ofInt16_ofBytes_toBytes2,
      BitVec.ofInt_toInt, sw8, sw16, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_42
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, e.setCh true (cpC e.a.d0 e.a.d1), ih,
        ⟨e, hCe, rfl⟩, hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩, Nat.le_of_eq (var_L62b _)⟩
      have l3' : (cpB e.a.d0 e.a.d1).tq.length = 3 := l3
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, cpC, tq_eq _ _ hD0.2.2.2.1 l3', sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      rw [tq_split e.a.d0.tq (t₀.regs.get64 .rsi + 343814#64) hD0.2.2.2.1,
        tq_split e.a.d0.tq (t₀.regs.get64 .rsi + 255046#64) hD0.2.2.2.1]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm

end Kraken.Examples.Sbr.DecExt
