import Kraken.X64.Examples.Sbr.Parse.DecExtCpe

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: `bs_add_harmonic` of the channel pair element

`L7b5` loads `n[1]` for `data[0]`; `L8e2`–`L960` the loop unrolled by four (`HL`), `L998`/`L9a7`
the rest. `L9d4` reads `bs_add_harmonic_flag[1]`; `La04`–`Laed` the same loops for `data[1]`.
As in `DecExtHarm`: the elements are bytes of the unowned `48 ?@ (data + 0x31)`, the values `DS`
do not change; the reader's index stays in a register (`RegI`).
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L7b5 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L7b5" := by
  cfg_block
  measure_hb "L7b5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    vcgen
    all_goals subst s₀
    case vc1 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, TabF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
        BitVec.add_assoc, BitVec.reduceAdd]
      sep_mem hmu
      all_goals simp [Int.toBytes_length]
    case vc2 =>
      rename_i v hx _ hc1
      ld_n1
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_28
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_L9d4
        | (simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_false] at hR ⊢
           all_goals first | assumption | exact hR)
    case vc3 =>
      rename_i v hx _ hc1 _ hc2
      ld_n1
      rw [le_all d.a.n1 (by omega)] at hc1
      rw [nc_all d.a.n1 (by omega)] at hc2
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hc1 hc2
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_21
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_, ?_, hc2⟩, hrb, p_h0.down⟩,
        ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_L8e2
        | (simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            and3_all d.a.n1 (by omega)] at hR ⊢
           all_goals first | assumption | exact hR | rfl)
    case vc4 =>
      rename_i v hx _ hc1 _ hc2 _
      ld_n1
      rw [le_all d.a.n1 (by omega)] at hc1
      rw [nc_all d.a.n1 (by omega)] at hc2
      simp only [decide_eq_false_iff_not] at hc1 hc2
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_26
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_, ?_, ?_⟩, hrb, p_h0.down⟩,
        ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_L998
        | (simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            and3_all d.a.n1 (by omega), BitVec.xor_self, BitVec.setWidth_zero,
            BitVec.toNat_ofNat] at hR ⊢
           all_goals first | assumption | exact hR | rfl | omega)

/-- A frame goal `s.regs.get64 r = …` on a register the block does not write. -/
macro "fr_ok" : tactic => `(tactic| (
  (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]) <;>
    first | assumption | trivial))

theorem blk_L8e2 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L8e2" := by
  cfg_block
  measure_hb "L8e2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, h9, h8, h4⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, p_h0.down⟩, ?_⟩, ?_⟩
    all_goals simp only [HL, RegI, var_L8ec, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      h9, h8, mask_all d.a.n1 (by omega), BitVec.xor_self, BitVec.setWidth_zero,
      BitVec.toNat_ofNat, true_and, Nat.zero_mod] at hR ⊢
    all_goals first | assumption | exact hR | omega

theorem blk_L8ec (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L8ec" := by
  cfg_block
  measure_hb "L8ec"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_L913, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_L913 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L913" := by
  cfg_block
  measure_hb "L913"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_L939, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_L939 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L939" := by
  cfg_block
  measure_hb "L939"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_L960, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_L960 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L960" := by
  cfg_block
  measure_hb "L960"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; to_tableC tableC.match_1.eq_22
    case' vc4 => left; apply Table.ofLabels_at; to_tableC tableC.match_1.eq_28
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    case vc3 =>
      rename_i hnz _
      rw [nz_hl _ _ _ hn48 h9 h10b] at hnz
      simp only [ne_eq, decide_eq_true_eq] at hnz
      have e := add4_toNat _ _ hn48 h10b
      refine ⟨by decide, ⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e]
        exact ⟨h9, h8, by omega, by omega⟩
      · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · left
        simp only [var_L8ec, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e, h9,
          BitVec.toNat_ofNat]
        omega
    case vc4 =>
      rename_i hnz hz _
      rw [h8, z_all _ (by omega)] at hz
      refine ⟨by decide, ⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · rw [var_L9d4]; exact Or.inl (by omega)
    case vc5 =>
      rename_i hnz hz _
      rw [h8, z_all _ (by omega)] at hz
      rw [nz_hl _ _ _ hn48 h9 h10b] at hnz
      simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hnz hz
      have e := add4_toNat _ _ hn48 h10b
      refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e, h8,
          BitVec.toNat_ofNat]
        omega
      · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · simp only [var_L998]; omega

theorem blk_L998 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L998" := by
  cfg_block
  measure_hb "L998"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, h108, h80, h84⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    obtain ⟨b, hb⟩ : ∃ b, b = (s₀.regs.get64 .r10).toNat := ⟨_, rfl⟩
    vcgen
    all_goals subst s₀
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ⟨b, ?_, ?_, ?_, ?_⟩⟩, hrb,
      p_h0.down⟩, ?_⟩, ?_⟩
    all_goals simp only [RegI, var_L9a7, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, h14, Int64.toBitVec_ofNat_norm, BitVec.xor_self, BitVec.setWidth_zero,
      BitVec.toNat_zero, sw32_64] at hR ⊢
    all_goals first | assumption | exact hR | omega | (subst hb; exact rdx_b _ _)

theorem blk_L9a7 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L9a7" := by
  cfg_block
  measure_hb "L9a7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, b, hdx, hb8, h98, h84⟩, hrb, hm⟩, hR⟩, hn⟩ :=
      hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; to_tableC tableC.match_1.eq_27
    case' vc4 => to_tableC tableC.match_1.eq_28
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, hdx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    case vc3 =>
      rename_i hnz _
      rw [nz_inc _ _ h98 h84] at hnz
      simp only [ne_eq, decide_eq_true_eq] at hnz
      have e := inc_toNat _ (Nat.lt_trans h98 h84)
      refine ⟨by decide, ⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, b, ?_, ?_, ?_, ?_⟩,
        hrb, ?_⟩, ?_⟩, ?_⟩
      iterate 4
        · first
            | exact hdx
            | omega
            | (rw [e]; omega)
            | rfl
      · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
      · left
        simp only [var_L9a7, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e]
        omega
    case vc4 =>
      refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
      · first | (rw [var_L9d4]; exact Or.inl (by omega)) | (simp only [var_L9d4]; omega)

theorem blk_L9d4 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L9d4" := by
  cfg_block
  measure_hb "L9d4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    dx_br hm
    all_goals try simp only [Width.bytes, BitVec.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    case vc3 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_25]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · fr_ok
      · fr_ok
      · fr_ok
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        rw [← hsi]; exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · fr_ok
      · fr_ok
      · edge_ok var_Lb1a
    case vc4 =>
      to_tableC tableC.match_1.eq_29
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · fr_ok
      · fr_ok
      · fr_ok
      · simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        rw [← hsi]; exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · fr_ok
      · fr_ok
      · exact Nat.le_of_eq (var_La04 _)

theorem blk_La04 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.La04" := by
  cfg_block
  measure_hb "La04"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    vcgen
    all_goals subst s₀
    case vc1 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, TabF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
        BitVec.add_assoc, BitVec.reduceAdd]
      sep_mem hmu
      all_goals simp [Int.toBytes_length]
    case vc2 =>
      rename_i v hx _ hc1
      ld_n1
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_25]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_Lb1a
        | (simp only [RegI, RegB, Reg64s.get64_set64, reduceCtorEq, ite_false] at hR ⊢
           all_goals first | assumption | exact hR)
    case vc3 =>
      rename_i v hx _ hc1 _ hc2
      ld_n1
      rw [le_all d.a.n1 (by omega)] at hc1
      rw [nc_all d.a.n1 (by omega)] at hc2
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hc1 hc2
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_30
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_, ?_, hc2⟩, hrb, p_h0.down⟩,
        ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_La29
        | (simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            and3_all d.a.n1 (by omega)] at hR ⊢
           all_goals first | assumption | exact hR | rfl)
    case vc4 =>
      rename_i v hx _ hc1 _ hc2 _
      ld_n1
      rw [le_all d.a.n1 (by omega)] at hc1
      rw [nc_all d.a.n1 (by omega)] at hc2
      simp only [decide_eq_false_iff_not] at hc1 hc2
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_35
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_, ?_, ?_⟩, hrb, p_h0.down⟩,
        ?_⟩, ?_⟩
      all_goals first
        | edge_ok var_Ladf
        | (simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            and3_all d.a.n1 (by omega), BitVec.xor_self, BitVec.setWidth_zero,
            BitVec.toNat_ofNat] at hR ⊢
           all_goals first | assumption | exact hR | rfl | omega)

omit [CodeEnv] in
theorem rdx_b1 (a r : BitVec 64) :
    BitVec.setWidth 64 255121#64 + (r + a * BitVec.ofNat 64 Width.W8.bytes + 0#64)
      = a + 166176#64 + 88945#64 + BitVec.ofNat 64 r.toNat := by
  simp only [Width.bytes, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_zero]
  bv_omega

theorem blk_La29 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.La29" := by
  cfg_block
  measure_hb "La29"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, h9, h8, h4⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, p_h0.down⟩, ?_⟩, ?_⟩
    all_goals simp only [HL, RegI, var_La33, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      h9, h8, mask_all d.a.n1 (by omega), BitVec.xor_self, BitVec.setWidth_zero,
      BitVec.toNat_ofNat, true_and, Nat.zero_mod] at hR ⊢
    all_goals first | assumption | exact hR | omega

theorem blk_La33 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.La33" := by
  cfg_block
  measure_hb "La33"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · (try simp only [T])
      simp only [LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_La59, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_La59 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.La59" := by
  cfg_block
  measure_hb "La59"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · (try simp only [T])
      simp only [LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_La80, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_La80 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.La80" := by
  cfg_block
  measure_hb "La80"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    all_goals subst s₀
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
    · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact ⟨h9, h8, h10m, h10b⟩
    · (try simp only [T])
      simp only [LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      refine ⟨?_, hsi, hdi⟩
      rw [← hsi]
      exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    · simp only [var_Laa6, Reg64s.get64_set64, reduceCtorEq, ite_false, Nat.le_refl]

theorem blk_Laa6 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Laa6" := by
  cfg_block
  measure_hb "Laa6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hL⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨h9, h8, h10m, h10b⟩ := hL
    obtain ⟨hdx, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; to_tableC tableC.match_1.eq_31
    case' vc4 => left; apply Table.ofLabels_at; rw [table.match_1.eq_25]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hdx hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    case vc3 =>
      rename_i hnz _
      rw [nz_hl _ _ _ hn48 h9 h10b] at hnz
      simp only [ne_eq, decide_eq_true_eq] at hnz
      have e := add4_toNat _ _ hn48 h10b
      refine ⟨by decide, ⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [HL, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e]
        exact ⟨h9, h8, by omega, by omega⟩
      · (try simp only [T])
        simp only [LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · left
        simp only [var_La33, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e, h9,
          BitVec.toNat_ofNat]
        omega
    case vc4 =>
      rename_i hnz hz _
      rw [h8, z_all _ (by omega)] at hz
      refine ⟨by decide, ⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegB, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · rw [var_Lb1a]; exact Or.inl (by omega)
    case vc5 =>
      rename_i hnz hz _
      rw [h8, z_all _ (by omega)] at hz
      rw [nz_hl _ _ _ hn48 h9 h10b] at hnz
      simp only [ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hnz hz
      have e := add4_toNat _ _ hn48 h10b
      refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e, h8,
          BitVec.toNat_ofNat]
        omega
      · (try simp only [T])
        simp only [LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hdx) (hsi ▸ hC.2.2.2.1.2.1)
      · simp only [var_Ladf]; omega

theorem blk_Ladf (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Ladf" := by
  cfg_block
  measure_hb "Ladf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, h108, h80, h84⟩, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    obtain ⟨b, hb⟩ : ∃ b, b = (s₀.regs.get64 .r10).toNat := ⟨_, rfl⟩
    vcgen
    all_goals subst s₀
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ⟨b, ?_, ?_, ?_, ?_⟩⟩, hrb,
      p_h0.down⟩, ?_⟩, ?_⟩
    all_goals simp only [RegI, var_Laed, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64, h14, Int64.toBitVec_ofNat_norm, BitVec.xor_self, BitVec.setWidth_zero,
      BitVec.toNat_zero] at hR ⊢
    all_goals first | assumption | exact hR | omega | (subst hb; simp only [sbrA, arg1]; exact rdx_b1 _ _)

theorem blk_Laed (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Laed" := by
  cfg_block
  measure_hb "Laed"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, b, hdx, hb8, h98, h84⟩, hrb, hm⟩, hR⟩, hn⟩ :=
      hs₀
    var_c hn
    have hn48 : d.a.n1 ≤ 48 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; to_tableC tableC.match_1.eq_36
    case' vc4 => try rw [table.match_1.eq_25]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, hdx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    all_goals try ((try simp only [Nat.zero_add]); omega)
    case vc3 =>
      rename_i hnz _
      rw [nz_inc _ _ h98 h84] at hnz
      simp only [ne_eq, decide_eq_true_eq] at hnz
      have e := inc_toNat _ (Nat.lt_trans h98 h84)
      refine ⟨by decide, ⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, ⟨hE, b, ?_, ?_, ?_, ?_⟩,
        hrb, ?_⟩, ?_⟩, ?_⟩
      iterate 4
        · first
            | exact hdx
            | omega
            | (rw [e]; omega)
            | rfl
      · (try simp only [T])
        simp only [LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegI, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
      · left
        simp only [var_Laed, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, e]
        omega
    case vc4 =>
      refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩, ?_⟩
      · simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · simp only [RegB, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        refine ⟨?_, hsi, hdi⟩
        rw [← hsi]
        exact setl_inc _ _ _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
      · first | (rw [var_Lb1a]; exact Or.inl (by omega)) | (simp only [var_Lb1a]; omega)

end Kraken.Examples.Sbr.DecExt
