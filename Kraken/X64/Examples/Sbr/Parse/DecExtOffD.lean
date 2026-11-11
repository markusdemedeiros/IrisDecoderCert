import Kraken.X64.Examples.Sbr.Parse.DecExtOff

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: `sbr_turnoff` in `read_sbr_data`

The copy of `sbr_turnoff` at `L48b`..`L4cd` (the same stores as `L527`..`L569`) with the locals
`LocW`, and `L4e2`, which forgets them (`LocE`) on the way to `L4ee`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L48b (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L48b" := by
  cfg_block
  measure_hb "L48b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hI, hrd, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, SbrS, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    simp only [sr_merge4] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d.off1, ih, ⟨d, hI, rfl⟩, hrd, ?_⟩,
      Nat.le_of_eq (var_L4a1 _)⟩
    simp only [DecF, SbrF, SbrS, sbrA, arg0, arg1, DS.off1, TabF_sr, AcF_sr, BitVec.add_assoc,
      BitVec.reduceAdd]
    simp only [sr_merge4, BitVec.ofNat_eq_ofNat, tb8_zero]
    sep_close hm

theorem blk_L4a1 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L4a1" := by
  cfg_block
  measure_hb "L4a1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨d₀, hT, rfl⟩, hrd, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, SbrS, sbrA, DS.off1, TabF_sr, AcF_sr, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d₀.off2, ih, ⟨d₀, hT, rfl⟩, hrd, ?_⟩,
      Nat.le_of_eq (var_L4b7 _)⟩
    simp only [DecF, SbrF, SbrS, sbrA, arg0, arg1, DS.off2, TabF_to, AcF_to, Args.turnoff,
      BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.reduceSetWidth] at hm
    try simp only [BitVec.ofNat_eq_ofNat] at hm ⊢
    simp only [tb_32] at hm
    simp only [c4, cell4, z1, z3] at hm ⊢
    sep_close hm

theorem blk_L4b7 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L4b7" := by
  cfg_block
  measure_hb "L4b7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨d₀, hT, rfl⟩, hrd, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, DataF, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    sep_pull hm [Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
        =@ (t₀.regs.get64 .rsi + 269672#64),
      Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
        =@ (t₀.regs.get64 .rsi + 180904#64)] as R hR
    have h1 := Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    have h2 := Block.sep_intro (Int.toBytes_length _ _) (by decide) (Mem.ac (H₂ :=
      Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
        =@ (t₀.regs.get64 .rsi + 180904#64) ⋆ (4 ?@ (t₀.regs.get64 .rsi + 269672#64) ⋆ R)) h1)
    subst hR
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d₀.off2, ih, ⟨d₀, hT, rfl⟩, hrd, ?_⟩,
      Nat.le_of_eq (var_L4cd _)⟩
    simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
    sep_close h2

theorem blk_L4cd (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L4cd" := by
  cfg_block
  measure_hb "L4cd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨d₀, hT, rfl⟩, hrd, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, SbrS, sbrA, DS.off2, TabF_to, AcF_to, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    have hl : d₀.sp.length = 6 := hT.2.1.1
    rw [← List.take_append_drop 4 d₀.sp, sp_split _ _ _ (by simp [hl]) (by simp [hl])] at hm
    have hl4 : (List.take 4 d₀.sp).length = 4 := by simp [hl]
    have hl2 : (List.drop 4 d₀.sp).length = 2 := by simp [hl]
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    all_goals try (simp only [hl4, hl2, BitVec.sub_self, BitVec.toNat_zero, Nat.reducePow]; omega)
    dx_br hm
    all_goals try (simp only [hl4, hl2, BitVec.sub_self, BitVec.toNat_zero, Nat.reducePow]; omega)
    simp only [BitVec.sub_self, BitVec.toNat_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (Nat.le_of_eq hl4), List.drop_eq_nil_of_le (Nat.le_of_eq hl2),
      List.append_nil] at hm
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, gi, d₀.off, ih, einv_off hT, hrd, ?_⟩,
      Nat.le_of_eq (var_L4e2 _)⟩
    simp only [DecF, SbrF, SbrS, sbrA, arg0, arg1, DS.off, TabF_to, AcF_to, Hid.turnoff,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [rep6, sp_split _ _ _ (by decide) (by decide)]
    simp only [c4, cell4, z1, z2, z3] at hm ⊢
    sep_close hm

omit [CodeEnv] in
/-- `read_sbr_data`'s locals forgotten: `LocW` entails `LocE`. -/
theorem locW_locE (X : XA) (t₀ : MachineData) (i0 : BitVec 64) (gi : BitVec 32) :
    Mem.Entails (LocW X t₀ i0 gi) (LocE t₀) := by
  intro m h
  have e8 : t₀.regs.get64 .rsp - 0x48#64 + 8#64 = t₀.regs.get64 .rsp - 0x40#64 := by bv_omega
  have ec : t₀.regs.get64 .rsp - 0x48#64 + 0xc#64 = t₀.regs.get64 .rsp - 0x3c#64 := by bv_omega
  have e10 : t₀.regs.get64 .rsp - 0x48#64 + 0x10#64 = t₀.regs.get64 .rsp - 0x38#64 := by
    bv_omega
  simp only [LocW, LocE, GbR, GbW, cell8, cell4, Apply.c8, e8, ec, e10] at h ⊢
  have h' := Mem.ac (H₂ := Int.toBytes 8 i0.toInt =@ (t₀.regs.get64 .rsp - 0x60#64)
    ⋆ (Int.toBytes 8 (arg0 t₀).toInt =@ (t₀.regs.get64 .rsp - 0x50#64)
    ⋆ (Int.toBytes 8 X.r.buf.toInt =@ (t₀.regs.get64 .rsp - 0x48#64)
    ⋆ (Int.toBytes 4 gi.toInt =@ (t₀.regs.get64 .rsp - 0x40#64)
    ⋆ (Int.toBytes 4 X.r.p8.toInt =@ (t₀.regs.get64 .rsp - 0x38#64)
    ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64)
    ⋆ (Int.toBytes 8 (arg4 t₀).toInt =@ (t₀.regs.get64 .rsp - 0x58#64)
    ⋆ (4 ?@ (t₀.regs.get64 .rsp - 0x3c#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 0x34#64))))))))) h
  have h2 := (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget (Mem.Split.here _ _) (Mem.Entails.forget (Mem.Split.here _ _)
      (Mem.Entails.refl _) (Int.toBytes_length _ _) (by decide))
      (Int.toBytes_length _ _) (by decide))))) m h'
  exact Mem.ac h2

/-- `T` is monotone in the locals. -/
theorem T_locals {kc : Nat} {Ext : Mem 64 → Prop} {X : XA} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {LW LW' : Mem 64 → Prop} {d : DS} {ih : BitVec 32}
    (e : Mem.Entails LW LW') :
    Mem.Entails (T kc Ext X ra t₀ FR LW d ih) (T kc Ext X ra t₀ FR LW' d ih) := by
  refine Mem.Entails.sep_left (Mem.Entails.sep_left ?_)
  intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
  exact ⟨m₁, m₂, hd, hm, e m₁ h₁, h₂⟩

theorem blk_L4e2 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L4e2" := by
  cfg_block
  measure_hb "L4e2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hI, hrd, hm⟩, hn⟩ := hs₀
    var_n hn
    have hE : s₀.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (LocE t₀) d ih :=
      T_locals (locW_locE X t₀ i0 gi) _ hm
    simp only [T, LocW, GbR, GbW] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    all_goals try (simp only [Int.toBytes_length, Nat.reducePow, BitVec.sub_self,
      BitVec.toNat_zero]; omega)
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, ?_, d, ih, hI, hrd.2, hE⟩,
      Nat.le_of_eq (var_L4ee _)⟩
    simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

end Kraken.Examples.Sbr.DecExt
