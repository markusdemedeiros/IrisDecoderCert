import Kraken.X64.Examples.Sbr.Parse.DecExtOffD
import Kraken.X64.Examples.Sbr.Parse.DecExtCall

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the head of `read_sbr_data` (`L128`)

`sbr->id_aac = id_aac; sbr->ready_for_dequant = 1` (`DS.dat`), `ac` and the reader's index
saved in the locals (`LocW`); a decoder not started goes to the exit (`L4ee`, the locals
forgotten), a single (or coupling) channel element to `L349`, the rest to `L164`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- The locals before `read_sbr_data` forgotten: `LocW0` entails `LocE`. -/
theorem locW0_locE (X : XA) (t₀ : MachineData) (gi : BitVec 32) :
    Mem.Entails (LocW0 X t₀ gi) (LocE t₀) := by
  intro m h
  have e8 : t₀.regs.get64 .rsp - 0x48#64 + 8#64 = t₀.regs.get64 .rsp - 0x40#64 := by bv_omega
  have ec : t₀.regs.get64 .rsp - 0x48#64 + 0xc#64 = t₀.regs.get64 .rsp - 0x3c#64 := by bv_omega
  have e10 : t₀.regs.get64 .rsp - 0x48#64 + 0x10#64 = t₀.regs.get64 .rsp - 0x38#64 := by
    bv_omega
  simp only [LocW0, LocE, GbR, GbW, cell8, cell4, Apply.c8, e8, ec, e10] at h ⊢
  have h' := Mem.ac (H₂ := Int.toBytes 8 X.r.buf.toInt =@ (t₀.regs.get64 .rsp - 0x48#64)
    ⋆ (Int.toBytes 4 gi.toInt =@ (t₀.regs.get64 .rsp - 0x40#64)
    ⋆ (Int.toBytes 4 X.r.p8.toInt =@ (t₀.regs.get64 .rsp - 0x38#64)
    ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x68#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
    ⋆ (Int.toBytes 8 (arg4 t₀).toInt =@ (t₀.regs.get64 .rsp - 0x58#64)
    ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64)
    ⋆ (4 ?@ (t₀.regs.get64 .rsp - 0x3c#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 0x34#64))))))))) h
  have h2 := (Mem.Entails.forget8 _ _
    (Mem.Entails.forget (Mem.Split.here _ _) (Mem.Entails.forget (Mem.Split.here _ _)
      (Mem.Entails.refl _) (Int.toBytes_length _ _) (by decide))
      (Int.toBytes_length _ _) (by decide))) m h'
  exact Mem.ac h2

omit [CodeEnv] in
/-- A decoder not started: `EInv` (the live clauses are about a started decoder). -/
theorem einv_start0 {PI : List UInt8 → Prop} {X : XA} {d : DS} (h : Inv2 PI X d)
    (hs : d.a.start = 0) : EInv PI X d :=
  ⟨h.1, ⟨fun h' => absurd hs h', fun h' => absurd hs h'.1⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

omit [CodeEnv] in
/-- After `DS.dat`: `SInv`. -/
theorem sinv_dat {PI : List UInt8 → Prop} {X : XA} {t₀ : MachineData} {d : DS}
    (h : Inv2 PI X d) (hs : d.a.start ≠ 0) : SInv PI X t₀ (d.dat (idA t₀)) :=
  ⟨⟨⟨ai_id _ h.1.1, h.1.2⟩, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, hs, rfl⟩

omit [CodeEnv] in
theorem TabF_dat (x : Args) (id : BitVec 32) (p : BitVec 64) :
    TabF { x with idAac := id, ready := 1 } p = TabF x p := rfl

omit [CodeEnv] in
theorem test_idA (r : BitVec 64) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r))
      &&& BitVec.setWidth 32 (Int64.toBitVec 4294967293) = BitVec.setWidth 32 r &&& 0xfffffffd#32 := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]; rfl

omit [CodeEnv] in
theorem one32 : (1#32 : BitVec 32) = 1 := rfl

theorem blk_L128 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L128" := by
  cfg_block
  measure_hb "L128"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, hbx, h12, h13, gi, d, ih, hI, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0] at hm
    have hE : s₀.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (LocE t₀) d ih :=
      T_locals (locW0_locE X t₀ gi) _ hm
    simp only [T, DecF, SbrF, SbrS, AcF, sbrA, LocW0, GbR, GbW, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    have p_hE : PLift _ := ⟨hE⟩
    clear hm hE
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hbx, h12, h13, DecF, SbrF, SbrS, AcF, BitVec.add_assoc,
      BitVec.reduceAdd]
    dx_br hm
    all_goals try (simp only [Int.toBytes_length, Nat.reducePow, BitVec.sub_self,
      BitVec.toNat_zero]; omega)
    case vc2 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_31]
      refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, ?_, d, ih, einv_start0 hI ‹_›, hrb.2, ?_⟩, ?_⟩
      all_goals first | assumption | edge_ok var_L4ee | skip
      have h := p_hE.down
      simp only [DecF, SbrF, SbrS, AcF, sbrA, arg0, arg1, arg2,
        BitVec.add_assoc, BitVec.reduceAdd] at h
      sep_close h
      all_goals rfl
    case vc8 =>
      rename_i hz
      simp only [StatusFlags.zf_from_result, Reg64s.get64_set64, reduceCtorEq,
        ite_false, h13, test_idA, beq_iff_eq] at hz
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_15]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, BitVec.setWidth 64 gi, gi, d.dat (idA t₀), ih,
        ⟨sinv_dat hI ‹_›, ?_⟩, hrb, ?_⟩, ?_, ?_, hz⟩, ?_⟩
      all_goals first | exact trivial | edge_ok var_L349 | skip
      all_goals first
        | (dx_run hm [hbp, hsp, h14, hbx, h12, h13, sbrA, arg0, arg1, idZ]; done)
        | skip
      all_goals try (simp only [DS.dat, TabF_dat, idA, arg5, BitVec.reduceSetWidth,
          one32] at hm ⊢; sep_close hm)
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]; simp)
    case vc9 =>
      rename_i hz
      simp only [StatusFlags.zf_from_result, Reg64s.get64_set64, reduceCtorEq,
        ite_false, h13, test_idA, beq_eq_false_iff_ne] at hz
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, BitVec.setWidth 64 gi, gi, d.dat (idA t₀), ih,
        ⟨sinv_dat hI ‹_›, ?_⟩, hrb, ?_⟩, ?_, ?_, ?_, hz⟩, ?_⟩
      all_goals first | exact trivial | rfl | exact Nat.le_of_eq (var_L164 _) | skip
      all_goals try (simp only [DS.dat, TabF_dat, idA, arg5, BitVec.reduceSetWidth,
          one32] at hm ⊢; sep_close hm)

end Kraken.Examples.Sbr.DecExt
