import Kraken.X64.Examples.Sbr.Parse.DecExtMem

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the CRC skip, the push of `kx`/`m`, the header bit
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- `get_bits1`'s index update (`cmp; setl; add`) stays within `size_in_bits_plus8`. -/
theorem setl_inc (a p x : BitVec 32) (cf af : Bool) (ha : a.toNat ≤ p.toNat)
    (hp : p.toNat < 2 ^ 31) :
    (a + BitVec.setWidth 32 ((BitVec.setWidth 64 (x ^^^ x)).replaceLow
      (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (a - p)
        { cf := cf, af := af, of := (a - p).signed != a.signed - p.signed })).toNat))).toNat
      ≤ p.toNat := by
  rw [CondCode.interp_l_cmp_toInt32, BitVec.xor_self, BitVec.toInt_eq_toNat_cond,
    BitVec.toInt_eq_toNat_cond]
  rw [if_pos (by omega), if_pos (by omega)]
  by_cases h : a.toNat < p.toNat
  · rw [decide_eq_true (by omega)]
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]
    simp only [BitVec.setWidth_zero, BitVec.toNat_zero, Nat.zero_div, Nat.zero_mul,
      Nat.zero_add, Bool.toNat_true, BitVec.toNat_ofNat]
    omega
  · rw [decide_eq_false (by omega)]
    rw [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]
    simp only [BitVec.setWidth_zero, BitVec.toNat_zero, Nat.zero_div, Nat.zero_mul,
      Nat.zero_add, Bool.toNat_false, BitVec.toNat_ofNat]
    omega

theorem blk_L8b (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L8b" := by
  cfg_block
  measure_hb "L8b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hcx⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, GbR, GbW] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, h12, hcx, DecF]
    dx_br hm
    dx_run hm [hbp, hsp, h14, hdi, h12, hcx, DecF]
    simp only [interp_c_sub32, decide_eq_true_eq]
    refine ⟨⟨⟨hC, ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, h13⟩, gi, ih, hrb, ?_⟩, ?_, ?_⟩,
      Nat.le_of_eq (var_Lad _)⟩
    · sep_close hm
    · exact min_le _ _ _ _ hrb.1
    · first | trivial | rfl

theorem blk_Lad (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lad" := by
  cfg_block
  measure_hb "Lad"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hax, hsi⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, DS.st1, TabF_st1, BitVec.add_assoc,
      BitVec.reduceAdd, newRate] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, h12, hsi, DecF, SbrF, SbrS, AcF, DS.pro, TabF_pro,
      BitVec.add_assoc, BitVec.reduceAdd]
    dx_br hm
    simp only [extPro, BitVec.ofNat_eq_ofNat]
    simp only [tb4_ofInt, BitVec.reduceSetWidth, BitVec.ofNat_eq_ofNat] at hm
    refine ⟨⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, gi, ih, hrb, ?_⟩, ?_, ?_⟩, Nat.le_of_eq (var_Ld4 _)⟩
    all_goals first | assumption | trivial | sep_close hm

theorem blk_Ld4 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Ld4" := by
  cfg_block
  measure_hb "Ld4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hax, hsi⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF] at hm
    have hax32 : (BitVec.setWidth 32 (s₀.regs.get64 .rax)).toNat ≤ X.r.p8.toNat := by
      rw [BitVec.toNat_setWidth]; have := hC.2.2.2.1.2.1; omega
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, h12, hsi, DecF]
    dx_br hm
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Width.bytes,
      BitVec.ofNat_eq_ofNat, BitVec.mul_one] at *
    case vc2 =>
      sep_mem hm
      rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
      exact rd_off1 _ _ _ hax32 hC.2.2.2.1.2.2.1
    case vc4 =>
      rename_i s _ _ _ _ _ _ _ _ _ _ _ _
      have hg := setl_inc (BitVec.setWidth 32 (s.regs.get64 .rax)) X.r.p8
        (BitVec.setWidth 32 (s.regs.get64 .r8))
        ((BitVec.setWidth 32 (s.regs.get64 .rax) - X.r.p8).unsigned !=
          (BitVec.setWidth 32 (s.regs.get64 .rax)).unsigned - X.r.p8.unsigned)
        (((BitVec.setWidth 32 (s.regs.get64 .rax) - X.r.p8).take 4).unsigned !=
          ((BitVec.setWidth 32 (s.regs.get64 .rax)).take 4).unsigned - (X.r.p8.take 4).unsigned)
        hax32 hC.2.2.2.1.2.1
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_11]
      refine ⟨by decide, ?_, ?_⟩
      · refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, _, ih, ⟨hg, hrb.2⟩, ?_⟩
        all_goals first | assumption | trivial | sep_close hm
      · edge_ok var_L333
    case vc5 =>
      rename_i s _ _ _ _ _ _ _ _ _ _ _ _
      have hg := setl_inc (BitVec.setWidth 32 (s.regs.get64 .rax)) X.r.p8
        (BitVec.setWidth 32 (s.regs.get64 .r8))
        ((BitVec.setWidth 32 (s.regs.get64 .rax) - X.r.p8).unsigned !=
          (BitVec.setWidth 32 (s.regs.get64 .rax)).unsigned - X.r.p8.unsigned)
        (((BitVec.setWidth 32 (s.regs.get64 .rax) - X.r.p8).take 4).unsigned !=
          ((BitVec.setWidth 32 (s.regs.get64 .rax)).take 4).unsigned - (X.r.p8.take 4).unsigned)
        hax32 hC.2.2.2.1.2.1
      refine ⟨⟨hC, ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, h13⟩, _, ih, ⟨hg, hrb.2⟩, ?_⟩,
        by rw [var_Lff]; omega⟩
      sep_close hm


/-- After the prologue (`reset = 0`) `MI` still holds: the invariant at `read_sbr_data`. -/
theorem inv2_pro {PI : List UInt8 → Prop} {X : XA} {t : MachineData} (hC : DecCI PI X t) :
    Inv2 PI X (X.d.pro X.sr) :=
  ⟨mi_extPro _ _ hC.1, hC.2.1, hC.2.2.1, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hC.2.2.2.2.2.2.1⟩

omit [CodeEnv] in
theorem pro_reset (d : DS) (sr : BitVec 32) : (d.pro sr).a.reset = 0 := rfl

theorem blk_L333 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L333" := by
  cfg_block
  measure_hb "L333"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    case' vc3 => left; apply Table.ofLabels_at; rw [table.match_1.eq_14]
    dx_run hm [hbp, hsp, h14, hdi, h12, DecF, SbrF, SbrS, AcF, BitVec.add_assoc, BitVec.reduceAdd,
      pro_reset]
    dx_br hm
    case vc2 => exact absurd rfl ‹_›
    case vc3 =>
      refine ⟨by decide, ?_, ?_⟩
      · refine ⟨hC, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, gi, X.d.pro X.sr, ih, inv2_pro hC, hrb, ?_⟩
        all_goals first
          | (dx_run hm [hbp, hsp, h14, hdi, h12, h13, sbrA, arg0, arg1, idZ]; done)
          | ((try simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, BitVec.add_assoc, BitVec.reduceAdd])
             sep_close hm)
      · edge_ok var_L128


omit [CodeEnv] in
/-- `HI` with no reset pending is `MI`. -/
theorem mi_of_hi0 {s : St} (h : HI s) (hr : s.1.reset = 0) : MI s := by
  obtain ⟨a1, a2, -, a3, a4, a5, a6, i1⟩ := h
  exact ⟨⟨a1, a2 hr, a3, a4, a5, a6⟩, i1⟩

theorem blk_L10d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L10d" := by
  cfg_block
  measure_hb "L10d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, hbx, h12, h13, gi, d, ih, hI, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    case' vc2 => left; apply Table.ofLabels_at; rw [table.match_1.eq_14]
    dx_run hm [hbp, hsp, h14, hbx, h12, h13, DecF, SbrF, SbrS, AcF, BitVec.add_assoc,
      BitVec.reduceAdd]
    dx_br hm
    case vc2 =>
      refine ⟨by decide, ?_, ?_⟩
      · refine ⟨hC, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, gi, d, ih,
          ⟨mi_of_hi0 hI.1 ‹_›, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2.1⟩, hrb, ?_⟩
        all_goals first
          | (dx_run hm [hbp, hsp, h14, hbx, h12, h13, sbrA, arg0, arg1, idZ]; done)
          | ((try simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, BitVec.add_assoc, BitVec.reduceAdd])
             sep_close hm)
      · edge_ok var_L128
    case vc3 =>
      refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, gi, d, ih, ⟨hI, ‹_›⟩, hrb, ?_⟩, Nat.le_of_eq (var_L11d _)⟩
      all_goals first
        | trivial
        | assumption
        | (dx_run hm [hbp, hsp, h14, hbx, h12, h13, sbrA, arg0, arg1, idZ]; done)
        | (simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, BitVec.add_assoc, BitVec.reduceAdd]
           sep_close hm)

end Kraken.Examples.Sbr.DecExt
