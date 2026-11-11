import Kraken.X64.Examples.Sbr.Parse.DecExtMem

/-!
# `ff_aac_sbr_decode_extension`: the entry blocks (prologue, the copy of the reader, the skip)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_entry (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [BitVec.sub_sub_ofNat]
    case vc7 =>
      refine ⟨⟨hC, ⟨⟨by bv_omega, trivial, trivial⟩, trivial, trivial, trivial⟩, trivial, trivial,
        trivial, ?_⟩, Nat.le_of_eq (var_L21 _)⟩
      sep_close hm

/-- `gbc = *gb_host` (a 16-byte and an 8-byte move across the cells of the struct, `gh_eq`),
`cnt` to its local. -/
theorem blk_L21 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L21" := by
  cfg_block
  measure_hb "L21"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, hdx, hcx, h8, hm⟩, hn⟩ := hs₀
    var_n hn
    have hal := hC.2.2.2.2.2.1
    simp only [T, DecF, gh_eq] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hdx, hbp, h8, hsp, DecF, gh_eq]
    case vc4 => exact al_sub _ 72 hal (by decide)
    case vc7 =>
      simp only [tb_L16, tb_L8] at hm
      rw [L16_split (t₀.regs.get64 .rsp - 72#64) (t₀.regs.get64 .rsp - 64#64)
        (t₀.regs.get64 .rsp - 60#64) X X.i (by bv_omega) (by bv_omega),
        L8_split (t₀.regs.get64 .rsp - 56#64) (t₀.regs.get64 .rsp - 52#64) X (by bv_omega)] at hm
      refine ⟨⟨hC, ⟨⟨trivial, trivial, h14⟩, hdi, h12, h13⟩, trivial, hcx, trivial, ?_⟩, Nat.le_of_eq (var_L36 _)⟩
      sep_close hm

theorem skip_clamp (i p n : BitVec 32) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (i + (if n.toInt < (-i).toInt then -i else if n.toInt < (p - i).toInt then n else p - i)).toNat
      ≤ p.toNat := by
  split
  · rw [BitVec.add_neg_eq_sub, BitVec.sub_self, BitVec.toNat_zero]; omega
  · split
    · rename_i h1 h2
      have e1 : (-i).toInt = - (i.toNat : Int) := by
        rw [BitVec.toInt_neg, BitVec.toInt_eq_toNat_cond]; split <;> rw [Int.bmod_def] <;> split <;> omega
      have e2 : (p - i).toInt = (p.toNat : Int) - i.toNat := by
        rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub]; split <;> omega
      rw [e1] at h1; rw [e2] at h2
      rw [BitVec.toInt_eq_toNat_cond] at h1 h2
      rw [BitVec.toNat_add]
      split at h1 <;> omega
    · rw [BitVec.add_comm, BitVec.sub_add_cancel]; omega


variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L36 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L36" := by
  cfg_block
  measure_hb "L36"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, hdx, hcx, h8, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, GhW] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hdx, hbp, h8, hsp, DecF, GhW]
    simp only [BitVec.setWidth_32_64_32, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt,
      CondCode.interp_l_cmp_toInt32, decide_eq_true_eq] at hm ⊢
    simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have hok := hC.2.2.2.1
    refine ⟨⟨hC, ⟨⟨trivial, trivial, h14⟩, hdi, h12, h13⟩, hcx, _, ⟨hok.1, skip_clamp _ _ (BitVec.setWidth 32 (t₀.regs.get64 .r8 * BitVec.ofNat 64 Width.W64.bytes + 18446744073709551612#64)) hok.1 hok.2.1⟩, ?_⟩, Nat.le_of_eq (var_L63 _)⟩
    sep_close hm

end Kraken.Examples.Sbr.DecExt
