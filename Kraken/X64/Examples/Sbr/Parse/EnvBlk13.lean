import Kraken.X64.Examples.Sbr.Parse.EnvBlk11

/-!
# `read_sbr_envelope`: copy C (high resolution after low), the band loop
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

theorem idx_half (j o : Nat) (h : j + o < 2 ^ 32) :
    BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 j) + BitVec.setWidth 32 (BitVec.ofNat 64 o)))).ushiftRight
        ((Int64.toBitVec 1).toNat % 256 % 32)) = BitVec.ofNat 64 ((j + o) / 2) := by
  have e : BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 j) + BitVec.setWidth 32 (BitVec.ofNat 64 o)))
      = BitVec.ofNat 32 (j + o) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e, show (Int64.toBitVec 1).toNat % 256 % 32 = 1 from rfl]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, show (BitVec.ofNat 32 (j + o)).ushiftRight 1
    = BitVec.ofNat 32 (j + o) >>> 1 from rfl, BitVec.toNat_ushiftRight]
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

variable [CodeEnv]

theorem blk_L5cd0 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5cd0" := by
  cfg_block
  measure_hb "L5cd0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj, hax⟩, hn⟩ := hs₀
    have hn1 : x.n1 ≤ 48 := hC.2.2.1
    have hl : s₀.dmem.loadInt (arg1 t₀ + 0x4c1e0#64
        + BitVec.setWidth 64 (BitVec.setWidth 32 (1#8)) * 4#64 + Int64.toBitVec 0) 4
        = some (Int.ofBytes (Int.toBytes 4 (x.n1 : Int))) := by
      rw [show arg1 t₀ + 0x4c1e0#64 + BitVec.setWidth 64 (BitVec.setWidth 32 (1#8)) * 4#64
          + Int64.toBitVec 0 = arg1 t₀ + 0x4c1e4#64 by
        rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (1#8)) * 4#64 = 4#64 from rfl,
          show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
        bv_omega]
      exact T_ld_n1 hm
    have hl90 := T_ld_f90 hm
    rw [hFC.2.1] at hl90
    have e90 : loadInt s₀.dmem (s₀.regs.get64 .rbp + Int64.toBitVec (-144)) 8
        = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 (96 - odd x)).toInt)) := by
      rw [hbp]; exact hl90
    have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (x.n1 : Int))))
        = BitVec.ofNat 64 x.n1 := by
      rw [c4_val]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hodd : odd x ≤ 1 := by simp only [odd]; omega
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hax, h12]; exact Option.isSome_iff_exists.mpr ⟨_, hl⟩
    case' vc2 v hv' hc => skip
    case' vc3 v hv' hc => skip
    case' vc4 v hv' hc w hw hz => skip
    case' vc5 v hv' hc w hw hz => skip
    all_goals rsimp at hv' hc
    all_goals rw [hax, h12, hl] at hv'; cases hv'
    all_goals rw [CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl] at hc
    all_goals rw [hsi, hv] at hc
    all_goals simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
      decide_eq_false_iff_not, BitVec.toNat_ofNat] at hc
    all_goals rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
    case vc2.refl =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_⟩,
        Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rw [var_L5f90, var_L5cd0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        rw [hsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
    case vc3.refl =>
      rsimp; rw [e90]; rfl
    all_goals rsimp at hw hz
    all_goals rw [e90] at hw; cases hw
    all_goals simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hz
    case vc4.refl =>
      exfalso
      rw [z_sub_iff, hsi] at hz
      have := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
    case vc5.refl =>
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, by omega⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h15
      · rsimp; exact hsi
      · rw [var_L5ced, var_L5cd0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

theorem blk_L5ced (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5ced" := by
  cfg_block
  measure_hb "L5ced"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj⟩, hn⟩ := hs₀
    have hn1 : x.n1 ≤ 48 := hC.2.2.1
    have hl88 := T_ld_f88 hm
    rw [hFC.2.2.1] at hl88
    have hel := T_efq_ld hm
    have e88 : loadInt s₀.dmem (s₀.regs.get64 .rbp + Int64.toBitVec (-136)) 8
        = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 (odd x)).toInt)) := by
      rw [hbp]; exact hl88
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hin : (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * i)
        + BitVec.ofNat 64 ((j + x.n1 % 2) / 2) + Int64.toBitVec 0
        - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by
      simp only [arg3]; rw [efq_r9 _ _ _ (by omega)]; omega
    have hif1 : ((Int64.toBitVec 1).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have p15 : PLift _ := ⟨h15⟩
    have psi : PLift _ := ⟨hsi⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif1, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [e88, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    all_goals try simp only [h15, hsi, idx_half j (x.n1 % 2) (by omega)] at *
    · exact hel _ 1 hin
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj⟩, ?_⟩
      all_goals try rsimp
      all_goals first | (with_reducible exact hsp) | (with_reducible exact hbp) | (with_reducible exact hdx) | (with_reducible exact p13.down) | (with_reducible exact psi.down) | (with_reducible exact p15.down) | (show (_ : BitVec 64) = _; rsimp; exact p12.down) | skip
      rw [var_L5cfd, var_L5ced, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5d35 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5d35" := by
  cfg_block
  measure_hb "L5d35"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj, ⟨hix, hlim⟩, hbuf, htab, e, hW, hax, h10, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀) 2 _
      (vlc_walk_next hW hneg w)
    have hbl := fun (o : BitVec 32) (ho : o.toNat ≤ x.p8.toNat) =>
      T_buf_ld hm _ 4 (rd_off o x.p8 x.L ho hC.2.2.2.2.2.1)
    have plim : PLift _ := ⟨hlim⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have pbuf : PLift _ := ⟨hbuf⟩
    have ptab : PLift _ := ⟨htab⟩
    have psi : PLift _ := ⟨hsi⟩
    have p15 : PLift _ := ⟨h15⟩
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_lo]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [BitVec.setWidth_32_64_32, hlim, hbuf, htab, hix,
      show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
      show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero] at *
    · exact hbl _ (gb_clamp _ _ _ _)
    · rename_i hv _
      rw [vlc_key hax h10 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · rename_i hv _ _
      rw [vlc_key hax h10 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · rename_i hv hbuf' hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self,
        BitVec.msb_signExtend, decide_true, Bool.true_and, Nat.reduceLT] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj, ⟨?_, ?_⟩, ?_, ?_, _, vlc_walk_next hW hneg _, ?_, ?_, hs⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | (with_reducible exact hsp) | (with_reducible exact hbp) | (with_reducible exact hdx) | (with_reducible exact p13.down) | (with_reducible exact psi.down) | (with_reducible exact p15.down) | (with_reducible exact plim.down) | (with_reducible exact pbuf.down) | (with_reducible exact ptab.down) | (show (_ : BitVec 64) = _; rsimp; exact p12.down) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (with_reducible exact BitVec.setWidth_32_64_32 _) | skip
      rw [var_L5d75, var_L5d35, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)
    · rename_i hv hbuf' hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | (with_reducible exact hsp) | (with_reducible exact hbp) | (with_reducible exact hdx) | (with_reducible exact p13.down) | (with_reducible exact psi.down) | (with_reducible exact p15.down) | (with_reducible exact plim.down) | (with_reducible exact pbuf.down) | (with_reducible exact ptab.down) | (show (_ : BitVec 64) = _; rsimp; exact p12.down) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (with_reducible exact BitVec.setWidth_32_64_32 _) | skip
      rw [var_L5da6, var_L5d35, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)

theorem blk_L5d75 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5d75" := by
  cfg_block
  measure_hb "L5d75"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj, ⟨hix, hlim⟩, hbuf, htab, e, hW, hax, h11, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀) 1 _
      (vlc_walk_next hW hneg w)
    have hbl := fun (o : BitVec 32) (ho : o.toNat ≤ x.p8.toNat) =>
      T_buf_ld hm _ 4 (rd_off o x.p8 x.L ho hC.2.2.2.2.2.1)
    have plim : PLift _ := ⟨hlim⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have psi : PLift _ := ⟨hsi⟩
    have p15 : PLift _ := ⟨h15⟩
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_lo]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [BitVec.setWidth_32_64_32, hlim, hbuf, htab, hix,
      show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
      show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero] at *
    · exact hbl _ (gb_clamp _ _ _ _)
    · rename_i hv _
      rw [vlc_key hax h11 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · rename_i hv _ _
      rw [vlc_key hax h11 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj, ⟨?_, ?_⟩⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p15.down | exact p12.down | exact plim.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5da6, var_L5d75, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5da6 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5da6" := by
  cfg_block
  measure_hb "L5da6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      hJ, hj, hW⟩, hn⟩ := hs₀
    have hl := T_ld_f2c hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · (try rsimp); rw [hbp]; exact hl
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, hj, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact h12 | exact hJ | exact hJ.2.2.1 | exact hJ.2.2.2 | exact hW.1 | exact hW.2 | skip
      rw [var_L5daa, var_L5da6, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
