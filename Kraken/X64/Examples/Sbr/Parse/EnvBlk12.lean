import Kraken.X64.Examples.Sbr.Parse.EnvBlk8

/-!
# `read_sbr_envelope`: the first band of the low-resolution path, copy C
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

theorem blk_L5c26 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5c26" := by
  cfg_block
  measure_hb "L5c26"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD, hsi⟩,
      hn⟩ := hs₀
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hld := vlc_l1 hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀)
    have hwk := fun w : BitVec 32 => vlc_walk1 (hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀)) (idx1_lt w)
    have ei : loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4
        = some (Int.ofBytes (Int.toBytes 4 gi.toInt)) := by
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact hli
    have ep : loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 16) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl]; exact hlp
    have eb : loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 0) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hlb
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have psi : PLift _ := ⟨hsi⟩
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    have hif23 : ((Int64.toBitVec 23).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, hif23, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [ei, ep, eb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq] at *
    · rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hbl
    · rw [p13.down]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · rw [p13.down]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ?_, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5e2d, var_L5c26, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp)
    · rename_i hvs hvl hs _
      rw [p13.down] at hvs hvl
      simp only [(hld _).1, (hld _).2, Option.some.injEq] at hvs hvl
      subst hvs hvl
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ?_, ⟨?_, ?_⟩, ?_, ?_, _, hwk _, ?_, ?_, hs⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5c5e, var_L5c26, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)

theorem blk_L5c5e (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5c5e" := by
  cfg_block
  measure_hb "L5c5e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD, hsi,
      ⟨hix, hlim⟩, hbuf, htab, e, hW, hax, h10, hneg⟩, hn⟩ := hs₀
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
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ?_, ⟨?_, ?_⟩, ?_, ?_, _, vlc_walk_next hW hneg _, ?_, ?_, hs⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5df4, var_L5c5e, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)
    · rename_i hv hbuf' hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ?_, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5e29, var_L5c5e, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)

theorem blk_L5df4 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5df4" := by
  cfg_block
  measure_hb "L5df4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD, hsi,
      ⟨hix, hlim⟩, hbuf, htab, e, hW, hax, h11, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀) 1 _
      (vlc_walk_next hW hneg w)
    have hbl := fun (o : BitVec 32) (ho : o.toNat ≤ x.p8.toNat) =>
      T_buf_ld hm _ 4 (rd_off o x.p8 x.L ho hC.2.2.2.2.2.1)
    have plim : PLift _ := ⟨hlim⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have pbuf : PLift _ := ⟨hbuf⟩
    have ptab : PLift _ := ⟨htab⟩
    have psi : PLift _ := ⟨hsi⟩
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
    · refine ⟨⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ?_, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5e29, var_L5df4, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5e29 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5e29" := by
  cfg_block
  measure_hb "L5e29"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD, hsi,
      hW⟩, hn⟩ := hs₀
    have hl := T_ld_f2c hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · (try rsimp); rw [hbp]; exact hl
    · refine ⟨⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD, ?_, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact h12 | exact hsi | exact hW.1 | exact hW.2 | skip
      rw [var_L5e2d, var_L5e29, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5e2d (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5e2d" := by
  cfg_block
  measure_hb "L5e2d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD, hsi,
      ⟨hix, hlim⟩⟩, hn⟩ := hs₀
    have hst := T_gb_st hm
    have ei : (loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4).isSome = true := by
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, T_gb_idx hm]; rfl
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hrow : (s₀.regs.get64 .rsi + Int64.toBitVec 0 - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by
      rw [hsi, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; simp only [arg3]
      rw [show t₀.regs.get64 .rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1))
        - (t₀.regs.get64 .rcx + 0x151e0#64) = BitVec.ofNat 64 (48 * (i + 1)) by bv_omega,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 48 * (i + 1) < 2 ^ 64 by omega)]
      omega
    have hS : ∀ (v : BitVec 32) (b : Int), storeInt (storeInt s₀.dmem
        (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4 v.toInt) (s₀.regs.get64 .rsi + Int64.toBitVec 0) 1 b
        =⋆ T k Ext x ra t₀ fv v := by
      intro v b; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_efq_st (hst v) _ 1 hrow b
    have hL : ∀ (v : BitVec 32), (loadInt (storeInt s₀.dmem
        (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4 v.toInt) (s₀.regs.get64 .rsi + Int64.toBitVec 0) 1).isSome
        = true := by
      intro v; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_efq_ld (hst v) _ 1 hrow
    have psi : PLift _ := ⟨hsi⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have plim : PLift _ := ⟨hlim⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    · exact ei
    · first | exact hL _ | (simp only [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero] at hL; exact hL _)
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, _, ⟨hC, ?_, ?_, ?_, hS _ _⟩, hFC.2.2.2.2.2.1⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rw [BitVec.setWidth_32_64_32, plim.down]; exact gb_clamp _ _ _ _
      · show (0 : Nat) < _
        rw [var_L5e2d]
        have := fi_eq hbp hmT; have := h68
        simp only [fi_eq hbp hmT, h68, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
    · refine ⟨⟨fv, _, i, ⟨⟨⟨hC, ?_, ?_, ?_, hS _ _⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · first | (rw [BitVec.setWidth_32_64_32, plim.down]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _)
      · exact hdx
      · exact p13.down
      · exact p12.down
      · rw [var_L5e4b, var_L5e2d, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb (hS _ _)]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
