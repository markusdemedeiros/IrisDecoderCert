import Kraken.X64.Examples.Sbr.Parse.EnvBlk8

/-!
# `read_sbr_envelope`: copy A (time delta, same resolution), the band loop
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

/-- `sbr->n[bs_freq_res[e]]`, loaded through `r12 + 4 * fr`. -/
theorem T_ld_nf {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {gi : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv gi) (e : Nat)
    (hfr : u8 x.v.freqRes e = 0 ∨ u8 x.v.freqRes e = 1) :
    m.loadInt (arg1 t₀ + 0x4c1e0#64
        + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (fr x e))) * 4#64
        + Int64.toBitVec 0) 4
      = some (Int.ofBytes (Int.toBytes 4 (nf x e : Int))) := by
  rcases hfr with hf | hf
  · simp only [fr, nf, hf, ↓reduceIte]
    rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 0#64)) * 4#64 = 0#64 from rfl,
      show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, BitVec.add_zero]
    exact T_ld_n0 h
  · simp only [fr, nf, hf, ↓reduceIte, show (1 : Nat) ≠ 0 by omega]
    rw [show arg1 t₀ + 0x4c1e0#64
        + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 1))) * 4#64
        + Int64.toBitVec 0 = arg1 t₀ + 0x4c1e4#64 by
      rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 1)))
        * 4#64 = 4#64 from rfl, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
      bv_omega]
    exact T_ld_n1 h

omit [CodeEnv] in
theorem nf_le (x : EArgs) (e : Nat) (h0 : x.n0 ≤ 24) (h1 : x.n1 ≤ 48) : nf x e ≤ 48 := by
  simp only [nf]; split <;> omega

theorem blk_L5940 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5940" := by
  cfg_block
  measure_hb "L5940"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h48, hsi,
      hj, hax⟩, hn⟩ := hs₀
    have hi := hLI.1
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hfr : u8 x.v.freqRes (i + 1) = 0 ∨ u8 x.v.freqRes (i + 1) = 1 := by
      have := hC.1.2.2.2.2.2.1 (i + 1) (by omega); omega
    have hnf := nf_le x (i + 1) hC.2.1 hC.2.2.1
    have hl := T_ld_nf hm (i + 1) hfr
    have hv : BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (nf x (i + 1) : Int))))
        = BitVec.ofNat 64 (nf x (i + 1)) := by
      rw [c4_val]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hax, h12]; exact Option.isSome_iff_exists.mpr ⟨_, hl⟩
    case' vc2 v hv' hc => skip
    case' vc3 v hv' hc hz => revert hz
    case' vc4 v hv' hc hz => revert hz
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
      · rw [var_L5f90, var_L5940, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        rw [hsi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
    case vc3.refl =>
      intro hz; exfalso
      rsimp at hz
      rw [z_sub_iff, hsi] at hz
      have := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat, show (BitVec.setWidth 64 (Int64.toBitVec 48)).toNat = 48 from rfl,
        Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at this
      omega
    case vc4.refl =>
      intro hz
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, h48, ?_, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact hsi
      · omega
      · rw [var_L595a, var_L5940, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

omit [CodeEnv] in
theorem efq_prev (b : BitVec 64) (i j : Nat) (hc : 48 * i + j < 2 ^ 32) :
    (b + 86496#64 + BitVec.ofNat 64 (48 * (i + 1)) + BitVec.ofNat 64 j
      + Int64.toBitVec (-48) - (b + 0x151e0#64)).toNat = 48 * i + j := by
  have e1 : BitVec.ofNat 64 (48 * (i + 1)) = BitVec.ofNat 64 (48 * i) + 48#64 := by
    rw [show 48 * (i + 1) = 48 * i + 48 by omega, BitVec.ofNat_add]
  rw [e1, show Int64.toBitVec (-48) = 0xffffffffffffffd0#64 from rfl,
    show b + 86496#64 + (BitVec.ofNat 64 (48 * i) + 48#64) + BitVec.ofNat 64 j
      + 0xffffffffffffffd0#64 - (b + 0x151e0#64) = BitVec.ofNat 64 (48 * i) + BitVec.ofNat 64 j
      by bv_omega]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem blk_L595a (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L595a" := by
  cfg_block
  measure_hb "L595a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hsi, hj⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hl58 := T_ld_f58 hm
    rw [hLI.2.1] at hl58
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hel := T_efq_ld hm
    have hld := vlc_l1 hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀)
    have hwk := fun w : BitVec 32 => vlc_walk1 (hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀)) (idx1_lt w)
    have hin : (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1))
        + BitVec.ofNat 64 j + Int64.toBitVec (-48) - (arg3 t₀ + 0x151e0#64)).toNat + 1
        ≤ 432 := by
      simp only [arg3]; rw [efq_prev _ _ _ (by omega)]; omega
    have e58 : loadInt s₀.dmem (s₀.regs.get64 .rbp + (-88 : Int64).toBitVec) 8
        = some (Int.ofBytes (Int.toBytes 8
            (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1))).toInt)) := by
      rw [hbp]; exact hl58
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
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    have hif23 : ((Int64.toBitVec 23).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, hif23, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [e58, ei, ep, eb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq] at *
    case vc2 => rw [hsi]; exact hel _ 1 hin
    case vc6 => rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hbl
    case vc7 => rw [h13]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    case vc8 => rw [h13]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    case vc9 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, ?_, hj⟩, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact hsi | exact p12.down | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5a11, var_L595a, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)
    case vc10 =>
      rename_i hvs hvl hs _ _
      rw [h13] at hvs hvl
      simp only [(hld _).1, (hld _).2, Option.some.injEq] at hvs hvl
      subst hvs hvl
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, ?_, hj⟩, ⟨?_, ?_⟩, ?_, ?_, _, hwk _, ?_, ?_, hs⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact hsi | exact p12.down | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5998, var_L595a, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)

theorem blk_L5998 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5998" := by
  cfg_block
  measure_hb "L5998"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hsi, hj⟩, ⟨hix, hlim⟩, hbuf, htab, e, hW, hax, h10, hneg⟩, hn⟩ := hs₀
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
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, ?_, hj⟩, ⟨?_, ?_⟩, ?_, ?_, _, vlc_walk_next hW hneg _, ?_, ?_, hs⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L59d8, var_L5998, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)
    · rename_i hv hbuf' hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, ?_, hj⟩, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | exact pbuf.down | exact ptab.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5a0d, var_L5998, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)

theorem blk_L59d8 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L59d8" := by
  cfg_block
  measure_hb "L59d8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hsi, hj⟩, ⟨hix, hlim⟩, hbuf, htab, e, hW, hax, h11, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀) 1 _
      (vlc_walk_next hW hneg w)
    have hbl := fun (o : BitVec 32) (ho : o.toNat ≤ x.p8.toNat) =>
      T_buf_ld hm _ 4 (rd_off o x.p8 x.L ho hC.2.2.2.2.2.1)
    have plim : PLift _ := ⟨hlim⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
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
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, ?_, hj⟩, ⟨?_, ?_⟩⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact psi.down | exact p12.down | exact plim.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5a0d, var_L59d8, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5a0d (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5a0d" := by
  cfg_block
  measure_hb "L5a0d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      hJ, hW⟩, hn⟩ := hs₀
    have hl := T_ld_f2c hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · (try rsimp); rw [hbp]; exact hl
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJ, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact h12 | exact hJ | exact hW.1 | exact hW.2 | skip
      rw [var_L5a11, var_L5a0d, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5a11 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5a11" := by
  cfg_block
  measure_hb "L5a11"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hsi, hj⟩, ⟨hix, hlim⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    have hl38 := T_ld_f38 hm
    rw [h38] at hl38
    have hst := T_gb_st hm
    have e38 : loadInt s₀.dmem (s₀.regs.get64 .rbp + Int64.toBitVec (-56)) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rcx).toInt)) := by
      rw [hbp]; exact hl38
    have e58 : ∀ v : BitVec 32, loadInt (storeInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4
        v.toInt) (s₀.regs.get64 .rbp + Int64.toBitVec (-88)) 8
        = some (Int.ofBytes (Int.toBytes 8 (EQ t₀ + BitVec.ofNat 64 (48 * (i + 1))).toInt)) := by
      intro v; rw [hbp, hdx, show Int64.toBitVec 8 = 8#64 from rfl, T_ld_f58 (hst v), hLI.2.1]
    have hrow : (t₀.regs.get64 .rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1))
        + s₀.regs.get64 .rsi + Int64.toBitVec 0 - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by
      rw [hsi]; simp only [arg3]; rw [efq_r9 _ _ _ (by omega)]; omega
    have hS : ∀ (v : BitVec 32) (b : Int), storeInt (storeInt s₀.dmem
        (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4 v.toInt) (t₀.regs.get64 .rcx + 86496#64
        + BitVec.ofNat 64 (48 * (i + 1)) + s₀.regs.get64 .rsi + Int64.toBitVec 0) 1 b
        =⋆ T k Ext x ra t₀ fv v := by
      intro v b; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_efq_st (hst v) _ 1 hrow b
    have hL : ∀ (v : BitVec 32), (loadInt (storeInt s₀.dmem
        (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4 v.toInt) (t₀.regs.get64 .rcx + 86496#64
        + BitVec.ofNat 64 (48 * (i + 1)) + s₀.regs.get64 .rsi + Int64.toBitVec 0) 1).isSome
        = true := by
      intro v; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_efq_ld (hst v) _ 1 hrow
    have ei : (loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4).isSome = true := by
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, T_gb_idx hm]; rfl
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
    all_goals try simp only [e38, e58, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    · exact ei
    · exact hL _
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, _, ⟨hC, ?_, ?_, ?_, hS _ _⟩, hFC.2.2.2.2.2.1⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rw [BitVec.setWidth_32_64_32, plim.down]; exact gb_clamp _ _ _ _
      · show (0 : Nat) < _
        rw [var_L5a11, psi.down, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
        omega
    · refine ⟨⟨fv, _, i, j, ⟨⟨⟨hC, ?_, ?_, ?_, hS _ _⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, ?_, hj⟩, ?_⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · first | (rw [BitVec.setWidth_32_64_32, plim.down]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _)
      · exact hdx
      · exact p13.down
      · exact p12.down
      · exact psi.down
      · rw [var_L5a38, var_L5a11, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb (hS _ _)]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

theorem blk_L5a38 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5a38" := by
  cfg_block
  measure_hb "L5a38"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hsi, hj⟩, hcx⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hfr : u8 x.v.freqRes (i + 1) = 0 ∨ u8 x.v.freqRes (i + 1) = 1 := by
      have := hC.1.2.2.2.2.2.1 (i + 1) (by omega); omega
    have hl48 := T_ld_f48 hm
    rw [h48] at hl48
    have hfrl := T_ld_fr hm hC (i + 1) 0 (by omega) 12 rfl
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hbp, hl48]; rfl
    · rename_i v48 hv48
      rsimp at hv48; rw [hbp, hl48] at hv48; cases hv48
      rsimp; simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      rw [hcx, hfrl]; rfl
    all_goals rename_i v48 hv48 vf hvf hc
    all_goals rsimp at hv48 hvf
    all_goals rw [hbp, hl48] at hv48; cases hv48
    all_goals simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hvf
    all_goals rw [hcx, hfrl] at hvf; cases hvf
    all_goals rsimp at hc
    all_goals try rw [zx8] at hc
    all_goals try simp only [Nat.add_zero] at hfr hc
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j + 1, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        h48, ?_, by omega, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; rw [hsi]; exact (BitVec.ofNat_add j 1).symm
      · rsimp; rw [zx8]
      · rw [var_L5940, var_L5a38, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); rw [hsi, show BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) from
          (BitVec.ofNat_add j 1).symm]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · exfalso
      rcases hfr with h | h <;> rw [h] at hc <;> revert hc <;> decide

end Kraken.Examples.Sbr.Env
