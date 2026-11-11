import Kraken.X64.Examples.Sbr.Parse.EnvBlk11

/-!
# `read_sbr_envelope`: copy C (high resolution after low), the walk entry, the store, the step
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

theorem blk_L5cfd (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5cfd" := by
  cfg_block
  measure_hb "L5cfd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj⟩, hn⟩ := hs₀
    have hn1 : x.n1 ≤ 48 := hC.2.2.1
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
    have p15 : PLift _ := ⟨h15⟩
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
    case vc4 => rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hbl
    case vc5 => rw [h13]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    case vc6 => rw [h13]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    case vc7 =>
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | (with_reducible exact hsp) | (with_reducible exact hbp) | (with_reducible exact hdx) | (with_reducible exact h13) | (with_reducible exact psi.down) | (with_reducible exact p15.down) | (show (_ : BitVec 64) = _; rsimp; exact p12.down) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5daa, var_L5cfd, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)
    case vc8 =>
      rename_i hvs hvl hs _
      rw [h13] at hvs hvl
      simp only [(hld _).1, (hld _).2, Option.some.injEq] at hvs hvl
      subst hvs hvl
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj, ⟨?_, ?_⟩, ?_, ?_, _, hwk _, ?_, ?_, hs⟩, ?_⟩
      all_goals try rsimp
      all_goals first | (with_reducible exact hsp) | (with_reducible exact hbp) | (with_reducible exact hdx) | (with_reducible exact h13) | (with_reducible exact psi.down) | (with_reducible exact p15.down) | (show (_ : BitVec 64) = _; rsimp; exact p12.down) | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5d35, var_L5cfd, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)

theorem blk_L5daa (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5daa" := by
  cfg_block
  measure_hb "L5daa"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj, ⟨hix, hlim⟩⟩, hn⟩ := hs₀
    have hn1 : x.n1 ≤ 48 := hC.2.2.1
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hst := T_gb_st hm
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
    have p15 : PLift _ := ⟨h15⟩
    have plim : PLift _ := ⟨hlim⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    all_goals try simp only [e58, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    · exact ei
    case vc2 =>
      rename_i hz; exfalso
      rw [z_sub_iff, psi.down] at hz
      have := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat, show (BitVec.setWidth 64 (Int64.toBitVec 48)).toNat = 48 from rfl,
        Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at this
      omega
    · exact hL _
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, _, ⟨hC, ?_, ?_, ?_, hS _ _⟩, hFC.2.2.2.2.2.1⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rw [BitVec.setWidth_32_64_32, plim.down]; exact gb_clamp _ _ _ _
      · show (0 : Nat) < _
        rw [var_L5daa, psi.down, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
        omega
    · refine ⟨⟨fv, _, i, j, ⟨⟨⟨hC, ?_, ?_, ?_, hS _ _⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, hj⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · first | (rw [BitVec.setWidth_32_64_32, plim.down]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _)
      · exact hdx
      · exact p13.down
      · exact p12.down
      · exact p15.down
      · exact psi.down
      · rw [var_L5dd7, var_L5daa, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb (hS _ _)]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

theorem blk_L5dd7 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5dd7" := by
  cfg_block
  measure_hb "L5dd7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨h48, hfr1, h15, hsi⟩, hj⟩, hn⟩ := hs₀
    have hn1 : x.n1 ≤ 48 := hC.2.2.1
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hl48 := T_ld_f48 hm
    rw [h48] at hl48
    have hl38 := T_ld_f38 hm
    rw [hFC.2.2.2.2.2.2.2] at hl38
    have hfrl := T_ld_fr hm hC (i + 1) 0 (by omega) 12 rfl
    have hf1 : (x.v.freqRes.getD (i + 1) 0).toNat = 1 := hfr1
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hbp, hl48]; rfl
    · rename_i v48 hv48
      rsimp at hv48; rw [hbp, hl48] at hv48; cases hv48
      rsimp; rw [hbp, hl38]; rfl
    · rename_i v48 hv48 v38 hv38
      rsimp at hv48 hv38; rw [hbp, hl48] at hv48; cases hv48
      rw [hbp, hl38] at hv38; cases hv38
      rsimp; simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      rw [hfrl]; rfl
    all_goals rename_i v48 hv48 v38 hv38 vf hvf hc
    all_goals rsimp at hv48 hv38 hvf
    all_goals rw [hbp, hl48] at hv48; cases hv48
    all_goals rw [hbp, hl38] at hv38; cases hv38
    all_goals simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hvf
    all_goals rw [hfrl] at hvf; cases hvf
    all_goals rsimp at hc
    all_goals try rw [zx8] at hc
    all_goals try simp only [Nat.add_zero] at hc
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j + 1, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, hfr1, ?_, ?_⟩, by omega, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h15
      · rsimp; rw [hsi]; exact (BitVec.ofNat_add j 1).symm
      · rsimp; rw [zx8, hf1]; rfl
      · rw [var_L5cd0, var_L5dd7, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); rw [hsi, show BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) from
          (BitVec.ofNat_add j 1).symm]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · exfalso
      rw [hf1] at hc; revert hc; decide
