import Kraken.X64.Examples.Sbr.Parse.EnvBlk11

/-!
# `read_sbr_envelope`: copy B (frequency delta), the band loop (`L5ad0` … `L5bc7`)

`f_huff` (`fH x t₀`, pointer in the slot at `rbp - 0x98`), band `j + 1` with `j` in `r9`,
`i + 1` in `rbx`, the row `env_facs_q[i + 1]` through the slot at `rbp - 0x60`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

theorem blk_L5ad0 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5ad0" := by
  cfg_block
  measure_hb "L5ad0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hbx, h9,
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
    case' vc3 v hv' hc => skip
    all_goals rsimp at hv' hc
    all_goals rw [hax, h12, hl] at hv'; cases hv'
    all_goals rw [CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl] at hc
    all_goals rw [h9, r9_succ, hv] at hc
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
      · rw [var_L5f90, var_L5ad0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
    case vc3.refl =>
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, ?_, ?_,
        ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact hbx
      · rsimp; exact h9
      · rsimp; rw [h9, r9_succ]
      · simp only [nf, u8]; omega
      · rw [var_L5ae4, var_L5ad0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

theorem blk_L5bc7 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5bc7" := by
  cfg_block
  measure_hb "L5bc7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨hbx, h9, h14, hj⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hfr : u8 x.v.freqRes (i + 1) = 0 ∨ u8 x.v.freqRes (i + 1) = 1 := by
      have := hC.1.2.2.2.2.2.1 (i + 1) (by omega); omega
    have hnf := nf_le x (i + 1) hC.2.1 hC.2.2.1
    have hj47 : j + 1 ≤ 47 := by omega
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    have hl38 := T_ld_f38 hm
    rw [h38] at hl38
    have hfrl := T_ld_fr hm hC (i + 1) 0 (by omega) 12 rfl
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hbp, hl38]; rfl
    · rename_i v38 hv38
      rsimp at hv38; rw [hbp, hl38] at hv38; cases hv38
      rsimp; simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      rw [hbx, hfrl]; rfl
    all_goals rename_i v38 hv38 vf hvf hc
    all_goals rsimp at hv38 hvf
    all_goals rw [hbp, hl38] at hv38; cases hv38
    all_goals simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hvf
    all_goals rw [hbx, hfrl] at hvf; cases hvf
    all_goals rsimp at hc
    all_goals try rw [zx8] at hc
    all_goals try simp only [Nat.add_zero] at hfr hc
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j + 1, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ?_, ?_, hj47, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact hbx
      · rsimp; exact h14
      · rsimp; rw [zx8]
      · rw [var_L5ad0, var_L5bc7, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); rw [h14, h9]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · exfalso
      rcases hfr with h | h <;> rw [h] at hc <;> revert hc <;> decide

omit [CodeEnv] in
theorem enD_kt1 (x : EArgs) (t₀ : MachineData) : kt x t₀ + 1 < 10 := by
  simp only [kt]; split <;> split <;> omega

omit [CodeEnv] in
theorem enD_efq (b : BitVec 64) (i j : Nat) (hc : 48 * (i + 1) + j < 2 ^ 32) :
    (b + 86496#64 + BitVec.ofNat 64 (48 * (i + 1) + 1) + BitVec.ofNat 64 j
      + Int64.toBitVec (-1) - (b + 0x151e0#64)).toNat = 48 * (i + 1) + j := by
  have e1 : BitVec.ofNat 64 (48 * (i + 1) + 1) = BitVec.ofNat 64 (48 * (i + 1)) + 1#64 := by
    rw [BitVec.ofNat_add]
  rw [e1, show Int64.toBitVec (-1) = 0xffffffffffffffff#64 from rfl,
    show b + 86496#64 + (BitVec.ofNat 64 (48 * (i + 1)) + 1#64) + BitVec.ofNat 64 j
      + 0xffffffffffffffff#64 - (b + 0x151e0#64)
      = BitVec.ofNat 64 (48 * (i + 1)) + BitVec.ofNat 64 j by bv_omega]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem blk_L5ae4 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5ae4" := by
  cfg_block
  measure_hb "L5ae4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12,
      ⟨hbx, h9, h14, hj⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hnf := nf_le x (i + 1) hC.2.1 hC.2.2.1
    have hl60 := T_ld_f60 hm
    rw [hLI.2.2] at hl60
    have hl98 := T_ld_f98 hm
    rw [hFC.1] at hl98
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hel := T_efq_ld hm
    have hK := enD_kt1 x t₀
    have hld := vlc_l1 hm hC.2.2.2.2.2.2.2.1 (kt x t₀ + 1) hK
    have hwk := fun w : BitVec 32 => vlc_walk1 (hC.2.2.2.2.2.2.2.1 (kt x t₀ + 1) hK) (idx1_lt w)
    have hin : (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1) + 1)
        + BitVec.ofNat 64 j + Int64.toBitVec (-1) - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by
      simp only [arg3]; rw [enD_efq _ _ _ (by omega)]; omega
    have e60 : loadInt s₀.dmem (s₀.regs.get64 .rbp + (-96 : Int64).toBitVec) 8
        = some (Int.ofBytes (Int.toBytes 8
            (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1) + 1)).toInt)) := by
      rw [hbp]; exact hl60
    have e98 : loadInt s₀.dmem (s₀.regs.get64 .rbp + (-152 : Int64).toBitVec) 8
        = some (Int.ofBytes (Int.toBytes 8 (x.vt (kt x t₀ + 1)).p.toInt)) := by
      rw [hbp]; exact hl98
    have ei : loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4
        = some (Int.ofBytes (Int.toBytes 4 gi.toInt)) := by
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact hli
    have ep : loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 16) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl]; exact hlp
    have eb : loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 0) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hlb
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    have hif23 : ((Int64.toBitVec 23).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, hif23, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [e60, e98, ei, ep, eb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq] at *
    · rw [h9]; exact hel _ 1 hin
    · rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hbl
    · exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · rename_i w st b1 b2 b3 vs vl af hvs hvl hs hq hb
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩,
        ⟨?_, ?_, ?_, hj⟩, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first
        | exact hsp
        | exact hbp
        | exact hdx
        | exact h13
        | exact hbx
        | exact h9
        | exact h14
        | (rw [BitVec.setWidth_32_64_32]; exact hgi)
        | exact BitVec.setWidth_32_64_32 _
        | skip
      rw [var_L5b97, var_L5ae4, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); (try exact Nat.le_refl _)
    · rename_i w st b1 b2 b3 vs vl af hvs hvl hs hq hb
      simp only [(hld _).1, (hld _).2, Option.some.injEq] at hq hb
      subst hq hb
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hvs
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩,
        ⟨?_, ?_, ?_, hj⟩, ⟨?_, ?_⟩, ?_, ?_, _, hwk _, ?_, ?_, hvs⟩, ?_⟩
      all_goals try rsimp
      all_goals first
        | exact hsp
        | exact hbp
        | exact hdx
        | exact h13
        | exact hbx
        | exact h9
        | exact h14
        | (rw [BitVec.setWidth_32_64_32]; exact hgi)
        | exact BitVec.setWidth_32_64_32 _
        | skip
      rw [var_L5b25, var_L5ae4, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); (try exact Nat.le_refl _)

theorem blk_L5b25 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5b25" := by
  cfg_block
  measure_hb "L5b25"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, 
      ⟨hbx, h9, h14, hj⟩, ⟨hdi, h8⟩, h12, h13', e, hW, hax, h10, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀ + 1) (enD_kt1 x t₀) 2 _
      (vlc_walk_next hW hneg w)
    have hbl := fun (o : BitVec 32) (ho : o.toNat ≤ x.p8.toNat) =>
      T_buf_ld hm _ 4 (rd_off o x.p8 x.L ho hC.2.2.2.2.2.1)
    have p8 : PLift _ := ⟨h8⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have p13' : PLift _ := ⟨h13'⟩
    have pdi : PLift _ := ⟨hdi⟩
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_lo]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [BitVec.setWidth_32_64_32, h8, h12, h13', hdi,
      show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
      show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero] at *
    · exact hbl _ (gb_clamp _ _ _ _)
    · rename_i hv _
      rw [vlc_key hax h10 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · rename_i hv _ _
      rw [vlc_key hax h10 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · rename_i hv hbuf hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      simp only [CondCode.interp_s, StatusFlags.sf_from_result, BitVec.and_self,
        BitVec.msb_signExtend, decide_true, Bool.true_and, Nat.reduceLT] at hs
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, 
        ⟨?_, ?_, ?_, hj⟩, ⟨?_, ?_⟩, ?_, ?_, _, vlc_walk_next hW hneg _, ?_, ?_, hs⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact h9 | exact h14 | exact hbx | exact p8.down | exact p12.down | exact p13'.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5b61, var_L5b25, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)
    · rename_i hv hbuf hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, 
        ⟨?_, ?_, ?_, hj⟩, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact h9 | exact h14 | exact hbx | exact p8.down | exact p12.down | exact p13'.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5b93, var_L5b25, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)

theorem blk_L5b61 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5b61" := by
  cfg_block
  measure_hb "L5b61"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, 
      ⟨hbx, h9, h14, hj⟩, ⟨hdi, h8⟩, h12, h13', e, hW, hax, h11, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀ + 1) (enD_kt1 x t₀) 1 _
      (vlc_walk_next hW hneg w)
    have hbl := fun (o : BitVec 32) (ho : o.toNat ≤ x.p8.toNat) =>
      T_buf_ld hm _ 4 (rd_off o x.p8 x.L ho hC.2.2.2.2.2.1)
    have p8 : PLift _ := ⟨h8⟩
    have p12 : PLift _ := ⟨h12⟩
    have p13 : PLift _ := ⟨h13⟩
    have p13' : PLift _ := ⟨h13'⟩
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_lo]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, ↓reduceIte] at *
    all_goals try rsimp at *
    all_goals try simp only [BitVec.setWidth_32_64_32, h8, h12, h13', hdi,
      show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
      show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero] at *
    · exact hbl _ (gb_clamp _ _ _ _)
    · rename_i hv _
      rw [vlc_key hax h11 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · rename_i hv _ _
      rw [vlc_key hax h11 hv]
      exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, 
        ⟨?_, ?_, ?_, hj⟩, ⟨?_, ?_⟩⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact h9 | exact h14 | exact hbx | exact p8.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5b93, var_L5b61, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

theorem blk_L5b93 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5b93" := by
  cfg_block
  measure_hb "L5b93"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, 
      hJ, hW⟩, hn⟩ := hs₀
    have hl := T_ld_f2c hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · (try rsimp); rw [hbp]; exact hl
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact hJ | exact hW | skip
      rw [var_L5b97, var_L5b93, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _


theorem blk_L5b97 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5b97" := by
  cfg_block
  measure_hb "L5b97"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, 
      ⟨hbx, h9, h14, hj⟩, ⟨hdi, h8⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hnf := nf_le x (i + 1) hC.2.1 hC.2.2.1
    have hi := hLI.1
    have hl40 := T_ld_f40 hm
    have hl60 := T_ld_f60 hm
    rw [hFC.2.2.2.2.2.2.1] at hl40
    rw [hLI.2.2] at hl60
    have hst := T_gb_st hm
    have hli := T_gb_idx hm
    have e40 : loadInt s₀.dmem (s₀.regs.get64 .rbp + Int64.toBitVec (-64)) 8
        = some (Int.ofBytes (Int.toBytes 8 (arg1 t₀ + 0x4c1e0#64).toInt)) := by
      rw [hbp]; exact hl40
    have ei : (loadInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4).isSome = true := by
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    have e60 : ∀ v : BitVec 32, loadInt (storeInt s₀.dmem (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4
        v.toInt) (s₀.regs.get64 .rbp + Int64.toBitVec (-96)) 8
        = some (Int.ofBytes (Int.toBytes 8 (EQ t₀ + BitVec.ofNat 64 (48 * (i + 1) + 1)).toInt)) := by
      intro v; rw [hbp, hdx, show Int64.toBitVec 8 = 8#64 from rfl, T_ld_f60 (hst v), hLI.2.2]
    have hrow : (t₀.regs.get64 .rcx + 86496#64 + BitVec.ofNat 64 (48 * (i + 1) + 1)
        + s₀.regs.get64 .r9 + Int64.toBitVec 0 - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by
      rw [h9]; simp only [arg3]; rw [efq_r9 _ _ _ (by omega)]; omega
    have hS : ∀ (v : BitVec 32) (b : Int), storeInt (storeInt s₀.dmem
        (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4 v.toInt) (t₀.regs.get64 .rcx + 86496#64
        + BitVec.ofNat 64 (48 * (i + 1) + 1) + s₀.regs.get64 .r9 + Int64.toBitVec 0) 1 b
        =⋆ T k Ext x ra t₀ fv v := by
      intro v b; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_efq_st (hst v) _ 1 hrow b
    have hL : ∀ (v : BitVec 32), (loadInt (storeInt s₀.dmem
        (s₀.regs.get64 .rdx + Int64.toBitVec 8) 4 v.toInt) (t₀.regs.get64 .rcx + 86496#64
        + BitVec.ofNat 64 (48 * (i + 1) + 1) + s₀.regs.get64 .r9 + Int64.toBitVec 0) 1).isSome
        = true := by
      intro v; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_efq_ld (hst v) _ 1 hrow
    have pbx : PLift _ := ⟨hbx⟩
    have p9 : PLift _ := ⟨h9⟩
    have p14 : PLift _ := ⟨h14⟩
    have p13 : PLift _ := ⟨h13⟩
    have p8 : PLift _ := ⟨h8⟩
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    all_goals try simp only [e40, ei, e60, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    · rename_i hz
      exfalso
      rw [z_sub_iff, p9.down] at hz
      have := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat, show (BitVec.setWidth 64 (Int64.toBitVec 47)).toNat = 47 from rfl,
        Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)] at this
      omega
    · exact hL _
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, _, ⟨hC, ?_, ?_, ?_, hS _ _⟩, hFC.2.2.2.2.2.1⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rw [BitVec.setWidth_32_64_32, p8.down]; exact gb_clamp _ _ _ _
      · show (0 : Nat) < _
        rw [var_L5b97, p9.down, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
        omega
    · refine ⟨⟨fv, _, i, j, ⟨⟨⟨hC, ?_, ?_, ?_, hS _ _⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨?_, ?_, ?_, hj⟩⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · first | (rw [BitVec.setWidth_32_64_32, p8.down]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _)
      · exact hdx
      · exact p13.down
      · simp only [R12, arg1]; (try rsimp)
      · exact pbx.down
      · exact p9.down
      · exact p14.down
      · rw [var_L5bc7, var_L5b97, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb (hS _ _)]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
