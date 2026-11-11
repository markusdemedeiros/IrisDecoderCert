import Kraken.X64.Examples.Sbr.Parse.EnvBlk6
import Kraken.X64.Examples.Sbr.Parse.EnvBlk7

/-!
# `read_sbr_envelope`: copy D (low resolution), the band loop
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

theorem e0 (b : BitVec 64) :
    b + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 0#64)) * 4#64 + Int64.toBitVec 0
      = b := by
  rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 0#64)) * 4#64 = 0#64 from rfl,
    show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, BitVec.add_zero]

variable [CodeEnv]

theorem n0v (n : Nat) (h : n ≤ 24) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int))))
      = BitVec.ofNat 64 n := by
  rw [c4_val]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega


theorem blk_L5e70 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5e70" := by
  cfg_block
  measure_hb "L5e70"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD, h9, hj,
      hsi, hax⟩, hn⟩ := hs₀
    have hn0 : x.n0 ≤ 24 := hC.2.1
    have hl0 := T_ld_n0 hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hax, e0, h12, hl0]; rfl
    · rename_i v hv hc
      rsimp at hv hc; rw [hax, e0, h12, hl0] at hv; cases hv
      rw [CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl] at hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_⟩,
        Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rw [var_L5f90, var_L5e70, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        rw [h9, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        omega
    · rename_i v hv hc hc2
      exfalso
      rsimp at hv hc hc2; rw [hax, e0, h12, hl0] at hv; cases hv
      rw [CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl] at hc hc2
      rw [h9, r9_succ, n0v _ hn0] at hc
      rw [hsi] at hc2
      simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not,
        BitVec.toNat_ofNat, BitVec.toNat_setWidth, show (Int64.toBitVec 48).toNat = 48 from rfl] at hc hc2
      omega
    · rename_i v hv hc hc2
      rsimp at hv hc hc2; rw [hax, e0, h12, hl0] at hv; cases hv
      rw [CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl] at hc hc2
      rw [h9, r9_succ, n0v _ hn0] at hc
      simp only [Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not,
        BitVec.toNat_ofNat] at hc
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD, ?_, ?_,
        by omega, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h9
      · rsimp; rw [h9, r9_succ]
      · rsimp; exact hsi
      · rw [var_L5e8d, var_L5e70, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        rsimp
        exact Nat.le_refl _

theorem kt_lt (x : EArgs) (t₀ : MachineData) : kt x t₀ < 10 := by
  simp only [kt]; split <;> split <;> omega

/-- The two loads of entry `j` of table `K`, reached by a walk. -/
theorem vlc_at {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32}
    (h : m =⋆ T k Ext x ra t₀ fv i) (hC : VlcC x.vt) (K : Nat) (hK : K < 10)
    (d : Nat) (j : BitVec 32) (hw : VWalk (x.vt K).es d j.toNat) :
    m.loadInt ((x.vt K).p + j.setWidth 64 * 4#64) 2
      = some (Int.ofBytes (((x.vt K).es.drop (4 * j.toNat)).take 2))
    ∧ m.loadInt ((x.vt K).p + j.setWidth 64 * 4#64 + 2#64) 2
      = some (Int.ofBytes (((x.vt K).es.drop (4 * j.toNat + 2)).take 2)) := by
  obtain ⟨F, hF⟩ := T_vlc k Ext x ra t₀ fv i
  rw [hF] at h
  have hN := VWalk.lt hw
  have h28 : j.toNat < 2 ^ 28 := by
    have := (hC K hK).2.1; simp only [VlcTab.N] at this; omega
  exact ⟨vlc_load_sym h hC K hK hN (vlc_addr _ j h28),
    vlc_load_len h hC K hK hN (vlc_addr2 _ j h28)⟩

omit [CodeEnv] in
theorem efq_k (b : BitVec 64) (c k : Nat) (hc : c + k < 2 ^ 32) :
    (b + 86496#64 + BitVec.ofNat 64 c + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k))
      + Int64.toBitVec 0 - (b + 0x151e0#64)).toNat = c + k := by
  have e1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k)) = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  rw [e1, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero,
    show b + 86496#64 + BitVec.ofNat 64 c + BitVec.ofNat 64 k - (b + 0x151e0#64)
      = BitVec.ofNat 64 c + BitVec.ofNat 64 k by bv_omega]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem idx1_lt (w : BitVec 32) :
    (w.ushiftRight ((Int64.toBitVec 23).toNat % 256 % 32)).toNat < 2 ^ 9 := vlc_idx1 w

/-- Level 1 of a walk: the two loads at the 9-bit window `w >> 23`. -/
theorem vlc_l1 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32}
    (h : m =⋆ T k Ext x ra t₀ fv i) (hC : VlcC x.vt) (K : Nat) (hK : K < 10) (w : BitVec 32) :
    let j := w.ushiftRight ((Int64.toBitVec 23).toNat % 256 % 32)
    m.loadInt ((x.vt K).p + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 j)) * 4#64
        + Int64.toBitVec 0) 2
      = some (Int.ofBytes (((x.vt K).es.drop (4 * j.toNat)).take 2))
    ∧ m.loadInt ((x.vt K).p + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 j)) * 4#64
        + Int64.toBitVec 2) 2
      = some (Int.ofBytes (((x.vt K).es.drop (4 * j.toNat + 2)).take 2)) := by
  intro j
  have hw : VWalk (x.vt K).es 3 j.toNat := vlc_walk1 (hC K hK) (idx1_lt w)
  have := vlc_at h hC K hK 3 j hw
  rw [BitVec.setWidth_32_64_32, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero,
    show Int64.toBitVec 2 = 2#64 from rfl]
  exact this

theorem blk_L5e8d (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5e8d" := by
  cfg_block
  measure_hb "L5e8d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD,
      h9, h14, hj, hsi⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hl80 := T_ld_f80 hm
    rw [hJD.2.2.1] at hl80
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hel := T_efq_ld hm
    have hld := vlc_l1 hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀)
    have hwk := fun w : BitVec 32 => vlc_walk1 (hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀)) (idx1_lt w)
    have hin : (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * i)
        + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (2 * (j + 1) - x.n1 % 2)))
        + Int64.toBitVec 0 - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by
      have := hC.2.1
      rw [efq_k _ _ _ (by omega)]; omega
    have e80 : loadInt s₀.dmem (s₀.regs.get64 .rbp + (-128 : Int64).toBitVec) 8
        = some (Int.ofBytes (Int.toBytes 8
            (t₀.regs.get64 Reg64.rcx + 86496#64 + BitVec.ofNat 64 (48 * i)).toInt)) := by
      rw [hbp]; exact hl80
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
    all_goals try simp only [e80, ei, ep, eb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq] at *
    · rw [hsi]; exact hel _ 1 hin
    · rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]; exact hbl
    · rw [h13]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).1⟩
    · rw [h13]; exact Option.isSome_iff_exists.mpr ⟨_, (hld _).2⟩
    · rename_i w st b1 b2 b3 vs vl af hvs hvl hs hq hb
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, hJD,
        ⟨?_, ?_, hj, ?_⟩, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact h9 | exact h14 | exact hsi | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5f3e, var_L5e8d, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)
    · rename_i w st b1 b2 b3 vs vl af hvs hvl hs hq hb
      rw [h13] at hvs hvl
      simp only [(hld _).1, (hld _).2, Option.some.injEq] at hvs hvl
      subst hvs hvl
      simp only [CondCode.interp_ns, StatusFlags.sf_from_result, BitVec.and_self,
        Bool.not_eq_false', BitVec.msb_signExtend, decide_true,
        Bool.true_and, Nat.reduceLT] at hs
      refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, hJD,
        ⟨?_, ?_, hj, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, _, hwk _, ?_, ?_, hs⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact h9 | exact h14 | exact hsi | (rw [BitVec.setWidth_32_64_32]; exact hgi) | exact BitVec.setWidth_32_64_32 _ | skip
      · rw [var_L5eca, var_L5e8d, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
        case hb => (try rsimp); exact hbp
        (try rsimp); (try exact Nat.le_refl _)


omit [CodeEnv] in
/-- The level-2/3 index of a walk: `sym + (window >> (len & 31))`. -/
theorem vlc_key {a r w v : BitVec 64} {sym len : BitVec 16}
    (ha : a.setWidth 32 = sym.signExtend 32) (hl : r.setWidth 32 = len.signExtend 32)
    (hv : v.setWidth 32 = (w.setWidth 32).ushiftRight
      ((BitVec.setWidth 64 (BitVec.setWidth 32 r)).toNat % 256 % 32)) :
    a.setWidth 32 + v.setWidth 32 = (w.setWidth 32).ushiftRight (len.toNat % 32)
      + sym.signExtend 32 := by
  rw [hv, ha, hl, vlc_sh, BitVec.add_comm]

theorem blk_L5eca (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5eca" := by
  cfg_block
  measure_hb "L5eca"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, hJD,
      ⟨h9, h14, hj, hsi⟩, ⟨hdi, h8⟩, h12, h13', e, hW, hax, h10, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀) 2 _
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
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, hJD,
        ⟨?_, ?_, hj, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, _, vlc_walk_next hW hneg _, ?_, ?_, hs⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact h9 | exact h14 | exact hsi | exact p8.down | exact p12.down | exact p13'.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5f07, var_L5eca, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)
    · rename_i hv hbuf hvs hvl hs
      rw [vlc_key hax h10 hv, (hld _).1, Option.some.injEq] at hvs
      rw [vlc_key hax h10 hv, show Int64.toBitVec 2 = 2#64 from rfl, (hld _).2, Option.some.injEq] at hvl
      subst hvs hvl
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, hJD,
        ⟨?_, ?_, hj, ?_⟩, ?_, ?_⟩, Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact h9 | exact h14 | exact hsi | exact p8.down | exact p12.down | exact p13'.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5f3a, var_L5eca, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp)

theorem blk_L5f07 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5f07" := by
  cfg_block
  measure_hb "L5f07"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, hJD,
      ⟨h9, h14, hj, hsi⟩, ⟨hdi, h8⟩, h12, h13', e, hW, hax, h11, hneg⟩, hn⟩ := hs₀
    have hld := fun w => vlc_at hm hC.2.2.2.2.2.2.2.1 (kt x t₀) (kt_lt x t₀) 1 _
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
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, hJD,
        ⟨?_, ?_, hj, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact p13.down | exact h9 | exact h14 | exact hsi | exact p8.down | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _) | exact BitVec.setWidth_32_64_32 _ | skip
      rw [var_L5f3a, var_L5f07, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb hmT]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _

/-- The 4-byte spill at `rbp - 0x2c` (`-bits`) lies in the raw 8 bytes at `rbp - 0x30`. -/
theorem T_ld_f2c {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i) :
    (m.loadInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-44)) 4).isSome = true := by
  rw [T_frw] at h
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r
      (eq_r (eq_r (eq_r (eq_r eq_t)))))))))))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h
  refine Block.loadInt_isSome h ?_
  rw [show t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-44) - (t₀.regs.get64 .rsp - 0x38#64)
    = 4#64 by rw [show Int64.toBitVec (-44) = 0xffffffffffffffd4#64 from rfl]; bv_omega]
  decide

theorem blk_L5f3a (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5f3a" := by
  cfg_block
  measure_hb "L5f3a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, hJD,
      hJ, hW⟩, hn⟩ := hs₀
    have hl := T_ld_f2c hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · (try rsimp); rw [hbp]; exact hl
    · refine ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, hJD, ?_, ?_⟩, ?_⟩
      all_goals try rsimp
      all_goals first | exact hsp | exact hbp | exact hdx | exact h13 | exact hJ | exact hW | skip
      rw [var_L5f3e, var_L5f3a, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
      case hb => (try rsimp); exact hbp
      (try rsimp); exact Nat.le_refl _


omit [CodeEnv] in
theorem efq_r9 (b : BitVec 64) (c j : Nat) (hc : c + j < 2 ^ 32) :
    (b + 86496#64 + BitVec.ofNat 64 c + BitVec.ofNat 64 j + Int64.toBitVec 0
      - (b + 0x151e0#64)).toNat = c + j := by
  rw [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero,
    show b + 86496#64 + BitVec.ofNat 64 c + BitVec.ofNat 64 j - (b + 0x151e0#64)
      = BitVec.ofNat 64 c + BitVec.ofNat 64 j by bv_omega]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem fi_gb_efq {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} {regs : Reg64s} {zmms} {status}
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (h : m =⋆ T k Ext x ra t₀ fv i)
    (v : BitVec 32) (addr : BitVec 64)
    (hin : (addr - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432) (b : Int) :
    fi (MachineData.mk regs zmms status
      ((m.storeInt (arg2 t₀ + 8#64) 4 v.toInt).storeInt addr 1 b)) = fv.f68.toNat := by
  rw [fi_eq' regs zmms status _ hbp (T_efq_st (T_gb_st h v) addr 1 hin b)]

theorem blk_L5f3e (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5f3e" := by
  cfg_block
  measure_hb "L5f3e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, hJD,
      ⟨h9, h14, hj, hsi⟩, ⟨hdi, h8⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hn0 : x.n0 ≤ 24 := hC.2.1
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
    have pSi : PLift _ := ⟨hsi⟩
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
        rw [var_L5f3e, p9.down, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
        omega
    · refine ⟨⟨fv, _, i, j, ⟨⟨⟨hC, ?_, ?_, ?_, hS _ _⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ⟨?_, ?_, hj, ?_⟩⟩, ?_⟩
      all_goals try rsimp
      · exact hsp
      · exact hbp
      · first | (rw [BitVec.setWidth_32_64_32, p8.down]; exact gb_clamp _ _ _ _) | (rw [BitVec.setWidth_32_64_32]; exact gb_clamp _ _ _ _)
      · exact hdx
      · exact p13.down
      · simp only [R12, arg1]; (try rsimp)
      · exact p9.down
      · exact p14.down
      · exact pSi.down
      · rw [var_L5f6e, var_L5f3e, fi_eq hbp hmT, fi_eq' _ _ _ _ ?hb (hS _ _)]
        case hb => (try rsimp); exact hbp
        (try rsimp); exact Nat.le_refl _

theorem blk_L5f6e (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5f6e" := by
  cfg_block
  measure_hb "L5f6e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, j, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD,
      ⟨h9, h14, hj, hsi⟩⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hn0 : x.n0 ≤ 24 := hC.2.1
    have hi := hLI.1
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    have hl48 := T_ld_f48 hm
    have hl38 := T_ld_f38 hm
    rw [hJD.1] at hl48; rw [h38] at hl38
    have hfr := T_ld_fr hm hC (i + 1) 0 (by omega) 12 rfl
    have hu0 := hJD.2.1
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hbp, hl48]; rfl
    · rename_i v48 hv48
      rsimp at hv48; rw [hbp, hl48] at hv48; cases hv48
      rsimp; rw [hbp, hl38]; rfl
    · rename_i v48 hv48 v38 hv38
      rsimp at hv48 hv38; rw [hbp, hl48] at hv48; rw [hbp, hl38] at hv38; cases hv48; cases hv38
      rsimp; simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]; rw [hfr]; rfl
    all_goals rename_i v48 hv48 v38 hv38 vf hvf hc
    all_goals rsimp at hv48 hv38 hvf
    all_goals rw [hbp, hl48] at hv48; cases hv48
    all_goals rw [hbp, hl38] at hv38; cases hv38
    all_goals simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hvf
    all_goals rw [hfr] at hvf; cases hvf
    all_goals try simp only [u8] at hu0
    all_goals rsimp at hc
    all_goals try rw [zx8] at hc
    all_goals try simp only [Nat.add_zero] at hc
    all_goals try rw [hu0] at hc
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, j + 1, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD,
        ?_, by omega, ?_, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h14
      · rsimp; rw [hsi, show Int64.toBitVec 2 = 2#64 from rfl]
        have : x.n1 % 2 ≤ 1 := by omega
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, odd]
        omega
      · rsimp; rw [zx8]; simp only [Nat.add_zero]; rw [hu0]
      · rw [var_L5e70, var_L5f6e, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        (try rsimp); rw [h14, h9]
        simp only [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    · exfalso; revert hc; decide

end Kraken.Examples.Sbr.Env
