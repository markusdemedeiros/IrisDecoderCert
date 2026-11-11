import Kraken.X64.Examples.Sbr.Parse.EnvBlk3

/-!
# `read_sbr_envelope`: the USAC temporal-shaping flags at the end of an envelope
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h rd_off gb_clamp gb_clamp64 shr_lt shr30_lt)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

/-- Offsets into `bs_temp_shape` (`0x15ab4 = 88756`) and `bs_inter_temp_shape_mode`
(`0x15aba = 88762`). -/
theorem ts_off (b : BitVec 64) (c : Nat) (hc : c < 2 ^ 32) :
    (b + BitVec.ofNat 64 c + Int64.toBitVec 88756 - (b + 0x15ab4#64)).toNat = c := by
  rw [show Int64.toBitVec 88756 = 0x15ab4#64 from rfl,
    show b + BitVec.ofNat 64 c + 0x15ab4#64 - (b + 0x15ab4#64) = BitVec.ofNat 64 c by bv_omega,
    BitVec.toNat_ofNat]
  omega

theorem ts_off6 (b : BitVec 64) (c : Nat) (hc : c < 2 ^ 32) :
    (b + BitVec.ofNat 64 c + Int64.toBitVec 88762 - (b + 0x15ab4#64)).toNat = c + 6 := by
  rw [show Int64.toBitVec 88762 = 0x15aba#64 from rfl,
    show b + BitVec.ofNat 64 c + 0x15aba#64 - (b + 0x15ab4#64) = BitVec.ofNat 64 (c + 6) by
      bv_omega,
    BitVec.toNat_ofNat]
  omega

variable [CodeEnv]

/-- The 4-byte spill slot at `rbp - 0x70` holds no invariant; a load from it succeeds. -/
theorem T_ld_f70 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i) :
    (m.loadInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-112)) 4).isSome = true := by
  rw [fa_70]
  rw [T_frw] at h
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 4 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r eq_h)))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h
  exact Block.loadInt_isSome h (by simp)

section Gb

variable {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
  {t₀ : MachineData} {fv : FV} {i : BitVec 32}

/-- `T` without the reader's index cell. -/
def TG (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) (fv : FV) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Sv t₀ ⋆ (FrW r fv ⋆ (8 ?@ (r - 0xb0#64) ⋆ (Reserve k (r - 0xb0#64) ⋆ (ChE (arg3 t₀) x
    ⋆ (SbrE (arg1 t₀) x ⋆ (c8 (arg2 t₀) x.buf ⋆ (4 ?@ (arg2 t₀ + 0xc#64)
    ⋆ (cell4 (arg2 t₀ + 0x10#64) x.p8 ⋆ (InE Ext x t₀ ⋆ Rest x.R ra t₀)))))))))

theorem T_gi (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData)
    (fv : FV) (i : BitVec 32) :
    T k Ext x ra t₀ fv i = cell4 (arg2 t₀ + 8#64) i ⋆ TG k Ext x ra t₀ fv := by
  simp only [T, EF, GbE, TG]; ac_rfl

theorem T_gb_idx (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg2 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) :=
  T_ld_at h (T_gi k Ext x ra t₀ fv i) 4 (Int.toBytes_length 4 _) (by omega)

theorem T_gb_st (h : m =⋆ T k Ext x ra t₀ fv i) (v : BitVec 32) :
    m.storeInt (arg2 t₀ + 8#64) 4 v.toInt =⋆ T k Ext x ra t₀ fv v := by
  rw [T_gi] at h ⊢
  exact storeInt_sep _ 4 _ _ m ⟨h, Int.toBytes_length 4 _⟩ v.toInt

theorem T_gb_buf (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg2 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
  obtain ⟨F, hF⟩ : ∃ F, T k Ext x ra t₀ fv i = c8 (arg2 t₀) x.buf ⋆ F := by
    simp only [T, EF, GbE]
    exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_l eq_h)))))))⟩
  exact T_ld_at h hF 8 (Int.toBytes_length 8 _) (by omega)

theorem T_gb_p8 (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg2 t₀ + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  obtain ⟨F, hF⟩ : ∃ F, T k Ext x ra t₀ fv i = cell4 (arg2 t₀ + 0x10#64) x.p8 ⋆ F := by
    simp only [T, EF, GbE]
    exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_l (eq_r (eq_r eq_t)))))))))⟩
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem fi_gb {regs : Reg64s} {zmms} {status}
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (h : m =⋆ T k Ext x ra t₀ fv i)
    (v : BitVec 32) :
    fi (MachineData.mk regs zmms status (m.storeInt (arg2 t₀ + 8#64) 4 v.toInt))
      = fv.f68.toNat :=
  fi_eq' _ _ _ _ hbp (T_gb_st h v)

theorem T_ts_st (h : m =⋆ T k Ext x ra t₀ fv i) (addr : BitVec 64) (n : Nat)
    (hin : (addr - (arg3 t₀ + 0x15ab4#64)).toNat + n ≤ 12) (v : Int) :
    m.storeInt addr n v =⋆ T k Ext x ra t₀ fv i := by
  obtain ⟨F, hF⟩ := T_ts k Ext x ra t₀ fv i
  rw [hF] at h ⊢
  exact Block.storeInt h hin v

theorem T_ts_ld (h : m =⋆ T k Ext x ra t₀ fv i) (addr : BitVec 64) (n : Nat)
    (hin : (addr - (arg3 t₀ + 0x15ab4#64)).toNat + n ≤ 12) : (m.loadInt addr n).isSome = true := by
  obtain ⟨F, hF⟩ := T_ts k Ext x ra t₀ fv i
  rw [hF] at h
  exact Block.loadInt_isSome h hin

theorem fi_gb_ts {regs : Reg64s} {zmms} {status}
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (h : m =⋆ T k Ext x ra t₀ fv i)
    (v : BitVec 32) (addr : BitVec 64)
    (hin : (addr - (arg3 t₀ + 0x15ab4#64)).toNat + 1 ≤ 12) (b : Int) :
    fi (MachineData.mk regs zmms status
      ((m.storeInt (arg2 t₀ + 8#64) 4 v.toInt).storeInt addr 1 b)) = fv.f68.toNat :=
  fi_eq' _ _ _ _ hbp (T_ts_st (T_gb_st h v) addr 1 hin b)

theorem T_buf_ld (h : m =⋆ T k Ext x ra t₀ fv i) (off : BitVec 64) (n : Nat)
    (hin : off.toNat + n ≤ x.L) : (m.loadInt (x.buf + off) n).isSome = true := by
  obtain ⟨F, hF⟩ := T_buf k Ext x ra t₀ fv i
  rw [hF] at h
  exact Blocks.loadInt_isSome h (Blocks.Inside.base_add hin)

end Gb

/-- The byte spill at `rbp - 0x2d` lies in the raw 8 bytes at `rbp - 0x30`. -/
theorem T_ld_f2d {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i) :
    (m.loadInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-45)) 1).isSome = true := by
  rw [T_frw] at h
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r
      (eq_r (eq_r (eq_r (eq_r eq_t)))))))))))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h
  refine Block.loadInt_isSome h ?_
  rw [show t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-45) - (t₀.regs.get64 .rsp - 0x38#64)
    = 3#64 by rw [show Int64.toBitVec (-45) = 0xffffffffffffffd3#64 from rfl]; bv_omega]
  decide

theorem blk_L5f90 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5f90" := by
  cfg_block
  measure_hb "L5f90"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12⟩, hn⟩ := hs₀
    have hl78 := T_ld_f78 hm
    have hl70 := T_ld_f70 hm
    have hl68 := T_ld_f68 hm
    have hl38 := T_ld_f38 hm
    have hus := T_ld_usac hm
    have hit := T_ld_it hm
    have hmT : Hide _ := hm
    clear hm
    have h78 : fv.f78 = t₀.regs.get64 .rsi := hFC.2.2.2.1
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [hbp, hl78]; rfl
    · rename_i v78 hv78
      rsimp at hv78; rw [hbp, hl78] at hv78; cases hv78
      rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h78,
        show Int64.toBitVec 16 = 16#64 from rfl, hus]; rfl
    · rsimp; rw [hbp]; exact hl70
    · rename_i v78 hv78 vus hvus v70 hv70
      rsimp; rw [hbp, hl68]; rfl
    · rename_i v78 hv78 vus hvus v70 hv70 v68 hv68
      rsimp; rw [hbp, hl38]; rfl
    · rename_i v78 hv78 vus hvus v70 hv70 v68 hv68 v38 hv38 hz
      rsimp at hv78 hv68 hv38
      rw [hbp, hl78] at hv78; rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38
      cases hv78; cases hv68; cases hv38
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, ?_⟩,
        Or.inr ⟨?_, by decide⟩⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h68]
      · rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h38]
      · rw [var_L6019, var_L5f90]; simp only [fi]; rsimp
    · rename_i v78 hv78 vus hvus v70 hv70 v68 hv68 v38 hv38 hz
      rsimp at hv78; rw [hbp, hl78] at hv78; cases hv78
      rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h78,
        show Int64.toBitVec 20 = 20#64 from rfl, hit]; rfl
    · rename_i v78 hv78 vus hvus v70 hv70 v68 hv68 v38 hv38 hz vit hvit hz2
      rsimp at hv78 hv68 hv38
      rw [hbp, hl78] at hv78; rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38
      cases hv78; cases hv68; cases hv38
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, ?_⟩,
        Or.inr ⟨?_, by decide⟩⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h68]
      · rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h38]
      · rw [var_L6019, var_L5f90]; simp only [fi]; rsimp
    · rename_i v78 hv78 vus hvus v70 hv70 v68 hv68 v38 hv38 hz vit hvit hz2
      rsimp at hv78 hv68 hv38 hvus hvit hz hz2
      rw [hbp, hl78] at hv78; cases hv78
      rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38
      cases hv68; cases hv38
      rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h78,
        show Int64.toBitVec 16 = 16#64 from rfl, hus] at hvus
      rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h78,
        show Int64.toBitVec 20 = 20#64 from rfl, hit] at hvit
      cases hvus; cases hvit
      rw [← Bool.not_eq_true, z_sub_iff, cell4_val,
        show BitVec.setWidth 32 (Int64.toBitVec 0) = 0#32 from rfl] at hz hz2
      refine ⟨⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, ?_, hz, hz2⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h68]
      · rsimp; rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, h38]
      · rw [var_L5fac, var_L5f90]; simp only [fi]; rsimp; try exact Nat.le_refl _

theorem blk_L5fac (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5fac" := by
  cfg_block
  measure_hb "L5fac"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15, hus,
      hit⟩, hn⟩ := hs₀
    have hi8 : i ≤ 8 := by have := hC.1.2.2.2.2.1; have := hLI.1; omega
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hst := T_gb_st hm
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    have hif31 : ((Int64.toBitVec 31).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc, inc32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, hif31, ↓reduceIte] at *
    · try rsimp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    · rename_i vi hvi
      try rsimp at hvi
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rsimp; rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3
      rsimp at hvi hvb
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rsimp
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
        BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq,
        show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
        show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
      exact hbl
    · rename_i vi hvi vb hvb b1 b2 b3 vw hvw r1 f1 b4 r2 f2
      rsimp at hvi hvb
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rsimp; rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp b5 b6 b7 r3 f3 hA hvp
      rsimp at hvi hvb hvp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      rsimp; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp b5 b6 b7 r3 f3 hA hvp hc
      rsimp at hvi hvb hvp hc
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      rw [h9, CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl, BitVec.toNat_ofNat,
        show (BitVec.setWidth 64 (Int64.toBitVec 6)).toNat = 6 from rfl] at hc
      right; right; first | trivial | rfl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp b5 b6 b7 r3 f3 hA hvp hc
      rsimp at hvi hvb hvp hc
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      rw [h9, CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl, BitVec.toNat_ofNat,
        show (BitVec.setWidth 64 (Int64.toBitVec 6)).toNat = 6 from rfl] at hc
      have hi6 : i < 6 := by
        simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
        rw [Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)] at hc; exact hc
      refine ⟨⟨fv, _, i, ⟨⟨⟨hC, ?_, ?_, ?_, (by rsimp; rw [hdx]; exact hst _)⟩, ?_⟩, hFC, hLI, h68, ?_⟩,
        ?_, ?_, ?_, hi6⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · simp only [cell4_val, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega),
          BitVec.setWidth_eq]
        exact gb_clamp _ _ _ _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h9
      · rsimp; exact h15
      · rw [var_L5fdd, var_L5fac, fi_eq hbp hmT]
        rsimp
        rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, fi_gb ?hb hmT]
        case hb => (try rsimp); exact hbp
        exact Nat.le_refl _

theorem blk_L5fdd (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5fdd" := by
  cfg_block
  measure_hb "L5fdd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15, hi6⟩,
      hn⟩ := hs₀
    have hin : ∀ b : BitVec 64, (b + BitVec.ofNat 64 i + Int64.toBitVec 88756
        - (b + 0x15ab4#64)).toNat + 1 ≤ 12 := fun b => by rw [ts_off b i (by omega)]; omega
    have hts := T_ts_st hm
    have htl := T_ts_ld hm
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [h15, h9]; exact htl _ 1 (hin _)
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, ?_⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9,
        h15⟩, Or.inr ⟨?_, by decide⟩⟩
      · rsimp; rw [h15, h9]; exact hts _ 1 (hin _) _
      · rw [var_L6019, var_L5fdd, fi_eq hbp hmT]
        rsimp; rw [h15, h9, fi_eq' (k := k) (Ext := Ext) (x := x) (ra := ra) (t₀ := t₀) (fv := fv)
          (i := gi) _ _ _ _ hbp (hts _ 1 (hin _) _)]
    · refine ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, ?_⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9,
        h15, hi6⟩, ?_⟩
      · rsimp; rw [h15, h9]; exact hts _ 1 (hin _) _
      · rw [var_L5fe9, var_L5fdd, fi_eq hbp hmT]
        rsimp; rw [h15, h9, fi_eq' (k := k) (Ext := Ext) (x := x) (ra := ra) (t₀ := t₀) (fv := fv)
          (i := gi) _ _ _ _ hbp (hts _ 1 (hin _) _)]
        exact Nat.le_refl _

theorem blk_L5fe9 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5fe9" := by
  cfg_block
  measure_hb "L5fe9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15, hi6⟩,
      hn⟩ := hs₀
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hst := T_gb_st hm
    have hin : ∀ b : BitVec 64, (b + BitVec.ofNat 64 i + Int64.toBitVec 88762
        - (b + 0x15ab4#64)).toNat + 1 ≤ 12 := fun b => by rw [ts_off6 b i (by omega)]; omega
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    have hif30 : ((Int64.toBitVec 30).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, hif30, ↓reduceIte] at *
    · try rsimp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    · rename_i vi hvi
      try rsimp at hvi
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rsimp; rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3
      rsimp at hvi hvb
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rsimp
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
        BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq,
        show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
        show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
      exact hbl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 hA
      rsimp at hvi hvb
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rsimp; rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp b5 b6 b7 hA hvp
      rsimp at hvi hvb hvp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      rsimp; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp b5 b6 b7 hA hvp
      rsimp at hvi hvb hvp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      rsimp; rw [hdx, h15, h9, show Int64.toBitVec 8 = 8#64 from rfl]
      exact T_ts_ld (hst _) _ 1 (hin _)
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp b5 b6 b7 hA hvp
      rsimp at hvi hvb hvp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      refine ⟨⟨fv, _, i, ⟨⟨⟨hC, ?_, ?_, ?_,
        (by rsimp; rw [hdx, h15, h9, show Int64.toBitVec 8 = 8#64 from rfl];
            exact T_ts_st (hst _) _ 1 (hin _) _)⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · simp only [cell4_val, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega),
          BitVec.setWidth_eq]
        exact gb_clamp _ _ _ _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h9
      · rsimp; exact h15
      · rw [var_L6019, var_L5fe9, fi_eq hbp hmT]
        rsimp
        rw [hdx, h15, h9, show Int64.toBitVec 8 = 8#64 from rfl, fi_gb_ts ?hb hmT _ _ (hin _)]
        case hb => (try rsimp); exact hbp
        exact Nat.le_refl _

theorem blk_L5a60 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5a60" := by
  cfg_block
  measure_hb "L5a60"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15⟩,
      hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hoff := rd_off gi x.p8 x.L hgi hC.2.2.2.2.2.1
    have hbl := T_buf_ld hm _ 4 hoff
    have hli := T_gb_idx hm
    have hlb := T_gb_buf hm
    have hlp := T_gb_p8 hm
    have hst := T_gb_st hm
    have h2d := T_ld_f2d hm
    have hmT : Hide _ := hm
    clear hm
    have hif3 : ((Int64.toBitVec 3).toNat % 256 % 32 = 0) = False := eq_false (by decide)
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif3, ↓reduceIte] at *
    · try rsimp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    · rename_i vi hvi
      try rsimp at hvi
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rsimp; rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3
      rsimp at hvi hvb
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rsimp
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, cell4_val,
        BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega), BitVec.setWidth_eq,
        show (Int64.toBitVec 3).toNat % 256 % 32 = 3 from rfl,
        show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
      exact hbl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 hA
      rsimp at hvi hvb
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rsimp; rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp]; rfl
    · rsimp; rw [hbp]; exact h2d
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp v2d r3 f3 hA hvp h2dv
      rsimp at hvi hvb hvp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      rsimp; rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli]; rfl
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp v2d r3 f3 hA hvp h2dv hz
      exfalso
      rsimp at hz
      rw [z_sub_iff, h9] at hz
      have := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat, show (BitVec.setWidth 64 (Int64.toBitVec 8)).toNat = 8 from rfl]
        at this
      omega
    · rename_i vi hvi vb hvb b1 b2 b3 vw r1 f1 b4 r2 f2 vp v2d r3 f3 hA hvp h2dv hz
      rsimp at hvi hvb hvp
      rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, hli] at hvi; cases hvi
      rw [hdx, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hlb] at hvb; cases hvb
      rw [hdx, show Int64.toBitVec 16 = 16#64 from rfl, hlp] at hvp; cases hvp
      refine ⟨⟨fv, _, i, ⟨⟨⟨hC, ?_, ?_, ?_, (by rsimp; rw [hdx]; exact hst _)⟩, ?_⟩, hFC, hLI, h68,
        ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · simp only [cell4_val, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by omega),
          BitVec.setWidth_eq]
        exact gb_clamp _ _ _ _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; exact h9
      · rsimp; exact h15
      · rw [var_L5a95, var_L5a60, fi_eq hbp hmT]
        rsimp
        rw [hdx, show Int64.toBitVec 8 = 8#64 from rfl, fi_gb ?hb hmT]
        case hb => (try rsimp); exact hbp
        exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
