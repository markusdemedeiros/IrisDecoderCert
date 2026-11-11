import Kraken.X64.Examples.Sbr.Parse.EnvBlk2

/-!
# `read_sbr_envelope`: the loop step, the final copy, the error path, the epilogue
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

theorem sw_ofNat (n : Nat) (h : n < 2 ^ 32) :
    (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A row pointer stepped by one row (`addq $0x30`). -/
theorem add48 (e : BitVec 64) (a b : Nat) (h : b = a + 48) :
    BitVec.setWidth 64 (Int64.toBitVec 48) + (e + BitVec.ofNat 64 a) = e + BitVec.ofNat 64 b := by
  rw [BitVec.add_comm, BitVec.add_assoc,
    show BitVec.setWidth 64 (Int64.toBitVec 48) = BitVec.ofNat 64 48 from rfl, ← BitVec.ofNat_add,
    h]

/-- `48 * n` as `mov %r8d,%ecx; lea (%rcx,%rcx,2),%rcx; shl $4,%rcx` computes it. -/
theorem rcx48 (n : Nat) (h : n ≤ 8) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))
        + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) * 2#64 + Int64.toBitVec 0)
      <<< ((Int64.toBitVec 4).toNat % 256 % 64) = BitVec.ofNat 64 (48 * n) := by
  have h1 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [show (Int64.toBitVec 4).toNat % 256 % 64 = 4 from rfl,
    show Int64.toBitVec 0 = 0#64 from rfl, h1, BitVec.add_zero,
    show BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64 = BitVec.ofNat 64 (3 * n) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- Offsets into `env_facs_q` (`0x151e0 = 86496`). -/
theorem efq_off0 (b : BitVec 64) (c : Nat) (hc : c < 2 ^ 32) :
    (b + BitVec.ofNat 64 c + Int64.toBitVec 86496 - (b + 0x151e0#64)).toNat = c := by
  rw [show Int64.toBitVec 86496 = 0x151e0#64 from rfl,
    show b + BitVec.ofNat 64 c + 0x151e0#64 - (b + 0x151e0#64) = BitVec.ofNat 64 c by bv_omega,
    BitVec.toNat_ofNat]
  omega

theorem efq_off16 (b : BitVec 64) (c : Nat) (hc : c < 2 ^ 32) :
    (b + BitVec.ofNat 64 c + Int64.toBitVec 86512 - (b + 0x151e0#64)).toNat = c + 16 := by
  rw [show Int64.toBitVec 86512 = 0x151f0#64 from rfl,
    show b + BitVec.ofNat 64 c + 0x151f0#64 - (b + 0x151e0#64) = BitVec.ofNat 64 (c + 16) by
      bv_omega,
    BitVec.toNat_ofNat]
  omega

theorem efq_c0 (b : BitVec 64) : (b + Int64.toBitVec 86496 - (b + 0x151e0#64)).toNat = 0 := by
  rw [show Int64.toBitVec 86496 = 0x151e0#64 from rfl, BitVec.sub_self, BitVec.toNat_zero]

theorem efq_c16 (b : BitVec 64) : (b + Int64.toBitVec 86512 - (b + 0x151e0#64)).toNat = 16 := by
  rw [show Int64.toBitVec 86512 = 0x151f0#64 from rfl,
    show b + 0x151f0#64 - (b + 0x151e0#64) = 16#64 by bv_omega]
  rfl

variable [CodeEnv]

section Efq

variable {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
  {t₀ : MachineData} {fv : FV} {i : BitVec 32}

theorem T_efq_ld (h : m =⋆ T k Ext x ra t₀ fv i) (addr : BitVec 64) (n : Nat)
    (hin : (addr - (arg3 t₀ + 0x151e0#64)).toNat + n ≤ 432) : (m.loadInt addr n).isSome = true := by
  obtain ⟨F, hF⟩ := T_efq k Ext x ra t₀ fv i
  rw [hF] at h
  exact Block.loadInt_isSome h hin

theorem T_efq_st (h : m =⋆ T k Ext x ra t₀ fv i) (addr : BitVec 64) (n : Nat)
    (hin : (addr - (arg3 t₀ + 0x151e0#64)).toNat + n ≤ 432) (v : Int) :
    m.storeInt addr n v =⋆ T k Ext x ra t₀ fv i := by
  obtain ⟨F, hF⟩ := T_efq k Ext x ra t₀ fv i
  rw [hF] at h ⊢
  exact Block.storeInt h hin v

end Efq

theorem blk_L6019 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L6019" := by
  cfg_block
  measure_hb "L6019"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15⟩, hn⟩ :=
      hs₀
    have hne := T_ld_nenv hm
    have hl58 := T_ld_f58 hm
    have hs58 := T_st_f58 hm
    have hmT : Hide _ := hm
    clear hm
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hr9 : (BitVec.ofNat 64 i + 1).toNat = i + 1 := by
      rw [show BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) by rw [BitVec.ofNat_add]; rfl,
        BitVec.toNat_ofNat]
      omega
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rsimp; rw [h15, show Int64.toBitVec 8 = 8#64 from rfl, hne]; rfl
    · rename_i nv hnv hc
      rsimp at hnv; rw [h15, show Int64.toBitVec 8 = 8#64 from rfl, hne] at hnv; cases hnv
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, ⟨hC, ?_, ?_, hgi, hmT⟩, ?_, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; rw [c4_val, sw_ofNat x.v.nenv (by omega)]
      · rsimp; exact h15
      · rw [var_L606a, var_L6019, fi_eq hbp hmT, h68, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
        omega
    · rsimp; rw [hbp, hl58]; rfl
    · rename_i nv hnv hc v58 hv58
      rsimp at hv58; rw [hbp, hl58] at hv58; cases hv58
      rsimp; rw [hbp, T_ld_f60 (hs58 _)]; rfl
    all_goals
      rename_i nv hnv hc v58 hv58 v60 hv60 hz
      rsimp at hnv; rw [h15, show Int64.toBitVec 8 = 8#64 from rfl, hne] at hnv; cases hnv
      rsimp at hv58; rw [hbp, hl58] at hv58; cases hv58
      rsimp at hv60; rw [hbp, T_ld_f60 (hs58 _)] at hv60; cases hv60
      rsimp at hc hz
      rw [h9, c4_val, sw_ofNat _ (by omega)] at hc
      rw [h9] at hz
      rw [CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl, hr9, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)] at hc
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hc
    · rsimp
      rw [hbp]
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨_, gi, i + 1, ⟨⟨hC, ?_, ?_, hgi, T_st_f60 (hs58 _) _⟩, ?_⟩, hFC,
        ⟨hc, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
        rw [hLI.2.1]; exact add48 _ (48 * (i + 1)) (48 * (i + 1 + 1)) (by omega)
      · simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
        rw [hLI.2.2]; exact add48 _ (48 * (i + 1) + 1) (48 * (i + 1 + 1) + 1) (by omega)
      · rsimp; rw [h9, BitVec.ofNat_add]; rfl
      · rsimp; exact h15
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rw [var_L58fd, var_L6019, fi_eq hbp hmT, h68, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rsimp
        rw [h9, hr9]; omega
    · rw [CondCode.interp_nz, Bool.not_eq_false', ← CondCode.interp_z, z_sub_iff] at hz
      have := congrArg BitVec.toNat hz
      rw [hr9] at this
      simp only [show (BitVec.setWidth 64 (Int64.toBitVec 9)).toNat = 9 from rfl] at this
      omega

theorem blk_L606a (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L606a" := by
  cfg_block
  measure_hb "L606a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩, h8, h15⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals rename_i hc
    all_goals try rsimp at hc
    all_goals rw [h8, CondCode.interp_nc, ← CondCode.interp_c, c_sub _ _ _ rfl] at hc
    all_goals simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hc
    · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hc
      exfalso
      revert hc
      rw [show (Int64.toBitVec 10).toNat = 10 from rfl]
      omega
    · refine ⟨⟨fv, gi, ⟨hC, ?_, ?_, hgi, hm⟩, ?_, ?_, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact h8
      · rsimp; exact h15
      · rsimp; rfl
      · rw [var_L6075, var_L606a]; try exact Nat.le_refl _

theorem blk_L6075 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L6075" := by
  cfg_block
  measure_hb "L6075"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, ⟨hC, hsp, hbp, hgi, hm⟩, h8, h15, hax⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hif : ((Int64.toBitVec 4).toNat % 256 % 64 = 0) = False := eq_false (by decide)
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hif, ↓reduceIte] at *
    all_goals rsimp
    all_goals simp only [h8, h15, rcx48 _ hn8] at ⊢
    all_goals
      have e0 := efq_off0 (t₀.regs.get64 .rcx) (48 * x.v.nenv) (by omega)
      have e16 := efq_off16 (t₀.regs.get64 .rcx) (48 * x.v.nenv) (by omega)
      have c0 := efq_c0 (t₀.regs.get64 .rcx)
      have c16 := efq_c16 (t₀.regs.get64 .rcx)
      have hal : (t₀.regs.get64 .rcx).toNat % 32 = 0 := hC.2.2.2.2.2.2.2.2
    · exact T_efq_ld hm _ 32 (by rw [show arg3 t₀ = t₀.regs.get64 .rcx from rfl, e0]; omega)
    · exact T_efq_ld hm _ 32 (by rw [show arg3 t₀ = t₀.regs.get64 .rcx from rfl, e16]; omega)
    · exact T_efq_ld hm _ 32 (by rw [show arg3 t₀ = t₀.regs.get64 .rcx from rfl, c16]; omega)
    · simp only [isAligned, beq_iff_eq]
      rw [BitVec.toNat_add, show (Int64.toBitVec 86496).toNat = 86496 from rfl]
      omega
    · exact loadInt_isSome_storeInt _ _ _ _ _ _ (T_efq_ld hm _ 32 (by rw [show arg3 t₀ = t₀.regs.get64 .rcx from rfl, c0]; omega))
    · refine ⟨⟨fv, gi, ⟨hC, ?_, ?_, hgi,
        T_efq_st (T_efq_st hm _ 32 (by rw [show arg3 t₀ = t₀.regs.get64 .rcx from rfl, c16]; omega) _) _ 32 (by rw [show arg3 t₀ = t₀.regs.get64 .rcx from rfl, c0]; omega) _⟩,
        ?_⟩, ?_⟩
      · exact hsp
      · exact hbp
      · left; rsimp; rw [hax]; rfl
      · rw [var_L60a6, var_L6075]; try exact Nat.le_refl _

end Kraken.Examples.Sbr.Env
