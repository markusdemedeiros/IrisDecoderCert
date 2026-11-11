import Kraken.X64.Examples.Sbr.Parse.EnvBlk3

/-!
# `read_sbr_envelope`: the per-envelope dispatch on `bs_df_env` and the resolutions
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

theorem zx8 (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b])))
      = BitVec.ofNat 64 b.toNat := by
  have := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, Int.ofBytes_cons, Int.ofBytes, List.foldr, BitVec.toNat_ofInt,
    BitVec.toNat_ofNat]
  omega

theorem r9_succ (i : Nat) : BitVec.ofNat 64 i + Int64.toBitVec 1 = BitVec.ofNat 64 (i + 1) := by
  rw [show Int64.toBitVec 1 = 1#64 from rfl, BitVec.ofNat_add]

theorem row48 (n : Nat) (h : n ≤ 9) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64 + Int64.toBitVec 0)
      <<< ((Int64.toBitVec 4).toNat % 256 % 64) = BitVec.ofNat 64 (48 * n) := by
  rw [show (Int64.toBitVec 4).toNat % 256 % 64 = 4 from rfl,
    show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega

theorem row48' (n : Nat) (h : n ≤ 9) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64)
      <<< ((Int64.toBitVec 4).toNat % 256 % 64) = BitVec.ofNat 64 (48 * n) := by
  have := row48 n h
  rwa [show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero] at this

theorem zx8n (b : Nat) (h : b < 256) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 b)))
      = BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem zf_and {w : Nat} (a : BitVec w) (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result (a &&& a) f).zf = true ↔ a = 0#w := z_and_iff a f

theorem zf_sub {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result (a - b) f).zf = true ↔ a = b := z_sub_iff a b f

theorem eqrow (b : BitVec 64) (c : Nat) :
    BitVec.setWidth 64 (Int64.toBitVec 86496) + b + BitVec.ofNat 64 c
      = b + Int64.toBitVec 86496 + BitVec.ofNat 64 c := by
  rw [show BitVec.setWidth 64 (Int64.toBitVec 86496) = Int64.toBitVec 86496 from rfl,
    BitVec.add_comm (Int64.toBitVec 86496) b]

theorem efq_row (b : BitVec 64) (c : Nat) (hc : c < 2 ^ 32) :
    (b + Int64.toBitVec 86496 + BitVec.ofNat 64 c - (b + 0x151e0#64)).toNat = c := by
  rw [show Int64.toBitVec 86496 = 0x151e0#64 from rfl,
    show b + 0x151e0#64 + BitVec.ofNat 64 c - (b + 0x151e0#64) = BitVec.ofNat 64 c by bv_omega,
    BitVec.toNat_ofNat]
  omega

variable [CodeEnv]

theorem fi_f48 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} {regs : Reg64s} {zmms} {status}
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (h : m =⋆ T k Ext x ra t₀ fv i)
    (w : BitVec 64) :
    fi (MachineData.mk regs zmms status
      (m.storeInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-72)) 8 w.toInt))
      = fv.f68.toNat := by
  rw [fi_eq' regs zmms status _ hbp (T_st_f48 h w)]

theorem fi_f80 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} {regs : Reg64s} {zmms} {status}
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (h : m =⋆ T k Ext x ra t₀ fv i)
    (w : BitVec 64) :
    fi (MachineData.mk regs zmms status
      (m.storeInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-128)) 8 w.toInt))
      = fv.f68.toNat := by
  rw [fi_eq' regs zmms status _ hbp (T_st_f80 h w)]

theorem fi_efq {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} {regs : Reg64s} {zmms} {status}
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) (h : m =⋆ T k Ext x ra t₀ fv i)
    (addr : BitVec 64) (n : Nat) (hin : (addr - (arg3 t₀ + 0x151e0#64)).toNat + n ≤ 432) (v : Int) :
    fi (MachineData.mk regs zmms status (m.storeInt addr n v)) = fv.f68.toNat := by
  rw [fi_eq' regs zmms status _ hbp (T_efq_st h addr n hin v)]

theorem blk_L590d (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L590d" := by
  cfg_block
  measure_hb "L590d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15⟩, hn⟩ :=
      hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hs48 := T_st_f48 hm
    have hf1 := fun v => T_ld_fr (hs48 v) hC i 1 (by omega) 13 rfl
    have hf0 := fun v => T_ld_fr (hs48 v) hC i 0 (by omega) 12 rfl
    have hl48 := T_ld_f48 hm
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rename_i hz
      exfalso
      try rsimp at hz
      rw [z_sub_iff, h9] at hz
      have := congrArg BitVec.toNat hz
      simp only [BitVec.toNat_ofNat, show (BitVec.setWidth 64 (Int64.toBitVec 8)).toNat = 8 from rfl]
        at this
      omega
    · rsimp; rw [hbp, hl48]; rfl
    · rsimp; rw [hbp, h15, h9, hf1]; rfl
    · rename_i v1 hv1
      rsimp at hv1; rw [hbp, h15, h9, hf1] at hv1; cases hv1
      rsimp; rw [hbp, h15, h9, hf0]; rfl
    · rename_i v1 hv1 v2 hv2 hc
      rsimp at hv1 hv2; rw [hbp, h15, h9, hf1] at hv1; rw [hbp, h15, h9, hf0] at hv2
      cases hv1; cases hv2
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨{ fv with f48 := BitVec.ofNat 64 (i + 1) }, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, ?_⟩, ?_⟩, hFC, hLI, h68,
        ?_⟩, ?_, ?_, ?_⟩,
        Or.inr ⟨?_, by decide⟩⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; rw [hbp, h9, r9_succ]; exact hs48 _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rfl
      · rsimp; rw [zx8]
      · rw [var_L5be0, var_L590d, fi_eq hbp hmT]
        rsimp
        rw [hbp, fi_f48 ?hb hmT]
        case hb => (try rsimp); exact hbp
        all_goals rfl
    · rename_i v1 hv1 v2 hv2 hc
      rsimp at hv1 hv2; rw [hbp, h15, h9, hf1] at hv1; rw [hbp, h15, h9, hf0] at hv2
      cases hv1; cases hv2
      refine ⟨⟨{ fv with f48 := BitVec.ofNat 64 (i + 1) }, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, ?_⟩, ?_⟩, hFC, hLI, h68,
        ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; rw [hbp, h9, r9_succ]; exact hs48 _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rfl
      · rsimp; rw [zx8]
      · rw [var_L5930, var_L590d, fi_eq hbp hmT]
        rsimp
        rw [hbp, fi_f48 ?hb hmT]
        case hb => (try rsimp); exact hbp
        all_goals exact Nat.le_refl _

theorem blk_L5930 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5930" := by
  cfg_block
  measure_hb "L5930"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h48, hax⟩, hn⟩ :=
      hs₀
    have hi := hLI.1
    have hfr : u8 x.v.freqRes (i + 1) = 0 ∨ u8 x.v.freqRes (i + 1) = 1 := by
      have := hC.1.2.2.2.2.2.1 (i + 1) (by omega); omega
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rename_i hc
      exfalso
      rw [hax] at hc
      try simp only [fr] at hc
      rcases hfr with h | h <;> rw [h] at hc <;> revert hc <;> decide
    · rename_i b hc
      refine ⟨⟨fv, gi, i, 0, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, h48, ?_, by omega, ?_⟩,
        ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; simp only [BitVec.xor_self]; rfl
      · rsimp; exact hax
      · rw [var_L5940, var_L5930, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        rsimp
        simp only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero]
        omega

theorem blk_L5a95 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5a95" := by
  cfg_block
  measure_hb "L5a95"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h9, h15⟩,
      hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have hfr : u8 x.v.freqRes (i + 1) = 0 ∨ u8 x.v.freqRes (i + 1) = 1 := by
      have := hC.1.2.2.2.2.2.1 (i + 1) (by omega); omega
    have hes := T_efq_st hm
    have hel := T_efq_ld hm
    have hrow : (arg3 t₀ + Int64.toBitVec 86496 + BitVec.ofNat 64 (48 * (i + 1))
        - (arg3 t₀ + 0x151e0#64)).toNat + 1 ≤ 432 := by rw [efq_row _ _ (by omega)]; omega
    have hfS := fun v => T_ld_fr (hes _ 1 hrow v) hC i 1 (by omega) 13 rfl
    have hsS := fun v => hes _ 1 hrow v
    have hif4 : ((Int64.toBitVec 4).toNat % 256 % 64 = 0) = False := eq_false (by decide)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif4, ↓reduceIte] at *
    · rsimp
      rw [h15, h9, r9_succ, row48 _ (by omega), show Int64.toBitVec 0 = 0#64 from rfl,
        BitVec.add_zero]
      exact hel _ 1 hrow
    · rsimp
      rw [h15, h9, r9_succ, row48 _ (by omega), show Int64.toBitVec 0 = 0#64 from rfl,
        BitVec.add_zero, hfS]; rfl
    · rename_i b1 b2 b3 b4 b5 b6 b7 v hv hc
      exfalso
      rsimp at hv
      rw [h15, h9, r9_succ, row48 _ (by omega), show Int64.toBitVec 0 = 0#64 from rfl,
        BitVec.add_zero, hfS] at hv
      cases hv
      rsimp at hc
      rw [zx8] at hc
      try simp only [u8] at hfr
      rcases hfr with h | h <;> rw [h] at hc <;> revert hc <;> decide
    · rename_i b1 b2 b3 b4 b5 b6 b7 v b8 hv hc
      rsimp at hv
      rw [h15, h9, r9_succ, row48 _ (by omega), show Int64.toBitVec 0 = 0#64 from rfl,
        BitVec.add_zero, hfS] at hv
      cases hv
      refine ⟨⟨fv, gi, i, 0, ⟨⟨⟨hC, ?_, ?_, hgi, ?_⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ?_, ?_, by omega,
        ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp
        rw [h15, h9, r9_succ, row48 _ (by omega), show Int64.toBitVec 0 = 0#64 from rfl,
          BitVec.add_zero]
        exact hsS _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; rw [h9, r9_succ]
      · rsimp; simp only [BitVec.xor_self]; rfl
      · rsimp; rw [zx8]
      · rw [var_L5ad0, var_L5a95, fi_eq hbp hmT]
        rsimp
        simp only [h15, h9, r9_succ, row48' _ (show i + 1 ≤ 9 by omega), show Int64.toBitVec 0 = 0#64 from rfl,
          BitVec.add_zero]
        rw [fi_efq ?hb hmT _ 1 hrow]
        case hb => (try rsimp); exact hbp
        omega

theorem blk_L5be0 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5be0" := by
  cfg_block
  measure_hb "L5be0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h48, hax⟩, hn⟩ :=
      hs₀
    have hb := (x.v.freqRes.getD (i + 1) 0).toNat_lt
    have hn0 := T_ld_n0 hm
    have hz8 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (fr x (i + 1))))
        = fr x (i + 1) := zx8n _ hb
    have hu : ∀ c : Nat, c < 256 →
        (BitVec.setWidth 32 (BitVec.ofNat 64 c) = 0#32 ↔ c = 0) := by
      intro c hc
      constructor
      · intro h; have := congrArg BitVec.toNat h
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this; omega
      · intro h; subst h; rfl
    have hu' : BitVec.setWidth 32 (fr x (i + 1)) = 0#32 ↔ u8 x.v.freqRes (i + 1) = 0 :=
      hu _ hb
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    · rename_i b hz
      rw [CondCode.interp_nz, Bool.not_eq_true', ← Bool.not_eq_true, zf_and] at hz
      rsimp at hz
      rw [hax, hz8, hu'] at hz
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, h48, ?_, hz⟩, Or.inr ⟨?_, by decide⟩⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; rw [hax, hz8]
      · rw [var_L5ca5, var_L5be0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        all_goals rfl
    · rsimp; rw [h12, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hn0]; rfl
    · rename_i b hz v hv hz2
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_⟩, Or.inl ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rw [var_L5f90, var_L5be0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        all_goals omega
    · rename_i b hz v hv hz2
      rw [CondCode.interp_nz, Bool.not_eq_false', zf_and] at hz
      rw [← Bool.not_eq_true, z_sub_iff] at hz2
      rsimp at hz hv hz2
      rw [hax, hz8, hu'] at hz
      rw [h12, show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, hn0] at hv; cases hv
      rw [c4_val, show BitVec.setWidth 32 (Int64.toBitVec 0) = 0#32 from rfl] at hz2
      have hn0' : 0 < x.n0 := by
        have h24 := hC.2.1
        rcases Nat.eq_zero_or_pos x.n0 with h | h
        · exact absurd (by rw [h]) hz2
        · exact h
      refine ⟨⟨fv, gi, i, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, h48, hz, hn0'⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rw [var_L5bf6, var_L5be0, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        all_goals exact Nat.le_refl _

theorem blk_L5bf6 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5bf6" := by
  cfg_block
  measure_hb "L5bf6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h48, hfr, hn0⟩,
      hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    have hl68 := T_ld_f68 hm
    have hl38 := T_ld_f38 hm
    have hl48 := T_ld_f48 hm
    rw [h68] at hl68; rw [h38] at hl38; rw [h48] at hl48
    have hs80 := T_st_f80 hm
    have hel := fun v => T_efq_ld (hs80 v)
    have hif4 : ((Int64.toBitVec 4).toNat % 256 % 64 = 0) = False := eq_false (by decide)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif4, ↓reduceIte] at *
    · rsimp; rw [hbp, hl68]; rfl
    · rename_i v68 hv68 b1 b2 b3
      rsimp at hv68; rw [hbp, hl68] at hv68; cases hv68
      rsimp; rw [hbp, hl38]; rfl
    · rename_i v68 hv68 b1 b2 b3 v38 hv38
      rsimp at hv68 hv38; rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38; cases hv68; cases hv38
      rsimp; rw [hbp, hl48]; rfl
    · rename_i v68 hv68 b1 b2 b3 v38 v48 b4 b5 b6 hv38 hv48
      rsimp at hv68 hv38 hv48
      rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38; rw [hbp, hl48] at hv48
      cases hv68; cases hv38; cases hv48
      rsimp; rw [hbp, T_ld_f80 hmT]; rfl
    · rename_i v68 hv68 b1 b2 b3 v38 v48 b4 b5 b6 hv38 hv48
      rsimp at hv68 hv38 hv48
      rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38; rw [hbp, hl48] at hv48
      cases hv68; cases hv38; cases hv48
      rsimp
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      rw [hbp, row48 _ (by omega), show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero, eqrow]
      exact hel _ _ 1 (by rw [efq_row _ _ (by omega)]; omega)
    · rename_i v68 hv68 b1 b2 b3 v38 v48 b4 b5 b6 vb hv38 hv48 hvb
      rsimp at hv68 hv38 hv48
      rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38; rw [hbp, hl48] at hv48
      cases hv68; cases hv38; cases hv48
      refine ⟨⟨{ fv with f80 := EQ t₀ + BitVec.ofNat 64 (48 * i) }, gi, i,
        ⟨⟨⟨hC, ?_, ?_, hgi, ?_⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, ⟨h48, hfr, rfl, hn0⟩, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp
        simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
        try rw [hbp]
        try simp only [row48 _ (show i ≤ 9 by omega), row48' _ (show i ≤ 9 by omega),
          show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
        rw [eqrow]
        exact hs80 _
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp
        simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
        rw [row48 _ (by omega), eqrow]
        rfl
      · rw [var_L5c26, var_L5bf6, fi_eq hbp hmT]
        rsimp
        rw [hbp, fi_f80 ?hb hmT]
        case hb => (try rsimp); exact hbp
        all_goals exact Nat.le_refl _

theorem blk_L5ca5 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5ca5" := by
  cfg_block
  measure_hb "L5ca5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, h48, hax, hne⟩,
      hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have h1 : u8 x.v.freqRes (i + 1) = 1 := by
      have := hC.1.2.2.2.2.2.1 (i + 1) (by omega); omega
    have hax1 : s₀.regs.get64 .rax = 1#64 := by rw [hax]; simp only [fr, h1]
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    have hl68 := T_ld_f68 hm
    have hl38 := T_ld_f38 hm
    rw [h68] at hl68; rw [h38] at hl38
    have hif4 : ((Int64.toBitVec 4).toNat % 256 % 64 = 0) = False := eq_false (by decide)
    clear hax
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [hif4, ↓reduceIte] at *
    · rename_i hz
      exfalso
      rw [CondCode.interp_nz, Bool.not_eq_true', ← Bool.not_eq_true, zf_sub] at hz
      try rsimp at hz
      exact hz (by rw [hax1]; rfl)
    · rsimp; rw [hbp, hl68]; rfl
    · rename_i hz v68 hv68 b1 b2 b3
      rsimp at hv68; rw [hbp, hl68] at hv68; cases hv68
      rsimp; rw [hbp, hl38]; rfl
    · rename_i hz v68 hv68 b1 b2 b3 v38 b4 hv38
      rsimp at hv68 hv38; rw [hbp, hl68] at hv68; rw [hbp, hl38] at hv38; cases hv68; cases hv38
      refine ⟨⟨fv, gi, i, 0, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_,
        ⟨h48, h1, ?_, ?_⟩, by omega, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp
        simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
        try simp only [row48' _ (show i ≤ 9 by omega),
          show Int64.toBitVec 0 = 0#64 from rfl, BitVec.add_zero]
        rw [eqrow]; rfl
      · rsimp; simp only [BitVec.xor_self]; rfl
      · rsimp
        rw [BitVec.setWidth_replaceLow8]; rfl
      · rw [var_L5cd0, var_L5ca5, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        all_goals omega

theorem blk_L5e4b (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5e4b" := by
  cfg_block
  measure_hb "L5e4b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, gi, i, ⟨⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hFC, hLI, h68, h13⟩, h12, hJD⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1.2.2.2.2.1
    have hi := hLI.1
    have h38 : fv.f38 = t₀.regs.get64 .rcx := hFC.2.2.2.2.2.2.2
    have h6c : fv.f6c = BitVec.ofNat 32 (2 - odd x) := hFC.2.2.2.2.1
    have hl48 := T_ld_f48 hm
    have hl38 := T_ld_f38 hm
    have hl6c := T_ld_f6c hm
    rw [hJD.1] at hl48; rw [h38] at hl38; rw [h6c] at hl6c
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
    · rename_i v48 hv48 v38 hv38 vf hvf hc
      rsimp at hv48 hv38 hvf
      rw [hbp, hl48] at hv48; cases hv48
      rw [hbp, hl38] at hv38; cases hv38
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hvf
      rw [hfr] at hvf; cases hvf
      exfalso
      rsimp at hc
      rw [zx8] at hc
      try simp only [u8] at hu0
      rw [hu0] at hc
      revert hc; decide
    · rsimp; rw [hbp, hl6c]; rfl
    · rename_i v48 hv48 v38 hv38 vf hvf hc b v6c hv6c
      rsimp at hv48 hv38 hvf
      rw [hbp, hl48] at hv48; cases hv48
      rw [hbp, hl38] at hv38; cases hv38
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at hvf
      rw [hfr] at hvf; cases hvf
      rsimp at hv6c; rw [hbp, hl6c] at hv6c; cases hv6c
      refine ⟨⟨fv, gi, i, 0, ⟨⟨⟨hC, ?_, ?_, hgi, hm⟩, ?_⟩, hFC, hLI, h68, ?_⟩, ?_, hJD, ?_, by omega,
        ?_, ?_⟩, ?_⟩
      · rsimp; exact hsp
      · rsimp; exact hbp
      · rsimp; exact hdx
      · rsimp; exact h13
      · show (_ : BitVec 64) = _; rsimp; exact h12
      · rsimp; simp only [BitVec.xor_self]; rfl
      · rsimp; rw [cell4_val, sw_ofNat _ (by omega)]
      · rsimp; rw [zx8]; try simp only [u8] at hu0
        simp only [Nat.add_zero]; rw [hu0]
      · rw [var_L5e70, var_L5e4b, fi_eq hbp hm, fi_eq' _ _ _ _ ?hb hm]
        case hb => (try rsimp); exact hbp
        all_goals omega

end Kraken.Examples.Sbr.Env
