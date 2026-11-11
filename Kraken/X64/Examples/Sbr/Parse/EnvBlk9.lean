import Kraken.X64.Examples.Sbr.Parse.EnvBlk6
import Kraken.X64.Examples.Sbr.Parse.EnvBlk7

/-!
# `read_sbr_envelope`: the setup (`L57ef` … `L58f1`)

The table selection (`t_huff`, `f_huff` from `ff_aac_sbr_vlc`) and the frame stores before the
envelope loop.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (Hide eq_r eq_l eq_h)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Env

variable [CodeEnv]

/-- A store into the raw 8 bytes at `rbp - 0x30` keeps `T`. -/
theorem enD_st_r30 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i)
    (c : Int64) (n : Nat) (hc : (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec c
      - (t₀.regs.get64 .rsp - 0x38#64)).toNat + n ≤ 8) (v : Int) :
    m.storeInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec c) n v =⋆ T k Ext x ra t₀ fv i := by
  rw [T_frw] at h ⊢
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r
      (eq_r (eq_r (eq_r (eq_r eq_t)))))))))))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h ⊢
  exact Block.storeInt h hc v

/-- A load from the raw 8 bytes at `rbp - 0x30` succeeds. -/
theorem enD_ld_r30 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i)
    (c : Int64) (n : Nat) (hc : (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec c
      - (t₀.regs.get64 .rsp - 0x38#64)).toNat + n ≤ 8) :
    (m.loadInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec c) n).isSome = true := by
  rw [T_frw] at h
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r
      (eq_r (eq_r (eq_r (eq_r eq_t)))))))))))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h
  exact Block.loadInt_isSome h hc

omit [CodeEnv] in
theorem enD_hc2d (r : BitVec 64) :
    (r - 8#64 + Int64.toBitVec (-45) - (r - 0x38#64)).toNat + 1 ≤ 8 := by
  rw [fa_2d, show r - 0x35#64 - (r - 0x38#64) = 3#64 by bv_omega]; decide

omit [CodeEnv] in
theorem enD_hc2c (r : BitVec 64) :
    (r - 8#64 + Int64.toBitVec (-44) - (r - 0x38#64)).toNat + 4 ≤ 8 := by
  rw [fa_2c, show r - 0x34#64 - (r - 0x38#64) = 4#64 by bv_omega]; decide

/-- A 4-byte load from the raw slot at `rbp - 0x70` succeeds. -/
theorem enD_ld_f70 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i) :
    (m.loadInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-112)) 4).isSome = true := by
  rw [fa_70]
  rw [T_frw] at h
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 4 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r eq_h)))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h
  exact Block.loadInt_isSome h (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- A 4-byte store into the raw slot at `rbp - 0x70` keeps `T`. -/
theorem enD_st_f70 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i) (v : Int) :
    m.storeInt (t₀.regs.get64 .rsp - 8#64 + Int64.toBitVec (-112)) 4 v
      =⋆ T k Ext x ra t₀ fv i := by
  rw [fa_70]
  rw [T_frw] at h ⊢
  obtain ⟨F, e⟩ : ∃ F, FrW (t₀.regs.get64 .rsp) fv = 4 ?@ (t₀.regs.get64 .rsp - 0x78#64) ⋆ F :=
    ⟨_, by simp only [FrW]; exact eq_r (eq_r (eq_r (eq_r (eq_r (eq_r eq_h)))))⟩
  rw [e, Std.ExtHashMap.sep_assoc] at h ⊢
  exact Block.storeInt h (by simp) v

omit [CodeEnv] in
theorem enD_z {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (a - b) f) = decide (a = b) := by
  by_cases h : a = b
  · rw [(z_sub_iff a b f).2 h]; simp [h]
  · have : ¬ (CondCode.z.interp (StatusFlags.from_result (a - b) f) = true) :=
      fun e => h ((z_sub_iff a b f).1 e)
    simp only [Bool.not_eq_true] at this; rw [this]; simp [h]

omit [CodeEnv] in
theorem enD_nz {w : Nat} (a b : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = !decide (a = b) := by
  rw [CondCode.interp_nz, ← CondCode.interp_z, enD_z]

omit [CodeEnv] in
theorem enD_sel (b : Bool) :
    BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64).replaceLow (BitVec.ofNat 8 b.toNat))
      <<< ((Int64.toBitVec 5).toNat % 32)) = if b then 32#64 else 0#64 := by
  cases b <;> rfl

omit [CodeEnv] in
theorem enD_nenv0 {x : EArgs} (hC : DWF False x.v) :
    (BitVec.ofNat 32 x.v.nenv = 0#32) ↔ x.v.nenv = 0 := by
  have := hC.2.2.2.2.1
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this <;> omega
  · intro h; rw [h]

theorem blk_L57ef (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L57ef" := by
  cfg_block
  measure_hb "L57ef"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hdi, hsi, h15, hcpl, h12, h14⟩, hn⟩ := hs₀
    have la : s₀.dmem.loadInt (s₀.regs.get64 .r15 + Int64.toBitVec 100) 4
        = some (Int.ofBytes (Int.toBytes 4 x.amp.toInt)) := by
      rw [h15, show Int64.toBitVec 100 = 0x64#64 from rfl]; exact T_ld_amp hm
    have ln : s₀.dmem.loadInt (s₀.regs.get64 .r15 + Int64.toBitVec 8) 4
        = some (Int.ofBytes (Int.toBytes 4 (x.v.nenv : Int))) := by
      rw [h15, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_ld_nenv hm
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    all_goals try simp only [la, ln, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [cell4_val, c4_val, enD_z, enD_nz, BitVec.setWidth_zero,
      show BitVec.setWidth 32 (Int64.toBitVec 0) = 0#32 from rfl] at *
    all_goals try simp only [Reg64s.get_low32] at *
    all_goals try rsimp at *
    all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero, enD_sel] at *
    all_goals try (case vc2 => decide)
    · have hne : x.v.nenv ≠ 0 := by
        intro h0; rename_i hz; simp [h0] at hz
      have pk : kt x t₀ = if x.amp = 0#32 then 2 else 6 := by
        show (if cpl x t₀ then _ else _) = _; rw [ite_eq_left_of_eq_true _ _ (eq_true hcpl)]
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, ⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩,
        Or.inr ⟨?_, by decide⟩⟩
      all_goals try rsimp
      all_goals first
        | exact hsp
        | exact hbp
        | exact hdx
        | exact hdi
        | exact hsi
        | exact h15
        | exact h12
        | exact h14
        | (rw [var_L5893, var_L57ef])
        | skip
      all_goals rw [pk]; by_cases ha : x.amp = 0#32 <;> simp only [ha, decide_true, decide_false,
        Bool.not_true, Bool.not_false, ↓reduceIte, Int64.toBitVec_ofNat_norm,
        BitVec.reduceSetWidth, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero, VA,
        Bool.false_eq_true, lab] <;> bv_omega
    · have h0 : x.v.nenv = 0 := by
        rename_i hz; simpa [enD_nenv0 hC.1] using hz
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, x.idx, ⟨hC, ?_, ?_, hgi, hmT⟩, ?_, ?_, ?_⟩, Or.inl ?_⟩
      all_goals try rsimp
      all_goals first
        | exact hsp
        | exact hbp
        | exact h15
        | (rw [var_L6075, var_L57ef]; decide)
        | (simp [h0]; done)
        | rfl

theorem blk_L584c (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L584c" := by
  cfg_block
  measure_hb "L584c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hdi, hsi, h15, hcpl, h12, h14⟩, hn⟩ := hs₀
    have la : s₀.dmem.loadInt (s₀.regs.get64 .r15 + Int64.toBitVec 100) 4
        = some (Int.ofBytes (Int.toBytes 4 x.amp.toInt)) := by
      rw [h15, show Int64.toBitVec 100 = 0x64#64 from rfl]; exact T_ld_amp hm
    have ln : s₀.dmem.loadInt (s₀.regs.get64 .r15 + Int64.toBitVec 8) 4
        = some (Int.ofBytes (Int.toBytes 4 (x.v.nenv : Int))) := by
      rw [h15, show Int64.toBitVec 8 = 8#64 from rfl]; exact T_ld_nenv hm
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    all_goals try simp only [la, ln, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [cell4_val, c4_val, enD_z, enD_nz, BitVec.setWidth_zero,
      show BitVec.setWidth 32 (Int64.toBitVec 0) = 0#32 from rfl] at *
    all_goals try simp only [Reg64s.get_low32] at *
    all_goals try rsimp at *
    all_goals try simp only [BitVec.xor_self, BitVec.setWidth_zero, enD_sel] at *
    all_goals try (case vc2 => decide)
    · have h0 : x.v.nenv = 0 := by
        rename_i hz; simpa [enD_nenv0 hC.1] using hz
      left; apply Table.ofLabels_at
      refine ⟨by decide, ⟨fv, x.idx, ⟨hC, ?_, ?_, hgi, hmT⟩, ?_, ?_, ?_⟩, Or.inl ?_⟩
      all_goals try rsimp
      all_goals first
        | exact hsp
        | exact hbp
        | exact h15
        | (rw [var_L6075, var_L584c]; decide)
        | (simp [h0]; done)
        | rfl
    · have hne : x.v.nenv ≠ 0 := by
        intro h0; rename_i hz; simp [h0] at hz
      have pk : kt x t₀ = if x.amp = 0#32 then 0 else 4 := by
        show (if cpl x t₀ then _ else _) = _; rw [ite_eq_right_of_eq_false _ _ (eq_false hcpl)]
      refine ⟨⟨fv, ⟨⟨hC, ?_, ?_, hgi, hmT⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩, ?_⟩
      all_goals try rsimp
      all_goals first
        | exact hsp
        | exact hbp
        | exact hdx
        | exact hdi
        | exact hsi
        | exact h15
        | exact h12
        | exact h14
        | (rw [var_L5893, var_L584c]; try exact Nat.le_refl _)
        | skip
      all_goals rw [pk]; by_cases ha : x.amp = 0#32 <;> simp only [ha, decide_true, decide_false,
        Bool.not_true, Bool.not_false, ↓reduceIte, Int64.toBitVec_ofNat_norm,
        BitVec.reduceSetWidth, Nat.reduceMul, Nat.reduceAdd, BitVec.add_zero, VA,
        Bool.false_eq_true, lab] <;> bv_omega

theorem enD_vld {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (h : m =⋆ T k Ext x ra t₀ fv i) (K : Nat)
    (hK : K < 10) :
    m.loadInt (VA + BitVec.ofNat 64 (8 * K)) 8
      = some (Int.ofBytes (Int.toBytes 8 (x.vt K).p.toInt)) := by
  obtain ⟨F, hF⟩ := T_vlc k Ext x ra t₀ fv i
  rw [hF] at h
  exact vlc_load_ptr h K hK

omit [CodeEnv] in
theorem enD_kt (x : EArgs) (t₀ : MachineData) : kt x t₀ ≤ 6 := by
  simp only [kt]; split <;> split <;> omega

theorem blk_L5893 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L5893" := by
  cfg_block
  measure_hb "L5893"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hdi, hsi, h15, h12, h14, hcx, h9, hnv⟩, hn⟩ := hs₀
    have hkt := enD_kt x t₀
    have hs50 := T_st_f50 hm
    have hv1 := fun w => enD_vld (hs50 w) (kt x t₀ + 1) (by omega)
    have hs98 := fun w w' => T_st_f98 (hs50 w) w'
    have hv2 := fun w w' => enD_vld (hs98 w w') (kt x t₀) (by omega)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [show Int64.toBitVec 0 = 0#64 from rfl] at *
    all_goals try rsimp at *
    · rw [hbp, T_ld_f50 hmT]; rfl
    · rw [hbp, h9, hv1]; rfl
    · rw [hbp, T_ld_f98 (hs50 _)]; rfl
    · rename_i v1 hv1'
      rw [hbp, h9, hv1] at hv1'; cases hv1'
      rw [hbp, hcx, hv2]; rfl
    · rename_i v1 v2 hv1' hv2'
      rw [hbp, h9, hv1] at hv1'; cases hv1'
      rw [hbp, hcx, hv2] at hv2'; cases hv2'
      refine ⟨?_, ?_⟩
      · apply Exists.intro
        refine ⟨⟨⟨hC, ?_, ?_, hgi, ?hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, hnv, ?_, ?_⟩
        case hm => rsimp; rw [hbp]; exact hs98 _ _
        all_goals try rsimp
        all_goals first
          | exact hsp
          | exact hbp
          | exact hdx
          | exact hsi
          | exact h15
          | exact h12
          | exact h14
          | exact hdi
          | (rw [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt])
          | skip
      · rw [var_L58a4, var_L5893]; try exact Nat.le_refl _

theorem blk_L58a4 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L58a4" := by
  cfg_block
  measure_hb "L58a4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hsi, h15, h12, h14, h13, hnv, h50, h98⟩, hn⟩ := hs₀
    have hl2d := enD_ld_r30 hm (-45) 1 (enD_hc2d _)
    have hs2d := enD_st_r30 hm (-45) 1 (enD_hc2d _)
    have hl90 := fun v => T_ld_f90 (hs2d v)
    have hs90 := fun v w => T_st_f90 (hs2d v) w
    have hl88 := fun v w => T_ld_f88 (hs90 v w)
    have hs88 := fun v w w' => T_st_f88 (hs90 v w) w'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    · rw [hbp]; exact hl2d
    · rw [hbp, hl90]; rfl
    · rw [hbp, hl88]; rfl
    · refine ⟨?_, ?_⟩
      · apply Exists.intro
        refine ⟨⟨⟨hC, ?_, ?_, hgi, ?hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, hnv, ?_, ?_, ?_, ?_⟩
        case hm => rsimp; rw [hbp]; exact hs88 _ _ _
        all_goals try rsimp
        all_goals first
          | exact hsp
          | exact hbp
          | exact hdx
          | exact hsi
          | exact h15
          | exact h12
          | exact h14
          | exact h13
          | exact h50
          | exact h98
          | skip
        all_goals
          rw [h14]
          have ho : x.n1 % 2 < 2 := Nat.mod_lt _ (by decide)
          simp only [odd]
          generalize x.n1 % 2 = o at *
          rcases (by omega : o = 0 ∨ o = 1) with rfl | rfl <;> rfl
      · rw [var_L58c5, var_L58a4]; try exact Nat.le_refl _

theorem blk_L58c5 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L58c5" := by
  cfg_block
  measure_hb "L58c5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hsi, h15, h12, h14, h13, hnv, h50, h98, h90, h88⟩,
      hn⟩ := hs₀
    have hl58 := T_ld_f58 hm
    have hs58 := T_st_f58 hm
    have hl6c := fun v => T_ld_f6c (hs58 v)
    have hs6c := fun v w => T_st_f6c (hs58 v) w
    have hl60 := fun v w => T_ld_f60 (hs6c v w)
    have hs60 := fun v w w' => T_st_f60 (hs6c v w) w'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    · rw [hbp, hl58]; rfl
    · rw [hbp, hl6c]; rfl
    · rw [hbp, hl60]; rfl
    · refine ⟨?_, ?_⟩
      · apply Exists.intro
        refine ⟨⟨⟨hC, ?_, ?_, hgi, ?hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?li⟩
        case hm => rsimp; rw [hbp]; exact hs60 _ _ _
        case li =>
          refine ⟨hnv, ?_, ?_⟩ <;> dsimp only <;> rw [h15] <;>
            simp only [EQ, arg3, show Int64.toBitVec 86544 = 0x15210#64 from rfl,
              show Int64.toBitVec 86545 = 0x15211#64 from rfl] <;> bv_omega
        · (try rsimp); exact hsp
        · (try rsimp); exact hbp
        · (try rsimp); exact hdx
        · (try rsimp); exact hsi
        · (try rsimp); exact h15
        · show (_ : BitVec 64) = _; rsimp; exact h12
        · (try rsimp); exact h13
        · exact h50
        · exact h98
        · exact h90
        · exact h88
        · dsimp only
          rw [h14]
          have ho : x.n1 % 2 < 2 := Nat.mod_lt _ (by decide)
          simp only [odd]
          generalize x.n1 % 2 = o at *
          rcases (by omega : o = 0 ∨ o = 1) with rfl | rfl <;> rfl
      · rw [var_L58e6, var_L58c5]; try exact Nat.le_refl _

theorem blk_L58e6 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L58e6" := by
  cfg_block
  measure_hb "L58e6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, hsi, h15, h12, h13, h50, h98, h90, h88, h6c, hLI⟩,
      hn⟩ := hs₀
    have hl78 := T_ld_f78 hm
    have hs78 := T_st_f78 hm
    have hl2c := fun v => enD_ld_r30 (hs78 v) (-44) 4 (enD_hc2c _)
    have hs2c := fun v => enD_st_r30 (hs78 v) (-44) 4 (enD_hc2c _)
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    · rw [hbp, hl78]; rfl
    · rw [hbp]; exact hl2c _
    · refine ⟨?_, ?_⟩
      · apply Exists.intro
        refine ⟨⟨⟨hC, ?_, ?_, hgi, ?hm⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        case hm => rsimp; rw [hbp]; exact hs2c _ _
        · (try rsimp); exact hsp
        · (try rsimp); exact hbp
        · (try rsimp); exact hdx
        · (try rsimp); exact h15
        · rsimp; simp only [BitVec.xor_self, BitVec.setWidth_zero]
        · show (_ : BitVec 64) = _; rsimp; exact h12
        · (try rsimp); exact h13
        · exact h50
        · exact h98
        · exact h90
        · exact h88
        · exact h6c
        · exact hLI
        · exact hsi
      · rw [var_L58f1, var_L58e6]; try exact Nat.le_refl _


theorem blk_L58f1 (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_envelope.L58f1" := by
  cfg_block
  measure_hb "L58f1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨fv, ⟨⟨hC, hsp, hbp, hgi, hm⟩, hdx⟩, h15, h9, h12, h13, h50, h98, h90, h88, h6c, hLI,
      h78⟩, hn⟩ := hs₀
    have hl40 := T_ld_f40 hm
    have hs40 := T_st_f40 hm
    have hl70 := fun v => enD_ld_f70 (hs40 v)
    have hs70 := fun v w => enD_st_f70 (hs40 v) w
    have hl38 := fun v w => T_ld_f38 (hs70 v w)
    have hs38 := fun v w w' => T_st_f38 (hs70 v w) w'
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try rsimp at *
    · rw [hbp, hl40]; rfl
    · rw [hbp]; exact hl70 _
    · rw [hbp, hl38]; rfl
    · refine ⟨?_, ?_⟩
      · apply Exists.intro
        refine ⟨x.idx, 0, ⟨⟨hC, ?_, ?_, hgi, ?hm⟩, ?_⟩, ?frc, ?li, ?_, ?_, ?_, ?_⟩
        case hm => rsimp; rw [hbp]; exact hs38 _ _ _
        case li => exact hLI
        case frc =>
          refine ⟨h98, h90, h88, h78, h6c, h50, ?_, ?_⟩
          · exact h12
          · exact h15
        · (try rsimp); exact hsp
        · (try rsimp); exact hbp
        · (try rsimp); exact hdx
        · (try rsimp); exact h9
        · (try rsimp); exact h15
        · (try rsimp); exact h13
        · show (_ : BitVec 64) = _; rsimp; exact h12
      · rw [var_L58fd, var_L58f1]; rsimp; rw [h9]; decide


end Kraken.Examples.Sbr.Env
