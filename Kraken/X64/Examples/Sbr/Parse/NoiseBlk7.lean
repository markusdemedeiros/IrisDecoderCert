import Kraken.X64.Examples.Sbr.Parse.NoiseVlc

/-!
# `read_sbr_noise`: the prologue

The six pushes (`entry_mem`: each over a raw slot of `BlankS`), the loads of `bs_coupling` and
`bs_num_noise`, the writes of the locals.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (GbW bswap32_havoc shl_cl32_havoc rd_off gb_clamp gb_clamp64)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- A store over the raw head cell, which then moves behind the next five. -/
theorem st_rot {m : Mem 64} {a v : BitVec 64} {B C D E F W : Mem 64 → Prop}
    (h : m =⋆ 8 ?@ a ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ W)))))) :
    (m.loadInt a 8).isSome = true
    ∧ (m.storeInt a 8 v.toInt =⋆ B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ (c8 a v ⋆ W)))))) := by
  refine ⟨Block.loadInt_isSome h (by simp), ?_⟩
  have h1 := Block.storeInt_val h (Split.here _ _) v.toInt
  exact Mem.ac h1

theorem entry_mem {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
    {i : BitVec 32} {m : Mem 64}
    (h : m =⋆ T k Ext x ra t₀ (Blank t₀) (BlankS (t₀.regs.get64 .rsp)) i)
    (v1 v2 v3 v4 v5 v6 : BitVec 64) :
    let r := t₀.regs.get64 .rsp
    let m1 := m.storeInt (r - 8#64) 8 v1.toInt
    let m2 := m1.storeInt (r - 16#64) 8 v2.toInt
    let m3 := m2.storeInt (r - 24#64) 8 v3.toInt
    let m4 := m3.storeInt (r - 32#64) 8 v4.toInt
    let m5 := m4.storeInt (r - 40#64) 8 v5.toInt
    (m.loadInt (r - 8#64) 8).isSome = true ∧ (m1.loadInt (r - 16#64) 8).isSome = true
    ∧ (m2.loadInt (r - 24#64) 8).isSome = true ∧ (m3.loadInt (r - 32#64) 8).isSome = true
    ∧ (m4.loadInt (r - 40#64) 8).isSome = true ∧ (m5.loadInt (r - 48#64) 8).isSome = true
    ∧ (m5.storeInt (r - 48#64) 8 v6.toInt =⋆ 8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64)
        ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i ⋆ (c8 (r - 0x30#64) v6 ⋆ (c8 (r - 0x28#64) v5
        ⋆ (c8 (r - 0x20#64) v4 ⋆ (c8 (r - 0x18#64) v3 ⋆ (c8 (r - 0x10#64) v2
        ⋆ (c8 (r - 0x8#64) v1 ⋆ Rest x.R ra t₀)))))))))) := by
  intro r m1 m2 m3 m4 m5
  have h0 : m =⋆ 8 ?@ (r - 8#64) ⋆ (8 ?@ (r - 16#64) ⋆ (8 ?@ (r - 24#64) ⋆ (8 ?@ (r - 32#64)
      ⋆ (8 ?@ (r - 40#64) ⋆ (8 ?@ (r - 48#64) ⋆ (8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64)
        ⋆ (Blank t₀ ⋆ (NoiseF Ext x t₀ i ⋆ Rest x.R ra t₀))))))))) := by
    refine Mem.ac h ?_
    simp only [T, BlankS, r]
    ac_rfl
  obtain ⟨l1, h1⟩ := st_rot (v := v1) h0
  obtain ⟨l2, h2⟩ := st_rot (v := v2) h1
  obtain ⟨l3, h3⟩ := st_rot (v := v3) h2
  obtain ⟨l4, h4⟩ := st_rot (v := v4) h3
  obtain ⟨l5, h5⟩ := st_rot (v := v5) h4
  obtain ⟨l6, h6⟩ := st_rot (v := v6) h5
  refine ⟨l1, l2, l3, l4, l5, l6, Mem.ac h6 ?_⟩
  ac_rfl

theorem blk_entry (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    obtain ⟨l1, l2, l3, l4, l5, l6, hE⟩ := entry_mem hm (s₀.regs.get64 .rbp) (s₀.regs.get64 .r15)
      (s₀.regs.get64 .r14) (s₀.regs.get64 .r13) (s₀.regs.get64 .r12) (s₀.regs.get64 .rbx)
    have hE' : PLift _ := ⟨hE⟩
    clear hE hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try nnorm
    all_goals try simp only [BitVec.sub_sub, BitVec.reduceAdd, BitVec.reduceSetWidth] at *
    case vc1 => exact l1
    case vc2 => exact l2
    case vc3 => exact l3
    case vc4 => exact l4
    case vc5 => exact l5
    case vc6 => exact l6
    case vc7 =>
      refine ⟨⟨hC, trivial, trivial, trivial, trivial, trivial, trivial, trivial, ?_⟩, Nat.le.refl⟩
      refine Mem.ac hE'.down ?_
      simp only [T, Saved]

omit [CodeEnv] in
theorem rl8 (old : BitVec 64) (new : BitVec 8) : BitVec.setWidth 8 (old.replaceLow new) = new := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]
  have := new.isLt
  omega

omit [CodeEnv] in
/-- `test; setne` twice and `and`: `bs_coupling && ch` (`kb`). -/
theorem kb_flags (a b : BitVec 32) (r r' : BitVec 64) (af af' : Bool) :
    BitVec.setWidth 8 (r.replaceLow (BitVec.ofNat 8 (CondCode.nz.interp
      (StatusFlags.from_result (a &&& a) { cf := false, af := af, of := false })).toNat))
    &&& BitVec.setWidth 8 (r'.replaceLow (BitVec.ofNat 8 (CondCode.nz.interp
      (StatusFlags.from_result (b &&& b) { cf := false, af := af', of := false })).toNat))
    = BitVec.ofNat 8 (if a ≠ 0#32 ∧ b ≠ 0#32 then 1 else 0) := by
  rw [rl8, rl8]
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self]
  by_cases ha : a = 0#32
  · subst ha; simp
  · by_cases hb : b = 0#32
    · subst hb; simp
    · have h1 : (a == 0#32) = false := beq_eq_false_iff_ne.mpr ha
      have h2 : (b == 0#32) = false := beq_eq_false_iff_ne.mpr hb
      simp [h1, h2, ha, hb]

theorem blk_L6111 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6111" := by
  cfg_block
  measure_hb "L6111"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hsp, hbp, hsi, hdx, hcx, hdi, h8, hm⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have hcpl := T_ld_cpl hm
    have hnl := T_ld_nn hm
    have pm : PLift _ := ⟨hm⟩
    have psp : PLift _ := ⟨hsp⟩
    have pbp : PLift _ := ⟨hbp⟩
    have psi : PLift _ := ⟨hsi⟩
    have pdx : PLift _ := ⟨hdx⟩
    have pcx : PLift _ := ⟨hcx⟩
    have pdi : PLift _ := ⟨hdi⟩
    have p8 : PLift _ := ⟨h8⟩
    clear hm
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try nnorm
    all_goals try simp only [psi.down, pcx.down] at *
    all_goals try (simp only [hcpl, hnl, Option.isSome_some]; done)
    all_goals try simp only [hcpl, hnl, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    case vc4 =>
      have h := ‹CondCode.z.interp _ = false›
      flg h
      refine ⟨⟨hC, by omega, psp.down, pbp.down, trivial, pdx.down, trivial, pdi.down, ?_, pm.down⟩,
        Nat.le.refl⟩
      rw [kb_flags, p8.down, BitVec.ofInt_toInt]
    case vc3 =>
      have h := ‹CondCode.z.interp _ = true›
      flg h
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, x.idx, hC.2.2.2.1, pm.down⟩, ?_, ?_, ?_⟩, Or.inl (by decide)⟩ <;>
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact psp.down | exact pbp.down | rfl | (rw [show x.nn = 0 by omega]; rfl) | (simp only [BitVec.xor_self]; rfl)

/-- The memory facts of `L613d`: the stores of `ac` and `t_huff` into the raw locals. -/
theorem mem613 {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
    {m : Mem 64} (hm : m =⋆ T k Ext x ra t₀ (Blank t₀) (Saved t₀) x.idx) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x48#64) 8).isSome = true
    ∧ (∀ v : BitVec 64, (storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 v.toInt).loadInt
        (VA + BitVec.ofNat 64 (8 * (8 + kb x t₀))) 8
          = some (Int.ofBytes (Int.toBytes 8 (TH x t₀).p.toInt)))
    ∧ (∀ v : BitVec 64, ((storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 v.toInt).loadInt
        (t₀.regs.get64 .rsp - 0x40#64) 8).isSome = true)
    ∧ (∀ w : BitVec 64, ((storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 (arg0 t₀).toInt).storeInt
        (t₀.regs.get64 .rsp - 0x40#64) 8 w.toInt) =⋆
        T k Ext x ra t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64)
          ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) w
          ⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64))))) (Saved t₀) x.idx) := by
  have hkb1 : kb x t₀ ≤ 1 := by simp only [kb]; split <;> omega
  have h1 := fun v : BitVec 64 => Block.storeInt_val (v := v.toInt) (a := t₀.regs.get64 .rsp - 0x48#64)
    (R := 8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64)
      ⋆ (NoiseF Ext x t₀ x.idx ⋆ Saved t₀ (Rest x.R ra t₀))))))))
    (Mem.ac hm (by simp only [T, Blank, c8]; ac_rfl)) (Split.here _ _)
  have h1T : ∀ v : BitVec 64, (storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 v.toInt) =⋆
      T k Ext x ra t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64)
        ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) v ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64)
        ⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64))))) (Saved t₀) x.idx :=
    fun v => Mem.ac (h1 v) (by simp only [T, c8]; ac_rfl)
  have hld : ∀ v : BitVec 64, (storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 v.toInt).loadInt
      (VA + BitVec.ofNat 64 (8 * (8 + kb x t₀))) 8
        = some (Int.ofBytes (Int.toBytes 8 (TH x t₀).p.toInt)) := by
    intro v
    obtain ⟨F, hF⟩ := T_vlcw (h1T v)
    exact vlc_load_ptr hF (8 + kb x t₀) (by omega)
  have hl40 : ∀ v : BitVec 64, ((storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 v.toInt).loadInt
      (t₀.regs.get64 .rsp - 0x40#64) 8).isSome = true := fun v =>
    Block.loadInt_isSome (Mem.ac (h1T v) (by simp only [T, c8]; ac_rfl)
      (H₂ := 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64)
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) v
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx
        ⋆ Saved t₀ (Rest x.R ra t₀)))))))))) (by simp)
  have h2 : ∀ v w : BitVec 64, ((storeInt m (t₀.regs.get64 .rsp - 0x48#64) 8 v.toInt).storeInt
      (t₀.regs.get64 .rsp - 0x40#64) 8 w.toInt) =⋆
      T k Ext x ra t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64)
        ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) v ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) w
        ⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64))))) (Saved t₀) x.idx := by
    intro v w
    have := Block.storeInt_val (v := w.toInt) (a := t₀.regs.get64 .rsp - 0x40#64)
      (Mem.ac (h1T v) (by simp only [T, c8]; ac_rfl)
        (H₂ := 8 ?@ (t₀.regs.get64 .rsp - 0x40#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64)
          ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) v
          ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
          ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx
          ⋆ Saved t₀ (Rest x.R ra t₀)))))))))) (Split.here _ _)
    exact Mem.ac this (by simp only [T, c8]; ac_rfl)
  have hl48 : (m.loadInt (t₀.regs.get64 .rsp - 0x48#64) 8).isSome = true :=
    Block.loadInt_isSome (Mem.ac hm (by simp only [T, Blank, c8]; ac_rfl)
      (H₂ := 8 ?@ (t₀.regs.get64 .rsp - 0x48#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64)
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x40#64)
        ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64)
        ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx
        ⋆ Saved t₀ (Rest x.R ra t₀)))))))))) (by simp)
  exact ⟨hl48, hld, hl40, h2 (arg0 t₀)⟩

theorem blk_L613d (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L613d" := by
  cfg_block
  measure_hb "L613d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hnn0, hsp, hbp, hsi, hdx, h9, hdi, hkb, hm⟩, hn⟩ := hs₀
    have hkb1 : kb x t₀ ≤ 1 := by simp only [kb]; split <;> omega
    obtain ⟨hl48, hld, hl40, h2⟩ := mem613 hm
    have e48 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551552#64 = t₀.regs.get64 .rsp - 0x48#64 := by
      bv_omega
    have e40 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64 = t₀.regs.get64 .rsp - 0x40#64 := by
      bv_omega
    have zk : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 (kb x t₀))) = BitVec.ofNat 64 (kb x t₀) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have ea : ∀ B : BitVec 64, B + BitVec.ofNat 64 (kb x t₀) * 8#64 + 64#64
        = B + BitVec.ofNat 64 (8 * (8 + kb x t₀)) := by intro B; bv_omega
    have P1 : PLift _ := ⟨h2⟩
    have P2 : PLift _ := ⟨hld⟩
    have P3 : PLift _ := ⟨hl40⟩
    have P4 : PLift _ := ⟨hl48⟩
    have pkb : PLift _ := ⟨hkb⟩
    have pe : PLift _ := ⟨And.intro e48 (And.intro e40 (And.intro zk ea))⟩
    clear hm hld hl40 hl48 h2 hkb e48 e40 zk ea
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try nnorm
    all_goals try simp only [hbp, hsp, hsi, hdx, h9, hdi]
    all_goals try simp only [pe.down.1, pe.down.2.1]
    all_goals try simp only [rl8, pkb.down, pe.down.2.2.1]
    all_goals try simp only [pe.down.2.2.2]
    all_goals try (simp only [P2.down, Option.isSome_some]; done)
    all_goals try simp only [P2.down, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    case vc1 => exact P4.down
    case vc3 => exact P3.down _
    case vc4 =>
      rename_i hx
      simp only [rl8, pkb.down, pe.down.2.2.1, pe.down.2.2.2, hbp, hdi, pe.down.1] at hx
      rw [P2.down, Option.some.injEq] at hx
      subst hx
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      exact ⟨⟨hC, hnn0, trivial, trivial, trivial, trivial, trivial, trivial, trivial, P1.down _⟩,
        Nat.le.refl⟩

/-- The memory facts of `L615b`: `f_huff`, the store of `&noise_facs_q`, the byte at `rbp-0x29`. -/
theorem mem615 {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
    {m : Mem 64} (hm : m =⋆ T k Ext x ra t₀ (Loc1 x t₀) (Saved t₀) x.idx) :
    m.loadInt (VA + BitVec.ofNat 64 (8 * (5 + 2 * kb x t₀))) 8
      = some (Int.ofBytes (Int.toBytes 8 (FH x t₀).p.toInt))
    ∧ (m.loadInt (t₀.regs.get64 .rsp - 0x50#64) 8).isSome = true
    ∧ (∀ v : BitVec 64, ((storeInt m (t₀.regs.get64 .rsp - 0x50#64) 8 v.toInt).loadInt (t₀.regs.get64 .rsp - 0x31#64) 1).isSome = true)
    ∧ (∀ (v : BitVec 64) (w : Int), ((storeInt m (t₀.regs.get64 .rsp - 0x50#64) 8 v.toInt).storeInt (t₀.regs.get64 .rsp - 0x31#64) 1 w) =⋆
        T k Ext x ra t₀ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) v
          ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p
          ⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64))))) (Saved t₀) x.idx) := by
  have hkb1 : kb x t₀ ≤ 1 := by simp only [kb]; split <;> omega
  have hld : m.loadInt (VA + BitVec.ofNat 64 (8 * (5 + 2 * kb x t₀))) 8
      = some (Int.ofBytes (Int.toBytes 8 (FH x t₀).p.toInt)) := by
    obtain ⟨F, hF⟩ := T_vlcw hm
    exact vlc_load_ptr hF (5 + 2 * kb x t₀) (by omega)
  have h0 : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx ⋆ Saved t₀ (Rest x.R ra t₀)))))))) :=
    Mem.ac hm (by simp only [T, Loc1]; ac_rfl)
  have h1 := fun v : BitVec 64 => Block.storeInt_val (v := v.toInt) h0 (Split.here _ _)
  have h1' : ∀ v : BitVec 64, storeInt m (t₀.regs.get64 .rsp - 0x50#64) 8 v.toInt =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) v ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx ⋆ Saved t₀ (Rest x.R ra t₀)))))))) :=
    fun v => Mem.ac (h1 v) (by simp only [c8]; ac_rfl)
  have e31 : (t₀.regs.get64 .rsp - 0x31#64 - (t₀.regs.get64 .rsp - 0x38#64)).toNat = 7 := by
    rw [show t₀.regs.get64 .rsp - 0x31#64 - (t₀.regs.get64 .rsp - 0x38#64) = 7#64 by bv_omega]; rfl
  refine ⟨hld, Block.loadInt_isSome h0 (by simp), fun v => Block.loadInt_isSome (h1' v) (by omega),
    fun v w => Mem.ac (Block.storeInt (h1' v) (by omega) w) (by simp only [T]; ac_rfl)⟩

theorem blk_L615b (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L615b" := by
  cfg_block
  measure_hb "L615b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hnn0, hsp, hbp, hsi, hdx, h9, hax, hcx, hm⟩, hn⟩ := hs₀
    obtain ⟨hld, h50, h31, hfin⟩ := mem615 hm
    have hkb1 : kb x t₀ ≤ 1 := by simp only [kb]; split <;> omega
    have z16 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (kb x t₀)) <<< 4)
        = BitVec.ofNat 64 (16 * kb x t₀) := by simp only [kb]; split <;> decide
    have ea : ∀ B : BitVec 64, BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (kb x t₀)) <<< 4)
        + B + 40#64 = B + BitVec.ofNat 64 (8 * (5 + 2 * kb x t₀)) := by
      intro B; rw [z16]; bv_omega
    have e50 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64 = t₀.regs.get64 .rsp - 0x50#64 := by
      bv_omega
    have e31 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551575#64 = t₀.regs.get64 .rsp - 0x31#64 := by
      bv_omega
    have pbp : PLift _ := ⟨hbp⟩
    have P1 : PLift _ := ⟨hld⟩
    have P2 : PLift _ := ⟨h50⟩
    have P3 : PLift _ := ⟨h31⟩
    have P4 : PLift _ := ⟨hfin⟩
    have pe : PLift _ := ⟨And.intro ea (And.intro e50 e31)⟩
    clear hm hld h50 h31 hfin ea e50 e31 z16
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try nnorm
    all_goals try simp only [hbp, h9, hax, hcx, Reg64s.get_low32]
    all_goals try simp only [pe.down.1, pe.down.2.1, pe.down.2.2]
    all_goals try (simp only [P1.down, Option.isSome_some]; done)
    all_goals try simp only [P1.down, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    case vc1 => simp
    case vc3 => exact P2.down
    case vc4 => exact P3.down _
    case vc5 =>
      simp only [hbp, Reg64s.get_low32, hcx, hax, pe.down.1, P1.down, Option.some.injEq] at *
      subst_vars
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      refine ⟨⟨hC, hnn0, ⟨?_, ?_, ?_, ?_, ?_⟩, trivial, P4.down _ _⟩, Nat.le.refl⟩ <;>
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals first | exact hsp | exact pbp.down | exact hsi | exact hdx | rfl

theorem mem6172 {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
    {m : Mem 64} (hm : m =⋆ T k Ext x ra t₀ (Loc2 x t₀) (Saved t₀) x.idx) :
    (m.loadInt (t₀.regs.get64 .rsp - 0x38#64) 4).isSome = true
    ∧ (∀ v : Int, ((storeInt m (t₀.regs.get64 .rsp - 0x38#64) 4 v).loadInt (t₀.regs.get64 .rsp - 0x58#64) 8).isSome = true)
    ∧ (∀ v : Int, ((storeInt m (t₀.regs.get64 .rsp - 0x38#64) 4 v).storeInt (t₀.regs.get64 .rsp - 0x58#64) 8 (arg3 t₀).toInt) =⋆
        T k Ext x ra t₀ (Loc x t₀) (Saved t₀) x.idx) := by
  have h0 : m =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (arg3 t₀ + 0x15a50#64)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx ⋆ Saved t₀ (Rest x.R ra t₀)))))))) :=
    Mem.ac hm (by simp only [T, Loc2]; ac_rfl)
  have h1 : ∀ v : Int, storeInt m (t₀.regs.get64 .rsp - 0x38#64) 4 v =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x58#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x38#64)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x50#64) (arg3 t₀ + 0x15a50#64)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀) ⋆ (c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x60#64) ⋆ (NoiseF Ext x t₀ x.idx ⋆ Saved t₀ (Rest x.R ra t₀)))))))) :=
    fun v => Mem.ac (Kraken.Examples.Sbr.Parse.slot_store h0 (by omega) v)
  refine ⟨Block.loadInt_isSome h0 (by simp), fun v => Block.loadInt_isSome (h1 v) (by simp),
    fun v => Mem.ac (Block.storeInt_val (h1 v) (Split.here _ _) (arg3 t₀).toInt)
      (by simp only [T, Loc, c8]; ac_rfl)⟩

theorem blk_L6172 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6172" := by
  cfg_block
  measure_hb "L6172"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hnn0, hR, h9, hm⟩, hn⟩ := hs₀
    obtain ⟨l38, l58, hfin⟩ := mem6172 hm
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64 = t₀.regs.get64 .rsp - 0x38#64 := by
      bv_omega
    have e58 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64 = t₀.regs.get64 .rsp - 0x58#64 := by
      bv_omega
    have pR : PLift _ := ⟨hR⟩
    have P1 : PLift _ := ⟨l38⟩
    have P2 : PLift _ := ⟨l58⟩
    have P3 : PLift _ := ⟨hfin⟩
    have pe : PLift _ := ⟨And.intro e38 e58⟩
    clear hm l38 l58 hfin e38 e58
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try nnorm
    all_goals try simp only [pR.down.2.1, h9]
    all_goals try simp only [pe.down.1, pe.down.2]
    case vc1 => exact P1.down
    case vc2 => exact P2.down _
    case vc3 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, x.idx, hC.2.2.2.1, P3.down _⟩, ⟨0, ?_, hnn0, ?_⟩, ?_⟩, ?_⟩ <;>
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.xor_self]
      case refine_1 => exact pR.down.1
      case refine_2 => exact pR.down.2.1
      case refine_3 => exact pR.down.2.2.1
      case refine_4 => exact pR.down.2.2.2.1
      case refine_5 => exact pR.down.2.2.2.2
      case refine_6 => rfl
      case refine_7 => simp only [arg3, Nat.mul_zero, BitVec.add_zero]
      all_goals simp

end Kraken.Examples.Sbr.Noise
