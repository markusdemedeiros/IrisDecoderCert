import Kraken.X64.Examples.Sbr.Parse.UsacBlk16
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the header's one-bit reads

`bs_amp_res` (into the cell `amp`), `bs_xover_band`'s neighbours and the flags of the header
(the raw `int` at `sbr + 0x28`, the branch bits). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The raw `int` at `sbr + 0x28` in the frame. -/
theorem um_split_r28 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (sA A.1.c + 0x28#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, SHW]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
    (Split.right (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    _) _) _⟩

/-- A store into the raw `int` at `sbr + 0x28` keeps the frame. -/
theorem um_storeR28 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : (a - (sA A.1.c + 0x28#64)).toNat + 4 ≤ 4) (v : Int) :
    m.storeInt a 4 v =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split_r28 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs ha v

/-- A load from the raw `int` at `sbr + 0x28` succeeds. -/
theorem um_loadR28 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : (a - (sA A.1.c + 0x28#64)).toNat + 4 ≤ 4) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split_r28 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h ha

omit [CodeEnv] in
/-- `sbr + 0x28` is `c + 0x28948`. -/
theorem r28_off (c : BitVec 64) (n : Nat) (hn : n = 166216) :
    ((c + BitVec.ofNat 64 n) - (sA c + 0x28#64)).toNat + 4 ≤ 4 := by
  subst hn; simp only [sA]; bv_omega

/-- The cell `bs_amp_res_header` (`sbr + 0x24`), at the values `st` and `st` with `amp := v`. -/
theorem um_split_amp (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (v : BitVec 32) :
    ∃ R, Split (cell4 (sA A.1.c + 0x24#64) st.amp) R (UM k A ra t₀ Lc Sg st)
      ∧ Split (cell4 (sA A.1.c + 0x24#64) v) R (UM k A ra t₀ Lc Sg { st with amp := v }) := by
  simp only [UM, UF, SHW]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.left (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right
      (Split.right (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _⟩

/-- Storing `bs_amp_res_header`. -/
theorem um_storeAmp {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x24#64) (v : BitVec 32) :
    m.storeInt a 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with amp := v } := by
  obtain ⟨R, hs, hs'⟩ := um_split_amp k A ra t₀ Lc Sg st v
  rw [hs', ha]
  exact Val.storeInt h hs (Int.toBytes_length 4 _) v.toInt

/-- Loading `bs_amp_res_header` succeeds. -/
theorem um_loadAmp {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : a = sA A.1.c + 0x24#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs, -⟩ := um_split_amp k A ra t₀ Lc Sg st 0#32
  rw [ha, Val.loadInt h hs (Int.toBytes_length 4 _) (by decide)]
  rfl


/-- A header flag into the raw `int` at `sbr + 0x28`; the branch bit. -/
theorem blk_L3475 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3475" := by
  cfg_block
  measure_hb "L3475"
    intro n
    simp only [tbl_L3475, var_L3475]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hdx⟩, h15⟩,
      rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeR28 (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadR28 (um_storeI hm v) a ha
    have hsI := fun v => um_storeI hm v
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hbl
    · exact hld _ _ (by rw [hbx]; exact r28_off _ _ rfl)
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L35bf], by decide⟩⟩
      rw [tbl_L35bf]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact ⟨hi_of_mi hP.1.1 hP.1.2.1, hP.2, hP.1.2.2, fun h => absurd hP.1.2.1 h⟩
      case hof => rw [hbx]; exact r28_off _ _ rfl
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down
    · refine ⟨?_, by
        simp only [var_L34b0, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L34b0]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      case hof => rw [hbx]; exact r28_off _ _ rfl
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down

/-- The header bit that selects the default header. -/
theorem blk_L34b0 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L34b0" := by
  cfg_block
  measure_hb "L34b0"
    intro n
    simp only [tbl_L34b0, var_L34b0]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hdx⟩, h15⟩,
      rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hsI := fun v => um_storeI hm v
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hbl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L35a5], by decide⟩⟩
      rw [tbl_L35a5]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hsI _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down
    · refine ⟨?_, by
        simp only [var_L34dd, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L34dd]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hsI _⟩, ?_⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down

/-- `bs_amp_res` into `bs_amp_res_header`. -/
theorem blk_L3410 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3410" := by
  cfg_block
  measure_hb "L3410"
    intro n
    simp only [tbl_L3410, var_L3410]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hP, hcx⟩, hm⟩, hdx, hsi, hdi⟩, h15⟩,
      rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeAmp (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadAmp (um_storeI hm v) a ha
    have hsI := fun v => um_storeI hm v
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    have hsiC := PLift.up hsi
    have hdiC := PLift.up hdi
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14, hcx, hsi, hdi,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hbl
    · exact hld _ _ (by rw [hbx]; bv_omega)
    · refine ⟨?_, by
        simp only [var_L343d, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L343d]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      case hof => rw [hbx]; bv_omega
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down

/-- The first header flag (no `indep_flag`). -/
theorem blk_L33ba (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L33ba" := by
  cfg_block
  measure_hb "L33ba"
    intro n
    simp only [tbl_L33ba, var_L33ba]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hP, hcx⟩, hm⟩, hdx, hsi⟩, h15⟩,
      rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hsI := fun v => um_storeI hm v
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    have hsiC := PLift.up hsi
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14, hcx, hsi,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hbl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L35bf], by decide⟩⟩
      rw [tbl_L35bf]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hsI _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact ⟨hi_of_mi hP.1.1 hP.1.2.1, hP.2, hP.1.2.2, fun h => absurd hP.1.2.1 h⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down
    · refine ⟨?_, by
        simp only [var_L33e6, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L33e6]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ⟨?sm, ?rr⟩, hsI _⟩, ?_, ?_, ?_⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      case rr => first | rfl | simp
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down

/-- The second header flag. -/
theorem blk_L33e6 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L33e6" := by
  cfg_block
  measure_hb "L33e6"
    intro n
    simp only [tbl_L33e6, var_L33e6]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hP, hax⟩, hm⟩, hdx, hsi, hdi⟩, h15⟩,
      rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hsI := fun v => um_storeI hm v
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    have hsiC := PLift.up hsi
    have hdiC := PLift.up hdi
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14, hax, hsi, hdi,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hbl
    · refine ⟨?_, by
        simp only [var_L3410, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3410]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ⟨?sm, ?rr⟩, hsI _⟩, ?_, ?_, ?_⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      case rr => first | rfl | simp
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15 | exact hsiC.down | exact hdiC.down

end Kraken.Examples.Sbr.Usac
