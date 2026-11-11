import Kraken.X64.Examples.Sbr.Parse.UsacBlk15
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the bit after the harmonic loops

One bit into the raw `int` at `data[1] + 4` (`um_storeT1`); `0` returns (`L3ef1`), `1` goes on
with `eax = 0`. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The raw `int` at `data[1] + 4` in the frame. -/
theorem um_split_t1 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (4 ?@ (dAc A.1.c 1 + 0x4#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, (Split.right (Split.right (Split.left (Split.right (Split.right (Split.right
    (Split.right (Split.left (Split.right (Split.here _ _) _) _) _) _) _) _) _) _) _)⟩

/-- A store into the raw `int` at `data[1] + 4` keeps the frame. -/
theorem um_storeT1 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : (a - (dAc A.1.c 1 + 0x4#64)).toNat + 4 ≤ 4) (v : Int) :
    m.storeInt a 4 v =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split_t1 k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs ha v

/-- A load from the raw `int` at `data[1] + 4` succeeds. -/
theorem um_loadT1 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : (a - (dAc A.1.c 1 + 0x4#64)).toNat + 4 ≤ 4) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs⟩ := um_split_t1 k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h ha

omit [CodeEnv] in
/-- `data[1] + 4` is `sbr + 0x3e464`. -/
theorem t_off (c : BitVec 64) (n : Nat) (hn : n = 255076) :
    ((c + BitVec.ofNat 64 n) - (dAc c 1 + 0x4#64)).toNat + 4 ≤ 4 := by
  subst hn; simp only [dAc, sA]; bv_omega

/-- The bit after the second harmonic loop. -/
theorem blk_L3c4b (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3c4b" := by
  cfg_block
  measure_hb "L3c4b"
    intro n
    simp only [tbl_L3c4b, var_L3c4b]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, -⟩, hm⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeT1 (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadT1 (um_storeI hm v) a ha
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
    · exact hld _ _ (by rw [hbx]; exact t_off _ _ rfl)
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3ef1, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3ef1]
      refine ⟨hF, ?_, _, ?out, hst _ _ ?hof _⟩
      case out =>
        unfold UsacOut
        exact ⟨hfin.1, fun _ => hfin.2, hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case hof => rw [hbx]; exact t_off _ _ rfl
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact hsp
    · refine ⟨?_, by
        simp only [var_L3c84, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3c84]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact ⟨hfin, trivial⟩
      case hof => rw [hbx]; exact t_off _ _ rfl
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · first | rfl | simp only [BitVec.xor_self, sw6432] | simp

/-- The bit after the third harmonic loop. -/
theorem blk_L3e17 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3e17" := by
  cfg_block
  measure_hb "L3e17"
    intro n
    simp only [tbl_L3e17, var_L3e17]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, -⟩, hm⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeT1 (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadT1 (um_storeI hm v) a ha
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
    · exact hld _ _ (by rw [hbx]; exact t_off _ _ rfl)
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl (by
        simp only [var_L3ef1, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega)⟩
      rw [tbl_L3ef1]
      refine ⟨hF, ?_, _, ?out, hst _ _ ?hof _⟩
      case out =>
        unfold UsacOut
        exact ⟨hfin.1, fun _ => hfin.2, hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case hof => rw [hbx]; exact t_off _ _ rfl
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      exact hsp
    · refine ⟨?_, by
        simp only [var_L3e50, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3e50]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact ⟨hfin, trivial⟩
      case hof => rw [hbx]; exact t_off _ _ rfl
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · first | rfl | simp only [BitVec.xor_self, sw6432] | simp

end Kraken.Examples.Sbr.Usac
