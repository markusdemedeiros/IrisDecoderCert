import Kraken.X64.Examples.Sbr.Parse.UsacBlk11
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the `bs_add_harmonic` loop bodies

Each body is the inlined `get_bits1` (as in `UsacBlk11.lean`) and one byte store into
channel 0's `bs_add_harmonic`, a raw 48-byte region of the footprint (`um_storeH`); the counter
stays below `n[1] ≤ 48` (`lp_lt`, `h_off`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- `bs_add_harmonic` of channel 0 (raw bytes) in the frame. -/
theorem um_split_h (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : ∃ R, Split (48 ?@ (dAc A.1.c 0 + 0x31#64)) R (UM k A ra t₀ Lc Sg st) := by
  simp only [UM, UF, DSc]
  exact ⟨_, (Split.right (Split.right (Split.left (Split.right (Split.right (Split.left
    (Split.right (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _
    _) _) _) _) _) _) _) _) _) _) _) _) _)⟩

/-- A byte store into `bs_add_harmonic` keeps the frame. -/
theorem um_storeH {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : (a - (dAc A.1.c 0 + 0x31#64)).toNat + 1 ≤ 48) (v : Int) :
    m.storeInt a 1 v =⋆ UM k A ra t₀ Lc Sg st := by
  obtain ⟨R, hs⟩ := um_split_h k A ra t₀ Lc Sg st
  exact Block.storeInt_split h hs ha v

/-- A byte load from `bs_add_harmonic` succeeds. -/
theorem um_loadH {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (a : BitVec 64)
    (ha : (a - (dAc A.1.c 0 + 0x31#64)).toNat + 1 ≤ 48) :
    (m.loadInt a 1).isSome = true := by
  obtain ⟨R, hs⟩ := um_split_h k A ra t₀ Lc Sg st
  rw [hs] at h
  exact Block.loadInt_isSome h ha

omit [CodeEnv] in
/-- The harmonic byte `i + j` of channel 0 is inside `bs_add_harmonic`. -/
theorem h_off (c i : BitVec 64) (n j : Nat) (hn : n = 166353 + j) (hi : i.toNat + j < 48) :
    ((c + i + BitVec.ofNat 64 n) - (dAc c 0 + 0x31#64)).toNat + 1 ≤ 48 := by
  subst hn; simp only [dAc, sA]; bv_omega

omit [CodeEnv] in
/-- The loop counter is below `48`. -/
theorem lp_lt {st : USt} {i b n : BitVec 64} (h : Lp st i b n) (h48 : st.x.n1 ≤ 48) :
    i.toNat + 1 < 48 + 1 ∧ i.toNat + 1 < b.toNat + 1 ∧ b.toNat ≤ 48 := by
  obtain ⟨-, rfl, -, h3⟩ := h
  have : (BitVec.ofNat 64 (st.x.n1 / 2 * 2)).toNat = st.x.n1 / 2 * 2 := by
    rw [BitVec.toNat_ofNat]; omega
  rw [this] at h3 ⊢; omega

/-- The first byte of a pair of the first harmonic loop. -/
theorem blk_L3ae0 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ae0" := by
  cfg_block
  measure_hb "L3ae0"
    intro n
    simp only [tbl_L3ae0, var_L3ae0]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨hfin, hlp⟩, hm⟩, hax⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeH (um_storeI hm v) a ha w
    have hld := fun v a ha => um_loadH (um_storeI hm v) a ha
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
    · exact hld _ _ (by
        rw [hbx]; exact h_off _ _ _ 0 rfl (by have := lp_lt hlp (n1_le hfin); omega))
    · refine ⟨?_, by simp only [var_L3b17, Reg64s.get64_set64, reduceCtorEq, ite_false]; omega⟩
      rw [tbl_L3b17]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm =>
        refine ⟨hfin, ?_⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
        exact hlp
      case hof => rw [hbx]; exact h_off _ _ _ 0 rfl (by have := lp_lt hlp (n1_le hfin); omega)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · exact hax

end Kraken.Examples.Sbr.Usac
