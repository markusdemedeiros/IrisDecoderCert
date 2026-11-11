import Kraken.X64.Examples.Sbr.Parse.UsacBlk18
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: `bs_xover_band`

`get_bits(gb, 4)` into byte 2 of `spectrum_params` (`um_storeSp2`); `Hid.xover` follows. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
theorem tb1 (v : BitVec 8) : Int.toBytes 1 v.toInt = [UInt8.ofBitVec v] := by
  revert v; decide

/-- `bs_xover_band` (byte 2 of `spectrum_params`), at `st` and with the new byte. -/
theorem um_split_sp (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) (b : UInt8) :
    ∃ R, Split (st.sp.take 4 =@ (sA A.1.c + 0x1c#64)) R (UM k A ra t₀ Lc Sg st)
      ∧ Split ((st.sp.set 2 b).take 4 =@ (sA A.1.c + 0x1c#64)) R
        (UM k A ra t₀ Lc Sg
          { st with sp := st.sp.set 2 b, h := { st.h with xover := b.toNat } }) := by
  have e : (st.sp.set 2 b).drop 4 = st.sp.drop 4 := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂; simp only [List.getElem_drop, List.getElem_set]
      exact ite_eq_right (by omega)
  simp only [UM, UF, SHW, e]
  exact ⟨_, Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _)
      _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.left (Split.left (Split.right (Split.right
      (Split.right (Split.right (Split.right (Split.right (Split.right (Split.here _ _) _) _) _)
      _) _) _) _) _) _) _) _⟩

/-- Storing `bs_xover_band`. -/
theorem um_storeSp2 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.sp.length = 6) (a : BitVec 64) (ha : a = sA A.1.c + 0x1e#64) (v : BitVec 8) :
    m.storeInt a 1 v.toInt =⋆ UM k A ra t₀ Lc Sg
      { st with sp := st.sp.set 2 (UInt8.ofBitVec v),
                h := { st.h with xover := (UInt8.ofBitVec v).toNat } } := by
  obtain ⟨R, hs, hs'⟩ := um_split_sp k A ra t₀ Lc Sg st (UInt8.ofBitVec v)
  rw [hs']; rw [hs] at h
  have h4 : (st.sp.take 4).length = 4 := by simp [hl]
  rw [List.take_set, ← bmerge (st.sp.take 4) _ 2 _ (by omega) (by omega)]
  rw [bsplit (st.sp.take 4) _ 2 (by omega) (by omega)] at h
  have ha2 : a = sA A.1.c + 0x1c#64 + BitVec.ofNat 64 2 := by rw [ha]; simp only [sA]; bv_omega
  rw [ha2]
  have := Val.storeInt (n := 1) h (Split.left (Split.right (Split.here _ _) _) _)
    (by simp) v.toInt
  rw [tb1] at this
  have e3 : (2 + 1 : Nat) = 3 := rfl
  simp only [e3] at this ⊢
  rw [show ∀ (X Y Z W : Mem 64 → Prop), (X ⋆ (Y ⋆ Z)) ⋆ W = Y ⋆ ((X ⋆ Z) ⋆ W) from
    fun X Y Z W => by ac_rfl]
  exact this

omit [CodeEnv] in
/-- `index + 4` clamped to `size_in_bits_plus8` (`cmovb`) stays below it. -/
theorem idx4_le (i p : BitVec 32) (af of : Bool) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (if CondCode.c.interp (StatusFlags.from_result (p - (BitVec.setWidth 32 4#64 + i))
        { cf := (p - (BitVec.setWidth 32 4#64 + i)).unsigned
            != p.unsigned - (BitVec.setWidth 32 4#64 + i).unsigned,
          af := af, of := of }) = true then p
      else BitVec.setWidth 32 4#64 + i).toNat ≤ p.toNat := by
  have e4 : (BitVec.setWidth 32 4#64 + i).toNat = i.toNat + 4 := by
    rw [BitVec.toNat_add]; simp; omega
  rw [apply_ite BitVec.toNat]
  split
  · exact Nat.le_refl _
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result] at h
    rw [e4]
    refine Nat.le_of_not_lt fun hc => h ?_
    have e : (p - (BitVec.setWidth 32 4#64 + i)).toNat = 2 ^ 32 + p.toNat - (i.toNat + 4) := by
      rw [BitVec.toNat_sub, e4]; omega
    simp only [BitVec.unsigned, e, e4, bne_iff_ne, ne_eq]
    omega

omit [CodeEnv] in
/-- `SpOk` with the new `bs_xover_band`. -/
theorem spok_set2 {st : USt} (h : SpOk st) (b : UInt8) :
    SpOk { st with sp := st.sp.set 2 b, h := { st.h with xover := b.toNat } } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [h1], ?_, ?_, h4⟩
  · show ((st.sp.set 2 b).getD 0 0).toNat = st.h.start
    rw [Parse.getD_set_ne _ _ _ _ (by decide)]; exact h2
  · show ((st.sp.set 2 b).getD 2 0).toNat = b.toNat
    rw [Parse.getD_set_eq _ _ _ (by omega)]

/-- Byte 2 of `spectrum_params` is there. -/
theorem um_loadSp2 {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st)
    (hl : st.sp.length = 6) (a : BitVec 64) (ha : a = sA A.1.c + 0x1e#64) :
    (m.loadInt a 1).isSome = true := by
  obtain ⟨R, hs, -⟩ := um_split_sp k A ra t₀ Lc Sg st 0
  rw [hs] at h
  have h4 : (st.sp.take 4).length = 4 := by simp [hl]
  rw [bsplit (st.sp.take 4) _ 2 (by omega) (by omega)] at h
  have ha2 : a = sA A.1.c + 0x1c#64 + BitVec.ofNat 64 2 := by rw [ha]; simp only [sA]; bv_omega
  rw [ha2, Val.loadInt (n := 1) h (Split.left (Split.right (Split.here _ _) _) _) (by simp)
    (by decide)]
  rfl

/-- `get_bits(gb, 4)`: `bs_xover_band`. -/
theorem blk_L343d (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L343d" := by
  cfg_block
  measure_hb "L343d"
    intro n
    simp only [tbl_L343d, var_L343d]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hdx⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 4)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := fun v a ha w => um_storeSp2 (um_storeI hm v) hI.2.1.1 a ha w
    have hld := fun v a ha => um_loadSp2 (um_storeI hm v) hI.2.1.1 a ha
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
    vcgen [Parse.bswap32_havoc, Parse.shl_cl32_havoc]
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
    · exact hld _ _ (by rw [hbx]; bv_omega)
    · refine ⟨?_, by
        simp only [var_L3475, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]; omega⟩
      rw [tbl_L3475]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _ _ ?hof _⟩, ?_⟩, ?_⟩
      case inv => exact ⟨hI.1, spok_set2 hI.2.1 _, idx4_le _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      case hof => rw [hbx]; bv_omega
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15

end Kraken.Examples.Sbr.Usac
