import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: `sbr_turnoff` (shard B)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- `kx[1] = 32`, `m[1] = 0`. -/
theorem blk_L1d5f (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d5f" ⟨"sbr_reset.L1d5f", B.L1d5f, some "sbr_reset.L1d71"⟩ := by
  info_off
  measure_hb "L1d5f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1d5f.mp hs
    clear hs
    have ld1 := c4_isSome (focus (Mm_kx1 ..) hm)
    have s1 := Mm_upd_kx1 .. ▸ c4_store (focus (Mm_kx1 ..) hm) (BitVec.setWidth 32 (32#64)).toInt 32 rfl
    have ld2 := c4_isSome (focus (Mm_m1 ..) s1)
    have s2' : _ =⋆ Mm k e (offA 1 a) ra t₀ (offSt 2 st) fr :=
      Mm_upd_m1 .. ▸ c4_store (focus (Mm_m1 ..) s1) (BitVec.setWidth 32 (0#64)).toInt 0 rfl
    have s2 : _ =⋆ Mm k e (offA 2 a) ra t₀ (offSt 2 st) fr := s2'
    clear s1 hm
    simp only [B.L1d5f]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals simp only [h12, AddrIndex.offset64_none, z, Int64.toBitVec_ofNat_norm]
    · with_reducible exact ld1
    · with_reducible exact ld2
    · rename_i s
      refine ⟨T.L1d71.mpr ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, s2⟩, ?_⟩
      var_step

set_option maxRecDepth 100000 in
/-- `data[1].e_a[1] = data[0].e_a[1] = -1` (raw cells). -/
theorem blk_L1d71 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d71" ⟨"sbr_reset.L1d71", B.L1d71, some "sbr_reset.L1d89"⟩ := by
  info_off
  measure_hb "L1d71"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1d71.mp hs
    clear hs
    have ld1 := slot_load (focus (Mm_ea1 ..) hm) (k := 4) (Nat.le_refl _)
    have s1 := (Mm_ea1 ..).symm ▸ slot_store (focus (Mm_ea1 ..) hm) (k := 4) (Nat.le_refl _)
      (BitVec.setWidth 32 (4294967295#64)).toInt
    have ld2 := slot_load (focus (Mm_ea0 ..) s1) (k := 4) (Nat.le_refl _)
    have s2 : _ =⋆ Mm k e (offA 2 a) ra t₀ (offSt 2 st) fr := (Mm_ea0 ..).symm ▸ slot_store
      (focus (Mm_ea0 ..) s1) (k := 4) (Nat.le_refl _) (BitVec.setWidth 32 (4294967295#64)).toInt
    clear s1 hm
    simp only [B.L1d71]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals simp only [h12, AddrIndex.offset64_none, z, Int64.toBitVec_ofNat_norm]
    · with_reducible exact ld1
    · with_reducible exact ld2
    · rename_i s
      refine ⟨T.L1d89.mpr ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, s2⟩, ?_⟩
      var_step

set_option maxRecDepth 100000 in
/-- `memset(spectrum_params, -1, 6)`: two stores. -/
theorem blk_L1d89 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d89" ⟨"sbr_reset.L1d89", B.L1d89, some "sbr_reset.L1d95"⟩ := by
  info_off
  measure_hb "L1d89"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, h12, hbx, st, fr, hM, hsp, hfm, hF, hm⟩ := T.L1d89.mp hs
    clear hs
    have hl : (offSt 2 st).sp.length = 6 := by rw [show (offSt 2 st).sp = a.sp from hsp]; exact hC.1
    have h1 := focus (Mm_sp ..) hm
    have e4 : arg1 t₀ + 0x1c#64 + 4#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 4 := rfl
    have e0 : arg1 t₀ + 0x1c#64 = arg1 t₀ + 0x1c#64 + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
    have ld1 : (s₀.dmem.loadInt (arg1 t₀ + 0x1c#64 + 4#64) 2).isSome = true := by
      rw [region_load (n := 2) h1 e4 (by omega) (by omega)]; rfl
    have s1 := region_store (n := 2) h1 e4 (by omega) (by omega) (BitVec.setWidth 16 (65535#64)).toInt
    have hl1 : (Parse.wr (offSt 2 st).sp 4 (Int.toBytes 2 (BitVec.setWidth 16 (65535#64)).toInt)).length = 6 := by
      rw [wr_length (by rw [Int.toBytes_length]; omega)]; exact hl
    have ld2 : ((s₀.dmem.storeInt (arg1 t₀ + 0x1c#64 + 4#64) 2 (BitVec.setWidth 16 (65535#64)).toInt).loadInt
        (arg1 t₀ + 0x1c#64) 4).isSome = true := by
      rw [region_load (n := 4) s1 e0 (by omega) (by omega)]; rfl
    have s2 := region_store (n := 4) s1 e0 (by omega) (by omega) (BitVec.setWidth 32 (4294967295#64)).toInt
    rw [sp_ff hl _ _ (by decide) (by decide), Mm_upd_sp] at s2
    have s3 : _ =⋆ Mm k e { a with us := 0 } ra t₀ (offSt 3 st) fr := s2
    clear s1 s2 h1 hm
    have hout := resetOut_turnoff hC.2.2.2.2.1 (resetC_lens hC) hM
    simp only [B.L1d89]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    vcgen
    all_goals try subst_vars
    all_goals simp only [hbx, AddrIndex.offset64_none, z, BitVec.add_zero, Int64.toBitVec_ofNat_norm]
    · with_reducible exact ld1
    · with_reducible exact ld2
    · rename_i s
      exact ⟨T.L1d95.mpr ⟨hC, ⟨hrsp, hrbp⟩, 0, offSt 3 st, fr, hout, hfm, hF, s3⟩, by var_step⟩

end Kraken.Examples.Sbr.Reset
