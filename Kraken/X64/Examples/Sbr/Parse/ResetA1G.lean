import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1F5
import Kraken.X64.Examples.Sbr.Parse.ResetA1Avx2

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the `f_master` fill set-up blocks `L1e09`, `L1e6b` (shard A1)

`vmovd` + `vpshufb .LCPI5_4` broadcast `dk` into the eight `int16` lanes of `xmm0` (`bc16`), the
loop bounds `nm & ~31` / `nm & ~7` and the tail start `rdi` are set up.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option linter.unusedSimpArgs false in
omit [CodeEnv] in
theorem a1_bc16 (d : Nat) (hd : d = 1 ∨ d = 2) :
    BitVec.packedBinOp 128 BitVec.pshufb128 (BitVec.setWidth 128 (BitVec.setWidth 32 (BitVec.ofNat 64 d)))
      (BitVec.ofInt 128 (0x01000100010001000100010001000100 : Int)) = bc16 d := by
  rcases hd with rfl | rfl
  · simp (disch := decide) only [ln_pk_step, ln_pk_base, BitVec.pshufb128]
    decide
  · simp (disch := decide) only [ln_pk_step, ln_pk_base, BitVec.pshufb128]
    decide

omit [CodeEnv] in
theorem a1_mask32 : ∀ n, n < 49 → (BitVec.ofNat 32 n &&& 4294967264#32) = BitVec.ofNat 32 (n / 32 * 32) := by
  decide

omit [CodeEnv] in
theorem a1_mask32' (n : Nat) (h : n < 49) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)))
      &&& BitVec.setWidth 32 4294967264#64) = BitVec.ofNat 64 (n / 32 * 32) := by
  have e1 : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)))
      = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have e2 : BitVec.setWidth 32 4294967264#64 = 4294967264#32 := by decide
  rw [e1, e2, a1_mask32 n h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

section Mem16

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

theorem a1_lcpi4_load (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (lab "LCPI5_4") 16
      = some (Int.ofBytes (Int.toBytes 16 (0x01000100010001000100010001000100 : Int))) := by
  have h := focus (Mm_cst ..) hm
  simp only [CstR] at h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h
  obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_lr h; obtain ⟨F, h⟩ := a1_pick_ll h
  exact loadInt_sep _ _ 16 _ m h (Int.toBytes_length 16 _) (by omega)

end Mem16

theorem blk_L1e09 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1e09" ⟨"sbr_reset.L1e09", B.L1e09, some "sbr_reset.L1e30"⟩ := by
  info_off
  measure_hb "L1e09"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, h32⟩, hm⟩, h12, h15⟩ := T.L1e09.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hl4 := a1_lcpi4_load hm
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    simp only [B.L1e09]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      hsi, h13]
    · rw [hl4]; rfl
    · rename_i v hv _
      try dsimp only at hv
      rw [hl4] at hv; obtain rfl := Option.some.inj hv
      have hr8 := a1_mask32' N (by omega)
      have hdi : BitVec.ofNat 64 (N / 32 * 32) + 1#64 = BitVec.ofNat 64 (N / 32 * 32 + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [← hr8] at hdi
      have hj0 : 0 < N / 32 * 32 := by omega
      have hdk : u8 a.sp 4 + 1 = 1 ∨ u8 a.sp 4 + 1 = 2 := by (try simp only [u8] at hA4 ⊢); omega
      subst hNdef
      refine ⟨T.L1e30.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, h32, ?_, ?_, ?_, 0, ?_, rfl, hj0,
          fun i _ hi => absurd hi (by omega)⟩, hm⟩, ?_, ?_⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx,
        hcx, h13, hax, hsi, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.xor_self,
        RegZmms.get_set_xmm_same, BitVec.setWidth_eq, Xbc]
      all_goals first
        | done
        | exact hr8
        | exact hdi
        | rfl
        | (rw [BitVec.ofInt_ofBytes_toBytes_eq 128 16 rfl]; exact a1_bc16 _ hdk)

theorem blk_L1e6b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1e6b" ⟨"sbr_reset.L1e6b", B.L1e6b, some "sbr_reset.L1e90"⟩ := by
  info_off
  measure_hb "L1e6b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, j, hr8j, hj8, hjn, hfil⟩, hm⟩, h12, h15⟩ :=
      T.L1e6b.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hl4 := a1_lcpi4_load hm
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    simp only [B.L1e6b]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      hsi, h13]
    · rw [hl4]; rfl
    · rename_i v hv
      try dsimp only at hv
      rw [hl4] at hv; obtain rfl := Option.some.inj hv
      have hr9 := a1_mask8' N (by omega)
      have hdi : BitVec.ofNat 64 (N / 8 * 8) + 1#64 = BitVec.ofNat 64 (N / 8 * 8 + 1) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      rw [← hr9] at hdi
      have hjl : j < N / 8 * 8 := by omega
      have hdk : u8 a.sp 4 + 1 = 1 ∨ u8 a.sp 4 + 1 = 2 := by (try simp only [u8] at hA4 ⊢); omega
      subst hNdef
      refine ⟨T.L1e90.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, j, ?_, hj8, hjl, hfil⟩, hm⟩, ?_, ?_⟩,
        by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx,
        hcx, h13, hax, hsi, hr8j, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        RegZmms.get_set_xmm_same, BitVec.setWidth_eq, Xbc]
      all_goals first
        | done
        | exact hr9
        | exact hdi
        | rfl
        | (rw [BitVec.ofInt_ofBytes_toBytes_eq 128 16 rfl]; exact a1_bc16 _ hdk)

end Kraken.Examples.Sbr.Reset
