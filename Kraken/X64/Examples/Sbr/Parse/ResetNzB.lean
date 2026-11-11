import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetNz
import Kraken.X64.Examples.Sbr.Parse.ResetNq

/-!
# `sbr_reset`: `derived3`, entry `0` of `f_tablenoise` and the dispatch on `n_q`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
theorem rsN_v16 (n : Nat) (h : n < 32768) :
    ((BitVec.setWidth 16 (BitVec.ofNat 64 n)).toInt % 65536).toNat = n := by
  have : (BitVec.setWidth 16 (BitVec.ofNat 64 n)).toInt = n := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  rw [this]; omega

omit [CodeEnv] in
/-- Entry `0` stored: no entries computed yet. -/
theorem rsN_NzM_zero (x : Args) (q : Nat) (hl : x.ftNoise.length = 12) (v : Int)
    (hv : (v % 65536).toNat = u16 x.ftLow 0) :
    wr x.ftNoise (2 * 0) (Int.toBytes 2 v) = NzM x q 0 := by
  apply eq_of_u16 (k := 6) (by rw [wr_length (by rw [Int.toBytes_length, hl]; omega), hl])
    (by simp [NzM])
  intro i hi
  rw [rsE_u16_wr2 v (by rw [hl]; omega), NzM, u16_mk16 hi]
  by_cases h0 : i = 0
  · subst h0; simp only [↓reduceIte, hv]; exact (Nat.mod_eq_of_lt (rsE_u16_lt _ _)).symm
  · simp only [h0, ↓reduceIte, show ¬ i ≤ 0 by omega]
    exact (Nat.mod_eq_of_lt (rsE_u16_lt _ _)).symm

omit [CodeEnv] in
theorem rsN_low0 (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) (h : f (xoOf a) < 65536) :
    u16 (dD2 a k0 nm f).ftLow 0 = f (xoOf a) := by
  simp only [dD2, derived2]
  rw [u16_mk16 (by omega)]
  simp only [↓reduceIte]; exact Nat.mod_eq_of_lt h

set_option maxRecDepth 100000 in
/-- `f_tablenoise[0] = f_tablelow[0]` (`kx[1]`); `n_q = 1` goes to the last entry, otherwise the loop. -/
theorem blk_L2bb5 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2bb5" ⟨"sbr_reset.L2bb5", B.L2bb5, some "sbr_reset.L2bde"⟩ := by
  info_off
  measure_hb "L2bb5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, h80, h50, q, hq1, hq6, hx, hcx, h14, h15⟩, hm⟩, h12⟩ := T.L2bb5.mp hs
    clear hs
    have hfnl : st.x.ftNoise.length = 12 := by rw [hx]; exact hC.2.2.2.2.2.2.2.2.1
    have hfn : st.x.ftNoise = (dD2 a k0 nm (fOf st)).ftNoise := by rw [hx]
    have hstore : ∀ (v : Int), (v % 65536).toNat = fOf st (xoOf a) →
        s₀.dmem.storeInt (arg1 t₀ + 0x4c2e6#64) 2 v
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q 0 } } : St) fr := by
      intro v hv
      have h := region_store (o := 2 * 0) (n := 2) (addr := arg1 t₀ + 0x4c2e6#64) (focus (Mm_ftNoise ..) hm)
        (by simp) (by rw [hfnl]; omega) (by rw [hfnl]; omega) v
      rw [hfn, rsN_NzM_zero _ q (by rw [← hfn]; exact hfnl) v
        (by rw [rsN_low0 _ _ _ _ (by omega)]; exact hv), Mm_upd_ftNoise] at h
      exact h
    have hx' : ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q 0 } } : St).x
        = dNz a k0 nm (fOf st) q 0 := by
      show ({ st.x with ftNoise := _ } : Args) = _
      rw [hx]
    have hld : ∀ v : Int, (v % 65536).toNat = fOf st (xoOf a) →
        (s₀.dmem.storeInt (arg1 t₀ + 0x4c2e6#64) 2 v).loadInt
          (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38) 8 = some (Int.ofBytes (slice fr (rb 0x38) 8)) :=
      fun v hv => fr_load (hstore v hv) hF (by omega) (by omega)
    have a38 : t₀.regs.get64 .rsp - 8#64 + (-56 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by
      have : (-56 : Int64).toBitVec = 0xffffffffffffffc8#64 := by decide
      rw [this]; bv_omega
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hv : ((BitVec.setWidth 16 (s₀.regs.get64 .r14)).toInt % 65536).toNat = fOf st (xoOf a) := by
      rw [h14]; exact rsN_v16 _ (by omega)
    simp only [B.L2bb5]
    vcgen
    all_goals try subst_vars
    all_goals simp only [hrbp, h12, z, a38, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    case vc1 =>
      rw [region_load (o := 0) (n := 2) (focus (Mm_ftNoise ..) hm) (by simp) (by rw [hfnl]; omega)
        (by rw [hfnl]; omega)]; rfl
    case vc2 => rw [hld _ hv]; rfl
    case vc3 =>
      rename_i hc
      exfalso
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, CondCode.interp_z,
        StatusFlags.zf_from_result, BitVec.and_self] at hc
      rw [hcx, beq_iff_eq] at hc
      have := congrArg BitVec.toNat hc
      simp only [BitVec.toNat_ofNat] at this
      simp at this; omega
    case vc4 =>
      rename_i v hl hz _ hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrbp, h12, z, a38,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, cc_z_sub, cc_nz_sub] at hc hl
      rw [hcx] at hc
      rw [hld _ hv, Option.some.injEq] at hl
      subst hl
      have hq2 : 2 ≤ q := by
        rcases (by omega : q = 1 ∨ 2 ≤ q) with h | h
        · subst h; revert hc; decide
        · exact h
      refine Or.inl (Table.ofLabels_at ⟨S.L2bde, T.L2bde.mpr ⟨hC, ⟨?_, ?_⟩,
        ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q 0 } } : St), fr, nm, k0,
        hMa, hsp, hfm, hF, h40, ⟨hk2, hf1, hf2, h30, h38, q, 0, hq1, hq6, hx', ?_, ?_, h50, h80, ?_, rfl,
        hq2, ?_⟩, hstore _ hv⟩, by edge_step⟩)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h38
      · exact h12
      · exact hcx
      · exact h15
    case vc5 =>
      rename_i v hl hz _ hc _
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrbp, h12, z, a38,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, cc_z_sub, cc_nz_sub] at hc hl
      rw [hcx] at hc
      rw [hld _ hv, Option.some.injEq] at hl
      subst hl
      obtain rfl : q = 1 := by
        rcases (by omega : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5) with h | h | h | h | h
        · exact h
        all_goals (subst h; revert hc; decide)
      refine Or.inl (Table.ofLabels_at ⟨S.L2c5b, T.L2c5b.mpr ⟨hC, ⟨?_, ?_⟩,
        ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) 1 0 } } : St), fr, nm, k0,
        hMa, hsp, hfm, hF, h40, ⟨hk2, hf1, hf2, h30, h38, 1, 0, hq1, hq6, hx', ?_, ?_, h50, h80, ?_, rfl,
        ?_, ?_, ?_⟩, hstore _ hv⟩, by edge_step⟩)
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact hrsp
      · exact hrbp
      · exact h38
      · exact h12
      · exact hcx
      · exact h15
      · rfl
      · exact rsE_xor_self _

end Kraken.Examples.Sbr.Reset
