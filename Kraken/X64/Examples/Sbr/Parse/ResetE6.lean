import Kraken.X64.Examples.Sbr.Parse.ResetA2Flt

/-!
# `sbr_reset`, shard A2: the 16-wide `min` loop of `array_min` (`L2289`)

Four `vpmovsxwd` loads of 8 bytes of the frame's `int16` array and four `vpminsd`; the spec
tracks only the index, so the block proof shows the loads are in the frame and steps `rdi` by 16.
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
/-- `rbp + 2 c - D` as `rbp - (D - 2 c)`. -/
theorem rsH_idx (r : BitVec 64) (c D : Nat) (hc : 2 * c ≤ D) :
    r + BitVec.ofNat 64 c * 2#64 + BitVec.ofNat 64 (2 ^ 64 - D % 2 ^ 64)
      = r - BitVec.ofNat 64 (D - 2 * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem rsH_step16 (D i : Nat) (h16 : i % 16 = 0) (hD : D % 16 = 0) (hi : i < D)
    (hne : ¬ D = i + 16) : i + 16 < D := by omega

set_option maxRecDepth 100000 in
/-- The 16-wide `min` loop. -/
theorem blk_L2289 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2289" ⟨"sbr_reset.L2289", B.L2289, some "sbr_reset.L22d3"⟩ := by
  info_off
  measure_hb "L2289"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hvm, hvm', hTB, h30,
        h17, hdx, hsi, hcx, i, hdi, hi16, hiD⟩, hm⟩⟩ := T.L2289.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hiD' : i < (A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 := hiD
    have hD48 : (A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 ≤ 47 := by
      have := hN.2; omega
    have hi48 : i + 16 ≤ 47 := by omega
    have hD64 : (A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 < 2 ^ 64 := by omega
    have hl1 := fr_load hm hF (d := 236 - 2 * i) (n := 8) (by omega) (by omega)
    have hl2 := fr_load hm hF (d := 228 - 2 * i) (n := 8) (by omega) (by omega)
    have hl3 := fr_load hm hF (d := 220 - 2 * i) (n := 8) (by omega) (by omega)
    have hl4 := fr_load hm hF (d := 212 - 2 * i) (n := 8) (by omega) (by omega)
    have ea1 := rsH_idx (t₀.regs.get64 .rsp - 8#64) i 236 (by omega)
    have ea2 := rsH_idx (t₀.regs.get64 .rsp - 8#64) i 228 (by omega)
    have ea3 := rsH_idx (t₀.regs.get64 .rsp - 8#64) i 220 (by omega)
    have ea4 := rsH_idx (t₀.regs.get64 .rsp - 8#64) i 212 (by omega)
    have hinc : BitVec.setWidth 64 16#64 + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 16) := by
      rw [BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.ofNat_add i 16).symm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2289]
    vcgen
    case vc1 =>
      rename_i s1 hs1; subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdi, ea1, hl1, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1 _ _; subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdi, ea2, hl2, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 _ _ _ _; subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdi, ea3, hl3, Option.isSome_some]
    case vc4 =>
      rename_i s1 hs1 _ _ _ _ _ _; subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdi, ea4, hl4, Option.isSome_some]
    case vc5 =>
      rename_i s1 hs1 _ _ _ _ _ _ _ _ hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdi, hsi, hinc, CondCode.interp_nz,
        StatusFlags.zf_from_result_sub] at hc ⊢
      rw [a2_beq_ofNat _ _ hD64 (by omega)] at hc
      have hne : ¬ ((A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 = i + 16) := by
        intro h
        have hd : decide ((A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 = i + 16) = true :=
          decide_eq_true h
        simp only [hd, Bool.not_true, Bool.false_eq_true] at hc
      have hlt16 := rsH_step16 _ i hi16 (by omega) hiD' hne
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2289.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        fr, hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm,
        hvm', hTB, h30, h17, ?_, ?_, ?_, i + 16, ?_, by omega, hlt16⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals first
        | exact hrsp | exact hrbp | exact h15 | exact h12 | exact h13 | exact hax
        | exact hdx | exact hsi | exact hcx | skip
      left; rw [← hn]; simp only [lex_var]
      simp only [VD.L2289, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdi, hsi, hinc]
      apply Kraken.lex_cons_lt_cons (by lex_len)
      apply Kraken.lex_cons_lt_of_lt (by lex_len)
      simp only [BitVec.toNat_ofNat]
      omega
    case vc6 =>
      rename_i s1 hs1 _ _ _ _ _ _ _ _ hc
      subst hs1 hP
      refine ⟨T.L22d3.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm',
        hTB, h30, h17, ?_, ?_, ?_⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals first
        | exact hrsp | exact hrbp | exact h15 | exact h12 | exact h13 | exact hax
        | exact hdx | exact hsi | exact hcx | skip
      rw [← hn]; simp only [lex_var]
      exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

end Kraken.Examples.Sbr.Reset
