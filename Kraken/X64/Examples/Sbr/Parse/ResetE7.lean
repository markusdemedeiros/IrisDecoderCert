import Kraken.X64.Examples.Sbr.Parse.ResetE6

/-!
# `sbr_reset`, shard A2: the change step of the two-region `vk1` fix-up (`L25cf`)

`change = min(vdk0_max - vk1[1], (vk1[n1] - vk1[1]) / 2)` in 32-bit arithmetic.
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
theorem rsI_cc49 (N : Nat) (hN : N < 2 ^ 32) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 49#64)
      { cf := (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 49#64).unsigned
          != (BitVec.setWidth 32 (BitVec.ofNat 64 N)).unsigned
            - (BitVec.setWidth 32 49#64).unsigned,
        af := af, of := of })
      = decide (49 ≤ N) := by
  rw [a2_cc_nc_sub]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  omega


omit [CodeEnv] in
theorem rsI_sw (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 y) = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := y.isLt
  omega

omit [CodeEnv] in
theorem rsI_toInt (x : Int) (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) :
    (BitVec.ofInt 32 x).toInt = x := by
  rw [BitVec.toInt_ofInt]
  simp only [Int.bmod_def]
  split <;> omega

omit [CodeEnv] in
theorem rsI_sub (x y : Int) (hx1 : -2 ^ 31 ≤ x) (hx2 : x < 2 ^ 31) (hy1 : -2 ^ 31 ≤ y)
    (hy2 : y < 2 ^ 31) (h1 : -2 ^ 31 ≤ x - y) (h2 : x - y < 2 ^ 31) :
    BitVec.ofInt 32 x - BitVec.ofInt 32 y = BitVec.ofInt 32 (x - y) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sub, rsI_toInt x hx1 hx2, rsI_toInt y hy1 hy2, rsI_toInt _ h1 h2]
  simp only [Int.bmod_def]
  split <;> omega

omit [CodeEnv] in
theorem rsI_sar (x : Int) (h1 : -2 ^ 31 ≤ x) (h2 : x < 2 ^ 31) :
    (BitVec.ofInt 32 x).sshiftRight 1 = BitVec.ofInt 32 (x / 2) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, rsI_toInt x h1 h2, rsI_toInt _ (by omega) (by omega),
    Int.shiftRight_eq_div_pow]
  rfl

omit [CodeEnv] in
/-- The change: `min(vm - A1, (An - A1) / 2)` in 32-bit arithmetic. -/
theorem rsI_chg (x1 xn : BitVec 16) (V : BitVec 32) (A1 An vm : Int) (h1 : x1.toInt = A1)
    (hn : xn.toInt = An) (hv : V = BitVec.ofInt 32 vm) (ha1 : -64 ≤ A1) (ha1' : A1 ≤ 64)
    (han : -64 ≤ An) (han' : An ≤ 64) (hvm : -64 ≤ vm) (hvm' : vm ≤ 64) :
    (if decide ((V - x1.signExtend 32).toInt
        < ((xn.signExtend 32 - x1.signExtend 32).sshiftRight 1).toInt) = true
      then V - x1.signExtend 32 else (xn.signExtend 32 - x1.signExtend 32).sshiftRight 1)
      = BitVec.ofInt 32 (min (vm - A1) ((An - A1) / 2)) := by
  have e1 : x1.signExtend 32 = BitVec.ofInt 32 A1 := by rw [← h1]; rfl
  have en : xn.signExtend 32 = BitVec.ofInt 32 An := by rw [← hn]; rfl
  rw [e1, en, hv, rsI_sub _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    rsI_sub _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    rsI_sar _ (by omega) (by omega), rsI_toInt _ (by omega) (by omega),
    rsI_toInt _ (by omega) (by omega)]
  by_cases h : vm - A1 < (An - A1) / 2
  · rw [decide_eq_true h, ite_eq_left_iff.mpr (fun hc => absurd rfl hc)]
    congr 1; omega
  · rw [decide_eq_false h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    congr 1; omega

set_option maxRecDepth 100000 in
/-- The change step: `change` in `edx`, `vk1[1]` in `eax`, `vk1[n1]` in `ecx`. -/
theorem blk_L25cf (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L25cf" ⟨"sbr_reset.L25cf", B.L25cf, some "sbr_reset.L25fc"⟩ := by
  info_off
  measure_hb "L25cf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h15, h12, h13, vm, hvm1, hvm2, hTA, h30, hArr⟩,
      hm⟩⟩ := T.L25cf.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hN32 : A2.n1N e a (k0N a row) k2 < 2 ^ 32 := Nat.lt_of_le_of_lt hN.2 (by decide)
    have hlee := fr_load hm hF (d := 0xee) (n := 2) (by omega) (by omega)
    have hl50 := fr_load hm hF (d := 0x50) (n := 4) (by omega) (by omega)
    have hl30 := fr_load hm hF (d := 0x30) (n := 8) (by omega) (by omega)
    have hln := fr_load hm hF (d := 240 - 2 * A2.n1N e a (k0N a row) k2) (n := 2) (by omega)
      (by omega)
    have eee : t₀.regs.get64 .rsp - 8#64 + 18446744073709551378#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0xee := by bv_omega
    have e50 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by bv_omega
    have e30 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by bv_omega
    have en := rsH_idx (t₀.regs.get64 .rsp - 8#64) (A2.n1N e a (k0N a row) k2) 240 (by omega)
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr (1392 - 48) 8))
        = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2) := h30
    obtain ⟨A, hA, hsum⟩ := hArr
    have hsl : 1392 - (240 - 2 * A2.n1N e a (k0N a row) k2)
        = 1152 + 2 * A2.n1N e a (k0N a row) k2 := by omega
    have hA1 := hA 1 (by omega) (by omega)
    have hAn := hA (A2.n1N e a (k0N a row) k2) (by omega) (by omega)
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L25cf]
    vcgen
    case vc1 =>
      rename_i s1 hs1 hc
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, h13] at hc
      rw [rsI_cc49 _ hN32] at hc
      have := of_decide_eq_true hc
      omega
    case vc2 =>
      rename_i s1 hs1 hc
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, eee, hlee, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 hc _ _
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e50, hl50, Option.isSome_some]
    case vc4 =>
      rename_i s1 hs1 hc _ _ _ _
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, Option.isSome_some]
    case vc5 =>
      rename_i s1 hs1 hc _ _ _ _ v3 hv3
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, Option.some.injEq] at hv3
      subst hv3
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, h30', en, hln, Option.isSome_some]
    case vc6 =>
      rename_i s1 hs1 hc v1 hv1 v2 hv2 v3 hv3 v4 hv4 _ _ _
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, eee, hlee, e50, hl50,
        Option.some.injEq] at hv1 hv2 hv3
      subst hv1 hv2 hv3
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, h30', en, hln, Option.some.injEq] at hv4
      subst hv4
      refine ⟨T.L25fc.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx,
        hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, ?_, ?_, vm, hvm1, hvm2, hTA, h30,
        ?_, A, hA, hsum, ?_, ?_, ?_⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.reduceMod, Nat.reduceEqDiff, Nat.one_ne_zero, reduceCtorEq, ↓reduceIte,
        Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact h30'
      · rw [rsI_sw, ← hA1.1]; rfl
      · rw [rsI_sw, hsl, ← hAn.1]; rfl
      · simp only [rsI_sw]
        rw [hsl, CondCode.interp_l_sub32 _ _ _ rfl]
        exact rsI_chg _ _ _ _ _ _ hA1.1 hAn.1 hTA.2.2.2 hA1.2.1 hA1.2.2 hAn.2.1 hAn.2.2 hvm1 hvm2
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

end Kraken.Examples.Sbr.Reset
