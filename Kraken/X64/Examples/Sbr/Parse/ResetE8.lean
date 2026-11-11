import Kraken.X64.Examples.Sbr.Parse.ResetE7
import Kraken.X64.Examples.Sbr.Parse.ResetA2Pfx

/-!
# `sbr_reset`, shard A2: the change applied to `vk1[1]` and `vk1[n1]` (`L25fc`)

`vk1[1] += change`, `vk1[n1] -= change`: the sum is kept, the entries stay in `[-256, 256]`.
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
theorem rsJ_neg (r : BitVec 64) (D : Nat) (_hD : D < 2 ^ 64) :
    r + BitVec.ofNat 64 (2 ^ 64 - D % 2 ^ 64) = r - BitVec.ofNat 64 D := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem rsJ_lo (y : BitVec 32) (z : Int) (hy : y = BitVec.ofInt 32 z) (h1 : -2 ^ 15 ≤ z)
    (h2 : z < 2 ^ 15) : (BitVec.ofInt 16 (BitVec.setWidth 16 (BitVec.setWidth 64 y)).toInt).toInt
      = z := by
  subst hy
  rw [BitVec.ofInt_toInt, BitVec.toInt_eq_toNat_bmod]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  simp only [Int.bmod_def]
  split <;> omega

omit [CodeEnv] in
/-- `Σ` after adding `c` at `1` and subtracting it at `n`. -/
theorem rsJ_ssum (A : Nat → Int) (c : Int) (n : Nat) (hn : 2 ≤ n) :
    ∀ m, A2.ssum (fun i => if i = 1 then A 1 + c else if i = n then A n - c else A i) m
      = A2.ssum A m + (if 1 ≤ m then c else 0) - (if n ≤ m then c else 0) := by
  intro m
  induction m with
  | zero => simp [A2.ssum]; omega
  | succ m ih =>
    simp only [A2.ssum, ih]
    by_cases h1 : m + 1 = 1
    · simp only [h1, ↓reduceIte]
      split <;> split <;> split <;> omega
    · by_cases h2 : m + 1 = n
      · simp only [h2, ↓reduceIte]
        split <;> split <;> split <;> split <;> omega
      · simp only [h1, h2, ↓reduceIte]
        split <;> split <;> split <;> split <;> omega

omit [CodeEnv] in
theorem rsJ_add (x y : Int) (hx1 : -2 ^ 31 ≤ x) (hx2 : x < 2 ^ 31) (hy1 : -2 ^ 31 ≤ y)
    (hy2 : y < 2 ^ 31) (h1 : -2 ^ 31 ≤ x + y) (h2 : x + y < 2 ^ 31) :
    BitVec.ofInt 32 x + BitVec.ofInt 32 y = BitVec.ofInt 32 (x + y) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_add, rsI_toInt x hx1 hx2, rsI_toInt y hy1 hy2, rsI_toInt _ h1 h2]
  simp only [Int.bmod_def]
  split <;> omega

set_option maxRecDepth 100000 in
/-- The change applied: `vk1[1] += change`, `vk1[n1] -= change`. -/
theorem blk_L25fc (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L25fc" ⟨"sbr_reset.L25fc", B.L25fc, some "sbr_reset.L2619"⟩ := by
  info_off
  measure_hb "L25fc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h15, h12, h13, vm, hvm1, hvm2, hTA, h30, hsi, A, hA,
        hsum, hax, hcx, hdx⟩, hm⟩⟩ := T.L25fc.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hA1 := hA 1 (by omega) (by omega)
    have hAn := hA (A2.n1N e a (k0N a row) k2) (by omega) (by omega)
    have e1 := rsJ_neg (t₀.regs.get64 .rsp - 8#64) 238 (by omega)
    have en := rsH_idx (t₀.regs.get64 .rsp - 8#64) (A2.n1N e a (k0N a row) k2) 240 (by omega)
    have hl1 := fr_load hm hF (d := 0xee) (n := 2) (by omega) (by omega)
    have hM1 := fr_store hm hF (d := 0xee) (n := 2) (by omega) (by omega)
    have hl2 : ∀ v : Int, ((s₀.dmem.storeInt (t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 238) 2
        v).loadInt (t₀.regs.get64 .rsp - 8#64
          - BitVec.ofNat 64 (240 - 2 * A2.n1N e a (k0N a row) k2)) 2).isSome = true := by
      intro v
      rw [fr_load (hM1 v) (fr_wr_len hF (by decide) v) (d := 240 - 2 * A2.n1N e a (k0N a row) k2)
        (n := 2) (by omega) (by omega)]; rfl
    have hN64 : A2.n1N e a (k0N a row) k2 < 2 ^ 64 := by omega
    have r1 : rb 0xee = 1152 + 2 * 1 := rfl
    have r2 : rb (240 - 2 * A2.n1N e a (k0N a row) k2) = 1152 + 2 * A2.n1N e a (k0N a row) k2 := by
      simp only [rb]; omega
    have hFl : fr.length = 0x548 := hF
    -- the new array
    have hArr : ∀ v1 v2 : Int, (BitVec.ofInt 16 v1).toInt = A 1 + min (vm - A 1)
        ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) → (BitVec.ofInt 16 v2).toInt
          = A (A2.n1N e a (k0N a row) k2) - min (vm - A 1)
        ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) →
        A2.Arr (wr (wr fr (rb 0xee) (Int.toBytes 2 v1)) (rb (240 - 2 * A2.n1N e a (k0N a row) k2))
            (Int.toBytes 2 v2))
          0x480 (A2.n1N e a (k0N a row) k2) 256
          (((k2 : Nat) : Int) - (((A2.k1Of (k0N a row) k2) : Nat) : Int)) := by
      intro v1 v2 hv1 hv2
      have hl1' : (wr fr (rb 0xee) (Int.toBytes 2 v1)).length = 0x548 :=
        fr_wr_len hF (by decide) v1
      refine ⟨fun i => if i = 1 then
          A 1 + min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2)
        else if i = A2.n1N e a (k0N a row) k2 then A (A2.n1N e a (k0N a row) k2)
          - min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) else A i,
        fun i hi1 hin => ?_, ?_⟩
      · rw [r2, a2_fv_wr _ _ _ _ _ (by rw [hl1']; omega), r1, a2_fv_wr _ _ _ _ _ (by omega)]
        have hAi := hA i hi1 hin
        by_cases h1 : i = 1
        · subst h1
          simp only [show ¬ (1 = A2.n1N e a (k0N a row) k2) by omega, ↓reduceIte, hv1]
          refine ⟨trivial, ?_, ?_⟩ <;> omega
        · by_cases h2 : i = A2.n1N e a (k0N a row) k2
          · subst h2
            simp only [h1, ↓reduceIte, hv2]
            refine ⟨trivial, ?_, ?_⟩ <;> omega
          · simp only [h1, h2, ↓reduceIte]
            exact ⟨hAi.1, by omega, by omega⟩
      · rw [rsJ_ssum A _ _ hN.1, hsum]
        simp only [show 1 ≤ A2.n1N e a (k0N a row) k2 by omega, Nat.le_refl, ↓reduceIte]
        omega
    simp only [B.L25fc]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hsi, e1, en, hl1, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hsi, e1, en]
      exact hl2 _
    case vc3 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hsi, e1, en]
      have hN0' : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have hNb : A2.n1N e a (k0N a row) k2 ≤ 48 := hN.2
      have hNa : 2 ≤ A2.n1N e a (k0N a row) k2 := hN.1
      have hAn' : -64 ≤ A (A2.n1N e a (k0N a row) k2) ∧ A (A2.n1N e a (k0N a row) k2) ≤ 64 :=
        hAn.2
      have r2' : rb (240 - 2 * A2.n1N e a (k0N a row) k2) = 1152 + 2 * A2.n1N e a (k0N a row) k2 :=
        r2
      have hm1 : -128 ≤ min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) ∧
          min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) ≤ 128 := by omega
      have hs1 : BitVec.setWidth 32 (s1.regs.get64 .rdx) + BitVec.setWidth 32 (s1.regs.get64 .rax)
          = BitVec.ofInt 32 (min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) + A 1) := by
        rw [hdx, hax]
        exact rsJ_add _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hs2 : BitVec.setWidth 32 (s1.regs.get64 .rcx) - BitVec.setWidth 32 (s1.regs.get64 .rdx)
          = BitVec.ofInt 32 (A (A2.n1N e a (k0N a row) k2)
            - min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2)) := by
        rw [hcx, hdx]
        exact rsI_sub _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hv1 := rsJ_lo _ (min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) + A 1) hs1
        (by omega) (by omega)
      have hv2 := rsJ_lo _ (A (A2.n1N e a (k0N a row) k2)
        - min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2)) hs2 (by omega) (by omega)
      rw [show min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) + A 1
        = A 1 + min (vm - A 1) ((A (A2.n1N e a (k0N a row) k2) - A 1) / 2) by omega] at hv1
      generalize (BitVec.setWidth 16 (BitVec.setWidth 64
          (BitVec.setWidth 32 (s1.regs.get64 .rdx)
            + BitVec.setWidth 32 (s1.regs.get64 .rax)))).toInt = V1 at hv1 ⊢
      generalize (BitVec.setWidth 16 (BitVec.setWidth 64
          (BitVec.setWidth 32 (s1.regs.get64 .rcx)
            - BitVec.setWidth 32 (s1.regs.get64 .rdx)))).toInt = V2 at hv2 ⊢
      have hF1 := fr_wr_len hF (o := rb 0xee) (n := 2) (by decide) V1
      have hl1' : (wr fr (rb 0xee) (Int.toBytes 2 V1)).length = 0x548 := hF1
      have hM2 := fr_store (hM1 V1) hF1 (d := 240 - 2 * A2.n1N e a (k0N a row) k2) (n := 2)
        (by omega) (by omega) V2
      have hF2 := fr_wr_len hF1 (o := rb (240 - 2 * A2.n1N e a (k0N a row) k2)) (n := 2)
        (by rw [r2']; omega) V2
      have hI1 := a2_inc_wr2 (p := rb 0xee) V1 (by rw [hFl, r1]; omega) (by rw [r1]; omega) hInc0
      have hI := a2_inc_wr2 (p := rb (240 - 2 * A2.n1N e a (k0N a row) k2)) V2
        (by rw [hl1', r2']; omega) (by rw [r2']; omega) hI1
      have hT1 := a2_ta_wr (rb 0xee) V1 (by rw [hFl, r1]; omega) (by rw [r1]; simp only [rb]; omega)
        hTA
      have hT := a2_ta_wr (rb (240 - 2 * A2.n1N e a (k0N a row) k2)) V2 (by rw [hl1', r2']; omega)
        (by rw [r2']; simp only [rb]; omega) hT1
      refine ⟨T.L2619.mpr ?_, ?_⟩
      · refine ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF2,
          ?_, hM2⟩⟩
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp]
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp]
        refine ⟨hk2v, hk1v, hlt, ?_, ?_, ?_, ?_, ?_, ?_, vm, ?_, ?_, ?_, ?_⟩
        · exact hI
        · exact hN0
        · exact hN1
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]; exact h15
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]; exact h12
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]; exact h13
        · exact hT
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrbp]
        · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
        · exact hArr V1 V2 hv1 hv2
      · rw [← hn]; simp only [lex_var]; exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

end Kraken.Examples.Sbr.Reset
