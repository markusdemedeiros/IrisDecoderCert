import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetELib
import Kraken.X64.Examples.Sbr.Parse.ResetE1

/-!
# `sbr_reset`: `sbr_make_f_derived`, the `f_tablelow` copy (`derived2`): the vector loops' setup
(shard B, env)
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
theorem rsE_and15 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))) &&& 15#32
      = BitVec.ofNat 32 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show (15 : Nat) = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

omit [CodeEnv] in
theorem rsE_R16 (n : Nat) (hn : n < 2 ^ 32) (fl : StatusFlags.from_result.Remaining) :
    (if CondCode.nz.interp (StatusFlags.from_result
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))) &&& 15#32) fl) = true
      then BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))) &&& 15#32)
      else 16#64) = BitVec.ofNat 64 (R16 n) := by
  rw [rsE_and15 n hn, CondCode.interp_nz, StatusFlags.zf_from_result]
  by_cases h : n % 16 = 0
  · simp only [h, R16, ↓reduceIte]; rfl
  · have h' : (BitVec.ofNat 32 (n % 16) == BitVec.zero 32) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp only [h', Bool.not_false, ↓reduceIte, R16, h]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_subR (n r : Nat) (h : r ≤ n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 64 n - BitVec.ofNat 64 r = BitVec.ofNat 64 (n - r) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_add1 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.ofNat 64 n + 1#64 = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_rsi16 (x : BitVec 64) (p : Nat) (hp : p < 2) :
    311992#64 + (x - BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 p * 2#64 + 0#64)))
      = x + BitVec.ofNat 64 (0x4c2b8 - 2 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- The 16-wide loop's setup: `r9 = n0 - R16 n0`, `rdx = R16 n0`. -/
theorem blk_L29f4 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L29f4" ⟨"sbr_reset.L29f4", B.L29f4, some "sbr_reset.L2a26"⟩ := by
  info_off
  measure_hb "L29f4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, rfl, h17, h13⟩, hm⟩ := T.L29f4.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have ha3 : s₀.regs.get64 .rbp + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x30) := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      simp only [rb, this, hrbp]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x30) (by omega) (by omega) ha3
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1344 8)) = arg1 t₀ := h30
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have P1 := PLift.up ld1
    have Px := PLift.up hx
    have Pm := PLift.up hm
    clear h30 hx hm ld1
    have hxo' : xoOf a < nm := hxo
    have hn16 : (nm - xoOf a + 1) / 2 < 2 ^ 32 := by omega
    have hR : R16 ((nm - xoOf a + 1) / 2) ≤ (nm - xoOf a + 1) / 2 := by
      simp only [R16]; split <;> omega
    have hp : (nm - xoOf a) % 2 < 2 := Nat.mod_lt _ (by omega)
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hW4 : BitVec.ofNat 64 Width.W32.bytes = 4#64 := rfl
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L29f4]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, hW4, hW2,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, z] at *
    case vc1 => rw [P1.down]; rfl
    case vc2 =>
      rename_i _ v hl
      have hl := hl.symm.trans P1.down
      simp only [Option.some.injEq] at hl
      subst hl
      simp only [h15, h13, rsE_R16 _ hn16, rsE_subR _ _ hR hn16, h30', rsE_rsi16 _ _ hp]
      refine ⟨T.L2a26.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp,
        hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, 0, Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx,
        rfl, h17, by rsE_rs; exact h13, by rsE_rs, by rsE_rs, by rsE_rs, by rsE_rs,
        by rsE_rs; exact rsE_add1 _ (by omega)⟩, Pm.down⟩, by var_step⟩

omit [CodeEnv] in
theorem rsE_and3 (n : Nat) (hn : n < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))) &&& 3#32
      = BitVec.ofNat 32 (n % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

omit [CodeEnv] in
theorem rsE_R4 (n : Nat) (hn : n < 2 ^ 32) (fl : StatusFlags.from_result.Remaining) :
    (if CondCode.nz.interp (StatusFlags.from_result
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))) &&& 3#32) fl) = true
      then BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n))) &&& 3#32)
      else 4#64) = BitVec.ofNat 64 (R4 n) := by
  rw [rsE_and3 n hn, CondCode.interp_nz, StatusFlags.zf_from_result]
  by_cases h : n % 4 = 0
  · simp only [h, R4, ↓reduceIte]; rfl
  · have h' : (BitVec.ofNat 32 (n % 4) == BitVec.zero 32) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    simp only [h', Bool.not_false, ↓reduceIte, R4, h]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_negadd (n r : Nat) (h : r ≤ n) (hn : n < 2 ^ 32) :
    BitVec.ofNat 64 n + (-BitVec.ofNat 64 r) * 1#64 + 0#64 + 1 = BitVec.ofNat 64 (n - r + 1) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_neg, BitVec.toNat_ofNat, h1]; omega

omit [CodeEnv] in
theorem rsE_lea2 (x : BitVec 64) (m : Nat) (hm : m < 2 ^ 32) :
    x + BitVec.ofNat 64 m * 2#64 + 0#64 = x + BitVec.ofNat 64 (2 * m) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- The 4-wide loop's setup: `rdx = n0 - R4 n0 - m`, `rsi = sbr + 2m`. -/
theorem blk_L2a85 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2a85" ⟨"sbr_reset.L2a85", B.L2a85, some "sbr_reset.L2aaf"⟩ := by
  info_off
  measure_hb "L2a85"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, h13, h16, h5, h9⟩, hm⟩ := T.L2a85.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have ha3 : s₀.regs.get64 .rbp + (-48 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x30) := by
      have : (-48 : Int64).toBitVec = 0xffffffffffffffd0#64 := by decide
      simp only [rb, this, hrbp]; bv_omega
    have ld1 := fr_load8 hm hF (d := 0x30) (by omega) (by omega) ha3
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1344 8)) = arg1 t₀ := h30
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have P1 := PLift.up ld1
    have Px := PLift.up hx
    have Pm := PLift.up hm
    clear h30 hx hm ld1
    have hxo' : xoOf a < nm := hxo
    have hn16 : (nm - xoOf a + 1) / 2 < 2 ^ 32 := by omega
    have h5' : m + 5 ≤ (nm - xoOf a + 1) / 2 := h5
    have hR : m ≤ (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) := by
      simp only [R4]; split <;> omega
    have hR4 : R4 ((nm - xoOf a + 1) / 2) ≤ (nm - xoOf a + 1) / 2 := by simp only [R4]; split <;> omega
    have hm32 : m < 2 ^ 32 := by omega
    have hn' : (nm - xoOf a + 1) / 2 - R4 ((nm - xoOf a + 1) / 2) < 2 ^ 32 := by omega
    have hp : (nm - xoOf a) % 2 < 2 := Nat.mod_lt _ (by omega)
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    have hW4 : BitVec.ofNat 64 Width.W32.bytes = 4#64 := rfl
    have hW1 : BitVec.ofNat 64 Width.W8.bytes = 1#64 := rfl
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2a85]
    vcgen
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, hW4, hW2, hW1,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, z] at *
    case vc1 => rw [P1.down]; rfl
    case vc2 =>
      rename_i _ v hl
      have hl := hl.symm.trans P1.down
      simp only [Option.some.injEq] at hl
      subst hl
      simp only [h15, h9, rsE_R4 _ hn16, rsE_subR _ _ hR4 hn16, rsE_negadd _ _ hR4 hn16,
        rsE_subR _ _ hR hn', h30', rsE_lea2 _ _ hm32]
      refine ⟨T.L2aaf.mpr ⟨hC, ⟨by rsE_rs; exact hrsp, by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp,
        hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, m, Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15, by rsE_rs; exact h10, by rsE_rs; exact hcx,
        by rsE_rs; exact h13, h16, h5, by rsE_rs; exact h9, by rsE_rs, by rsE_rs, by rsE_rs, by rsE_rs⟩,
        Pm.down⟩, by var_step⟩

omit [CodeEnv] in
theorem rsE_add16 (m : Nat) (h : 16 ≤ m) (hm : m < 2 ^ 32) :
    16#64 + BitVec.ofNat 64 (m - 16) = BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_ofNat_eq (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (BitVec.ofNat 64 x = BitVec.ofNat 64 y) ↔ x = y := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega
  · intro e; rw [e]

omit [CodeEnv] in
theorem rsE_var16 (r m : Nat) (h : m < r) (h16 : 16 ≤ m) (hr : r < 2 ^ 32) :
    ((BitVec.ofNat 64 r).toNat - (BitVec.ofNat 64 m).toNat) % 2 ^ 64
      < ((BitVec.ofNat 64 r).toNat - (BitVec.ofNat 64 (m - 16)).toNat) % 2 ^ 64 := by
  simp only [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsE_sw32n (r : Nat) (h : r < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 r)).toNat = r := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

set_option maxRecDepth 100000 in
/-- The 16-wide loop's latch: `rdi += 16`; then the 4-wide loop or the scalar copy. -/
theorem blk_L2a77 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2a77" ⟨"sbr_reset.L2a77", B.L2a77, some "sbr_reset.L2a85"⟩ := by
  info_off
  measure_hb "L2a77"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf64, hbr, h30, h38, m, hx, h14, h15, h10, hcx, h17, h13, h8, hsi, h9, hdx, hax, hm16, h16, hle, hdi, hx0⟩,
      hm⟩ := T.L2a77.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hxo' : xoOf a < nm := hxo
    have hle' : m ≤ (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) := hle
    have hR1 : 1 ≤ R16 ((nm - xoOf a + 1) / 2) := by simp only [R16]; split <;> omega
    have hR16 : R16 ((nm - xoOf a + 1) / 2) ≤ 16 := by simp only [R16]; split <;> omega
    have hn' : (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) < 2 ^ 32 := by omega
    have hm32 : m < 2 ^ 32 := by omega
    have hA : m ≠ (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) →
        m < (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) := by omega
    have hB : m = (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) → m < (nm - xoOf a + 1) / 2 := by
      omega
    have hB' : m = (nm - xoOf a + 1) / 2 - R16 ((nm - xoOf a + 1) / 2) →
        ¬ R16 ((nm - xoOf a + 1) / 2) < 5 → m + 5 ≤ (nm - xoOf a + 1) / 2 := by omega
    have hrdi := rsE_add16 m h16 hm32
    have heq := rsE_ofNat_eq _ _ hn' hm32
    have hr5 := rsE_sw32n (R16 ((nm - xoOf a + 1) / 2)) (by omega)
    have P30 : PLift (frSlot64 fr 0x30 = arg1 t₀) := ⟨h30⟩
    have Px := PLift.up hx
    have Pm := PLift.up hm
    have P0 := PLift.up hx0
    clear h30 hx hm hx0
    simp only [B.L2a77]
    vcgen
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth,
      Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    case vc1 =>
      rename_i hc
      simp only [hdi, h9, hrdi, Kraken.Examples.Sbr.Reset.cc_nz_sub, heq, Bool.not_eq_true',
        decide_eq_false_iff_not] at hc
      have hlt := hA (Ne.symm hc)
      exact Or.inl (Table.ofLabels_at ⟨S.L2a30, T.L2a30.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, m,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, h17, by rsE_rs; exact h13, by rsE_rs; exact h8,
        by rsE_rs; exact hsi, by rsE_rs; exact h9, by rsE_rs; exact hdx, by rsE_rs; exact hax, hm16, hlt,
        by rsE_rs; rw [hdi]; exact hrdi, P0.down⟩, Pm.down⟩, by
          left; simp only [lex_var]
          refine Kraken.lex_cons_lt_cons (by lex_len) ?_
          refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
          dsimp only
          simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdi, h9, hrdi]
          exact rsE_var16 _ _ hlt h16 hn'⟩)
    case vc2 =>
      rename_i hc hb
      simp only [hdi, h9, hrdi, Kraken.Examples.Sbr.Reset.cc_nz_sub, heq, Bool.not_eq_false',
        decide_eq_true_eq] at hc
      simp only [hdx, hr5, Kraken.Examples.Sbr.Reset.cc_c_sub, BitVec.toNat_ofNat, Nat.reduceMod,
        decide_eq_true_eq] at hb
      have hm' := hc.symm
      exact Or.inl (Table.ofLabels_at ⟨S.L2aef, T.L2aef.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, m,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, hB hm', by rsE_rs; exact h13,
        by rsE_rs; rw [hax, hm']⟩, Pm.down⟩, by edge_step⟩)
    case vc3 =>
      rename_i hc hb
      simp only [hdi, h9, hrdi, Kraken.Examples.Sbr.Reset.cc_nz_sub, heq, Bool.not_eq_false',
        decide_eq_true_eq] at hc
      simp only [hdx, hr5, Kraken.Examples.Sbr.Reset.cc_c_sub, BitVec.toNat_ofNat, Nat.reduceMod,
        decide_eq_false_iff_not, Bool.not_eq_true, decide_eq_true_eq] at hb
      have hm' := hc.symm
      refine ⟨T.L2a85.mpr ⟨hC, ⟨by rsE_rs; exact hrsp,
        by rsE_rs; exact hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf64, hbr, P30.down, h38, m,
        Px.down, by rsE_rs; exact h14, by rsE_rs; exact h15,
        by rsE_rs; exact h10, by rsE_rs; exact hcx, by rsE_rs; exact h13, hm16, hB' hm' hb,
        by rsE_rs; rw [h9, hm']⟩, Pm.down⟩, by var_step⟩


end Kraken.Examples.Sbr.Reset
