import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetE1

/-!
# `sbr_reset`: `sbr_make_f_derived`, the noise-band border loop (`derived3`, `f_tablenoise`)

`NzM x q j` is `f_tablenoise` with entry `0` stored and the entries `1..j` computed; a 2-byte
store of entry `j + 1` steps it (`rsN_NzM_step`). The bounds check (`L32b9`, the trap) is never
taken: every `temp` is at most `n[0] ≤ 24`.
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
theorem rsN_NzM_len (x : Args) (q j : Nat) : (NzM x q j).length = 12 := by simp [NzM]

omit [CodeEnv] in
/-- Entry `j + 1` stored: `j + 1` entries computed. -/
theorem rsN_NzM_step (x : Args) (q : Nat) {j : Nat} (hj : j + 1 < 6) (v : Int)
    (hv : (v % 65536).toNat = u16 x.ftLow (ntemp x.n0 q (j + 1))) :
    wr (NzM x q j) (2 * (j + 1)) (Int.toBytes 2 v) = NzM x q (j + 1) := by
  apply eq_of_u16 (k := 6) (by rw [wr_length (by rw [Int.toBytes_length, rsN_NzM_len]; omega), rsN_NzM_len])
    (by simp [NzM])
  intro i hi
  rw [rsE_u16_wr2 v (by rw [rsN_NzM_len]; omega), NzM, NzM, u16_mk16 hi]
  by_cases h1 : i = j + 1
  · subst h1; simp only [↓reduceIte, hv]; rw [u16_mk16 hi]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.le_refl]
    exact (Nat.mod_eq_of_lt (rsE_u16_lt _ _)).symm
  · simp only [h1, ↓reduceIte]
    rw [u16_mk16 hi]
    by_cases h0 : i = 0
    · simp [h0]
    · simp only [h0, ↓reduceIte]
      by_cases h2 : i ≤ j
      · simp [h2, show i ≤ j + 1 by omega]
      · simp [h2, show ¬ i ≤ j + 1 by omega]

omit [CodeEnv] in
/-- All `n_q` entries computed: `derived3`. -/
theorem rsN_dNz_q (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) (q : Nat) :
    dNz a k0 nm f q q = derived3 (dD2 a k0 nm f) q := rfl

omit [CodeEnv] in
theorem rsN_n0 (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) :
    (dD2 a k0 nm f).n0 = (nm - xoOf a + 1) / 2 := rfl

omit [CodeEnv] in
theorem rsN_and6 (q : Nat) (h : q < 6) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 q) &&& BitVec.setWidth 32 6#64)
      = BitVec.ofNat 64 (q - q % 2) := by
  obtain h | h | h | h | h | h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  all_goals subst h; decide

omit [CodeEnv] in
theorem rsN_r9 (r : BitVec 64) (q : Nat) (hq : q < 6) (h : BitVec.setWidth 32 r = BitVec.ofNat 32 q) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 r))
      &&& BitVec.setWidth 32 (Int64.toBitVec 6)) = BitVec.ofNat 64 (q - q % 2) := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), h]
  obtain h | h | h | h | h | h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  all_goals subst h; decide

omit [CodeEnv] in
theorem rsN_cx (r : BitVec 64) (q : Nat) (hq : q < 6) (h : BitVec.setWidth 32 r = BitVec.ofNat 32 q) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r) = BitVec.ofNat 64 q := by
  rw [h]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsN_sw64 (n : Nat) (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsN_sub32 (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsN_add32 (a b : Nat) (h : a + b < 2 ^ 32) :
    BitVec.ofNat 32 a + BitVec.ofNat 32 b = BitVec.ofNat 32 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsN_xor (x : BitVec 64) : BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x = BitVec.ofNat 32 0 := by
  simp

omit [CodeEnv] in
theorem rsN_toNat32 (n : Nat) (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  simp only [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem rsN_ad (x : BitVec 64) (i b c d : Nat) (h : b + 2 * i = c + d) (hb : b + 2 * i < 2 ^ 32) :
    x + BitVec.ofNat 64 i * 2#64 + BitVec.ofNat 64 b = x + BitVec.ofNat 64 c + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem rsN_lea (n : Nat) (h1 : 1 ≤ n) (h : n < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.ofNat 64 n + (0 : BitVec 64) + (-1 : Int64).toBitVec) = BitVec.ofNat 32 (n - 1) := by
  have e : (-1 : Int64).toBitVec = 0xffffffffffffffff#64 := by decide
  rw [e]; bv_omega

omit [CodeEnv] in
theorem rsN_inc32 (n : Nat) (h : n + 1 < 2 ^ 32) : BitVec.ofNat 32 n + 1 = BitVec.ofNat 32 (n + 1) := by
  bv_omega

omit [CodeEnv] in
theorem rsN_m2 (n : Nat) (h1 : 2 ≤ n) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (4294967294#32 + BitVec.ofNat 32 n) = BitVec.ofNat 64 (n - 2) := by
  bv_omega

omit [CodeEnv] in
theorem rsN_low (r : BitVec 64) (q : Nat) (hq : q < 6) (h : BitVec.setWidth 32 r = BitVec.ofNat 32 q) :
    BitVec.setWidth 8 r &&& 1#8 = BitVec.ofNat 8 (q % 2) := by
  rw [← BitVec.setWidth_setWidth_of_le (k := 8) (l := 32) r (by omega), h]
  obtain h | h | h | h | h | h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  all_goals subst h; decide

omit [CodeEnv] in
theorem rsN_ne64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega
  · intro h; rw [h]

omit [CodeEnv] in
theorem rsN_z8 (n : Nat) (h : n < 2) (fl : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.ofNat 8 n) fl) = decide (n = 0) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result]
  obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
  all_goals decide

/-- 32-bit arithmetic on small `ofNat` values (`rsN_normS`: also addresses). -/
macro "rsN_normS" : tactic => `(tactic| simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_lea,
  rsN_add32, rsN_inc32, rsN_xor, rsN_toNat32, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64,
  Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth])

macro "rsN_norm" : tactic => `(tactic| simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_lea,
  rsN_add32, rsN_inc32, rsN_xor, rsN_toNat32, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte])

set_option maxRecDepth 100000 in
/-- `n_q ≥ 2`: the loop setup (`r9 = n_q & 6`, `r10 = n_q`). -/
theorem blk_L2bde (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2bde" ⟨"sbr_reset.L2bde", B.L2bde, some "sbr_reset.L2bed"⟩ := by
  info_off
  measure_hb "L2bde"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, h11, h12, h50, h80, hcx, rfl, hq2, h15⟩, hm⟩ :=
      T.L2bde.mp hs
    clear hs
    simp only [B.L2bde]
    vcgen
    all_goals try subst_vars
    refine ⟨T.L2bed.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40, ⟨hk2, hf1, hf2, h30, h38,
      q, 0, hq1, hq6, hx, ?_, ?_, h50, h80, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals try assumption
    · exact rsE_xor_self _
    · exact rsE_xor_self _
    · exact rsN_cx _ _ hq6 hcx
    · exact rsN_r9 _ _ hq6 hcx
    · var_step

set_option maxRecDepth 100000 in
/-- The first entry of a pair: `f_tablenoise[j+1] = f_tablelow[temp]`. -/
theorem blk_L2bed (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2bed" ⟨"sbr_reset.L2bed", B.L2bed, some "sbr_reset.L2c1b"⟩ := by
  info_off
  measure_hb "L2bed"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, h11, h12, h50, h80, hcx, hj2, hjq, h15, h8, hsi, h10, h9⟩,
      hm⟩ := T.L2bed.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hn0 : (nm - xoOf a + 1) / 2 ≤ 24 := by omega
    have ht := ntemp_le ((nm - xoOf a + 1) / 2) q j
    have ht1 := ntemp_le ((nm - xoOf a + 1) / 2) q (j + 1)
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; simp [derived2, LowM]
    have hfn : st.x.ftNoise = NzM (dD2 a k0 nm (fOf st)) q j := by rw [hx]
    have hn0' : (dD2 a k0 nm (fOf st)).n0 = (nm - xoOf a + 1) / 2 := rfl
    have hfl' : (dD2 a k0 nm (fOf st)).ftLow = st.x.ftLow := by rw [hx]
    have hld : ∀ i, i = ntemp ((nm - xoOf a + 1) / 2) q (j + 1) →
        s₀.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 311890#64) 2
          = some (u16 st.x.ftLow (ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) : Int) := by
      intro i hi; subst hi
      rw [region_load (o := 2 * ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) (n := 2) (focus (Mm_ftLow ..) hm)
        (rsN_ad _ _ _ _ _ (by omega) (by omega)) (by rw [hfl]; omega) (by rw [hfl]; omega)]
      rw [ofBytes_slice2 _ _ (by omega)]
    have hfnl : st.x.ftNoise.length = 12 := by rw [hfn]; exact rsN_NzM_len _ _ _
    have hstore : ∀ i (v : Int), i = j →
        (v % 65536).toNat = u16 st.x.ftLow (ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) →
        s₀.dmem.storeInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 312040#64) 2 v
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St) fr := by
      intro i v hi hv; rw [hi]
      have h := region_store (o := 2 * (j + 1)) (n := 2) (focus (Mm_ftNoise ..) hm)
        (rsN_ad (arg1 t₀) j 312040 0x4c2e6 (2 * (j + 1)) (by omega) (by omega)) (by rw [hfnl]; omega) (by rw [hfnl]; omega) v
      rw [hfn, rsN_NzM_step _ _ (by omega) v (by rw [hn0', hfl']; exact hv), Mm_upd_ftNoise] at h
      exact h
    have hx' : ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St).x
        = dNz a k0 nm (fOf st) q (j + 1) := by
      show ({ st.x with ftNoise := _ } : Args) = _
      rw [hx]
    have hlds : ∀ i, i = j → (s₀.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 312040#64) 2).isSome = true := by
      intro i hi; rw [hi]
      rw [region_load (o := 2 * (j + 1)) (n := 2) (focus (Mm_ftNoise ..) hm)
        (rsN_ad (arg1 t₀) j 312040 0x4c2e6 (2 * (j + 1)) (by omega) (by omega)) (by rw [hfnl]; omega) (by rw [hfnl]; omega)]; rfl
    have hnt : ntemp ((nm - xoOf a + 1) / 2) q (j + 1) = ntemp ((nm - xoOf a + 1) / 2) q j
        + (0 * 2 ^ 32 + ((nm - xoOf a + 1) / 2 - ntemp ((nm - xoOf a + 1) / 2) q j)) / (q - j) := by
      rw [show q - j = q + 1 - (j + 1) by omega, Nat.zero_mul, Nat.zero_add]; rfl
    have P30 := PLift.up (And.intro h30 (And.intro h38 (And.intro h40 (And.intro h50 h80))))
    have Px := PLift.up hx'
    have Pld := PLift.up hld
    have Pst := PLift.up hstore
    have Plds := PLift.up hlds
    have PB := PLift.up (And.intro hC (And.intro hMa (And.intro hsp (And.intro hfm hF))))
    clear h30 h38 h40 h50 h80 hx hx' hm hld hstore hlds hfn hfl' hC hMa hsp hfm hF
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2bed]
    vcgen
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h10, h8, h12, h9]
    rsN_norm
    refine ⟨⟨by omega, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩, fun fl => ?_⟩
    vcgen
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h10, h8, h12, h9, hW2]
    all_goals rsN_normS
    case vc1 =>
      rename_i hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h10, h8, h12, h9, hW2] at hc
      simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_add32, rsN_xor, rsN_toNat32,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, Kraken.Examples.Sbr.Reset.cc_nc_sub,
        Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, BitVec.reduceToNat,
        decide_eq_true_eq, BitVec.toNat_ofNat] at hc
      exfalso; omega
    case vc2 => rw [Pld.down _ hnt.symm]; rfl
    case vc3 => rw [h8, hW2]; exact Plds.down _ rfl
    case vc4 =>
      rename_i v hl
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h10, h8, h12, h9, hW2] at hl
      simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_add32, rsN_xor, rsN_toNat32,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64,
        Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth] at hl
      rw [Pld.down _ hnt.symm, Option.some.injEq] at hl
      subst hl
      try simp only [h8, hW2]
      refine ⟨T.L2c1b.mpr ⟨PB.down.1, ⟨?_, ?_⟩,
        ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St), fr, nm, k0, PB.down.2.1, PB.down.2.2.1, PB.down.2.2.2.1,
        PB.down.2.2.2.2, P30.down.2.2.1, ⟨hk2, hf1, hf2, P30.down.1, P30.down.2.1, q, j + 1, hq1, hq6, Px.down,
        ?_, ?_, P30.down.2.2.2.1, P30.down.2.2.2.2, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        Pst.down _ _ rfl (rsE_val _ (rsE_u16_lt _ _))⟩, ?_⟩
      all_goals try rsN_normS
      all_goals try assumption
      · exact congrArg _ hnt.symm
      · var_step

set_option maxRecDepth 100000 in
/-- The second entry of a pair (`j` odd): `f_tablenoise[j+1] = f_tablelow[temp]`. -/
theorem blk_L2c1b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2c1b" ⟨"sbr_reset.L2c1b", B.L2c1b, some "sbr_reset.L2c4a"⟩ := by
  info_off
  measure_hb "L2c1b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, h11, h12, h50, h80, hcx, hj2, hjq, h15, h8, hdi, hax, h10, h9⟩,
      hm⟩ := T.L2c1b.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hn0 : (nm - xoOf a + 1) / 2 ≤ 24 := by omega
    have ht := ntemp_le ((nm - xoOf a + 1) / 2) q j
    have ht1 := ntemp_le ((nm - xoOf a + 1) / 2) q (j + 1)
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; simp [derived2, LowM]
    have hfn : st.x.ftNoise = NzM (dD2 a k0 nm (fOf st)) q j := by rw [hx]
    have hn0' : (dD2 a k0 nm (fOf st)).n0 = (nm - xoOf a + 1) / 2 := rfl
    have hfl' : (dD2 a k0 nm (fOf st)).ftLow = st.x.ftLow := by rw [hx]
    have hld : ∀ i, i = ntemp ((nm - xoOf a + 1) / 2) q (j + 1) →
        s₀.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 311890#64) 2
          = some (u16 st.x.ftLow (ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) : Int) := by
      intro i hi; subst hi
      rw [region_load (o := 2 * ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) (n := 2) (focus (Mm_ftLow ..) hm)
        (rsN_ad _ _ _ _ _ (by omega) (by omega)) (by rw [hfl]; omega) (by rw [hfl]; omega)]
      rw [ofBytes_slice2 _ _ (by omega)]
    have hfnl : st.x.ftNoise.length = 12 := by rw [hfn]; exact rsN_NzM_len _ _ _
    have hstore : ∀ i (v : Int), i = j - 1 →
        (v % 65536).toNat = u16 st.x.ftLow (ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) →
        s₀.dmem.storeInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 312042#64) 2 v
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St) fr := by
      intro i v hi hv; rw [hi]
      have h := region_store (o := 2 * (j + 1)) (n := 2) (focus (Mm_ftNoise ..) hm)
        (rsN_ad (arg1 t₀) (j - 1) 312042 0x4c2e6 (2 * (j + 1)) (by omega) (by omega)) (by rw [hfnl]; omega) (by rw [hfnl]; omega) v
      rw [hfn, rsN_NzM_step _ _ (by omega) v (by rw [hn0', hfl']; exact hv), Mm_upd_ftNoise] at h
      exact h
    have hx' : ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St).x
        = dNz a k0 nm (fOf st) q (j + 1) := by
      show ({ st.x with ftNoise := _ } : Args) = _
      rw [hx]
    have hlds : ∀ i, i = j - 1 → (s₀.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 312042#64) 2).isSome = true := by
      intro i hi; rw [hi]
      rw [region_load (o := 2 * (j + 1)) (n := 2) (focus (Mm_ftNoise ..) hm)
        (rsN_ad (arg1 t₀) (j - 1) 312042 0x4c2e6 (2 * (j + 1)) (by omega) (by omega)) (by rw [hfnl]; omega) (by rw [hfnl]; omega)]; rfl
    have hnt : ntemp ((nm - xoOf a + 1) / 2) q (j + 1) = ntemp ((nm - xoOf a + 1) / 2) q j
        + (0 * 2 ^ 32 + ((nm - xoOf a + 1) / 2 - ntemp ((nm - xoOf a + 1) / 2) q j)) / (q - (j - 1) - 1) := by
      rw [show q - (j - 1) - 1 = q + 1 - (j + 1) by omega, Nat.zero_mul, Nat.zero_add]; rfl
    have P30 := PLift.up (And.intro h30 (And.intro h38 (And.intro h40 (And.intro h50 h80))))
    have Px := PLift.up hx'
    have Pld := PLift.up hld
    have Pst := PLift.up hstore
    have Plds := PLift.up hlds
    have PB := PLift.up (And.intro hC (And.intro hMa (And.intro hsp (And.intro hfm hF))))
    clear h30 h38 h40 h50 h80 hx hx' hm hld hstore hlds hfn hfl' hC hMa hsp hfm hF
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2c1b]
    vcgen
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hdi, hax, h10, h8, h12, h9]
    simp only [AddrIndex.offset64_none]
    rsN_norm
    refine ⟨⟨by omega, Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩, fun fl => ?_⟩
    vcgen
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hdi, hax, h10, h8, h12, h9, hW2]
    all_goals try rsN_normS
    case vc1 =>
      rename_i hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hdi, hax, h10, h8, h12, h9, hW2,
        AddrIndex.offset64_none] at hc
      simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_add32, rsN_xor, rsN_toNat32, rsN_lea,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, Kraken.Examples.Sbr.Reset.cc_a_sub,
        Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, BitVec.reduceToNat,
        decide_eq_true_eq, BitVec.toNat_ofNat] at hc
      exfalso; omega
    case vc2 => rw [Pld.down _ hnt.symm]; rfl
    case vc3 => rw [h8, hW2]; exact Plds.down _ rfl
    case vc4 =>
      rename_i v hl
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hdi, hax, h10, h8, h12, h9, hW2,
        AddrIndex.offset64_none] at hl
      simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_add32, rsN_xor, rsN_toNat32, rsN_lea,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64,
        Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth] at hl
      rw [Pld.down _ hnt.symm, Option.some.injEq] at hl
      subst hl
      try simp only [h8, hW2]
      refine ⟨T.L2c4a.mpr ⟨PB.down.1, ⟨?_, ?_⟩,
        ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St), fr, nm, k0,
        PB.down.2.1, PB.down.2.2.1, PB.down.2.2.2.1,
        PB.down.2.2.2.2, P30.down.2.2.1, ⟨hk2, hf1, hf2, P30.down.1, P30.down.2.1, q, j + 1, hq1, hq6, Px.down,
        ?_, ?_, P30.down.2.2.2.1, P30.down.2.2.2.2, ?_, by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩,
        Pst.down _ _ rfl (rsE_val _ (rsE_u16_lt _ _))⟩, ?_⟩
      all_goals try rsN_normS
      all_goals try assumption
      · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · exact congrArg _ hnt.symm
      · have hr8 : 2#64 + BitVec.ofNat 64 (j - 1) = BitVec.ofNat 64 (j + 1) := by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
        simp only [lex_var]
        refine Kraken.lex_cons_le_cons (by lex_len) ?_
        refine Kraken.lex_cons_le_of_lt (by lex_len) ?_
        dsimp only
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, h9, hr8]
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show q - q % 2 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show j + 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j - 1 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show q - q % 2 - (j + 1) < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show q - q % 2 - (j - 1) < 2 ^ 64 by omega)]
        omega


set_option maxRecDepth 100000 in
/-- After a pair: `r10 -= 2`; back to `L2bed`, or done (`n_q` even), or the last entry. -/
theorem blk_L2c4a (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2c4a" ⟨"sbr_reset.L2c4a", B.L2c4a, some "sbr_reset.L2c5b"⟩ := by
  info_off
  measure_hb "L2c4a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, h11, h12, h50, h80, hcx, hj2, hj1, hjq, h15, h8, hsi, h10, h9⟩,
      hm⟩ := T.L2c4a.mp hs
    clear hs
    simp only [B.L2c4a]
    vcgen
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h10, h8, h12, h9,
      AddrIndex.offset64_none]
    all_goals try rsN_normS
    all_goals try simp only [rsN_m2 _ (by omega : 2 ≤ q - (j - 2)) (by omega), rsN_low _ _ hq6 hcx]
    case vc1 =>
      rename_i hc
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h9, h8, rsN_ne64 _ _ (by omega : q - q % 2 < 2 ^ 64)
        (by omega : j < 2 ^ 64), Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, rsN_low _ _ hq6 hcx,
        rsN_z8 _ (Nat.mod_lt _ (by omega : 0 < 2)),
        Kraken.Examples.Sbr.Reset.cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
        decide_eq_true_eq] at hc
      refine Or.inl (Table.ofLabels_at ⟨S.L2bed, T.L2bed.mpr ⟨hC, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption)⟩, st, fr, nm, k0, hMa, hsp, hfm,
        hF, h40, ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), h50, h80, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), hj2, by omega, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption),
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), ?_, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption)⟩, hm⟩, ?_⟩)
      · simp only [Reg64s.get64_set64, ↓reduceIte]; congr 1; omega
      · left; simp only [lex_var]; try dsimp only
        try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        refine Kraken.lex_cons_lt_cons (by lex_len) ?_
        refine Kraken.lex_cons_lt_cons (by lex_len) ?_
        refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
        decide
    case vc2 =>
      rename_i hc0 hc1 hc2
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h9, h8, rsN_ne64 _ _ (by omega : q - q % 2 < 2 ^ 64)
        (by omega : j < 2 ^ 64), Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, rsN_low _ _ hq6 hcx,
        rsN_z8 _ (Nat.mod_lt _ (by omega : 0 < 2)),
        Kraken.Examples.Sbr.Reset.cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
        decide_eq_true_eq] at hc0
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h9, h8, rsN_ne64 _ _ (by omega : q - q % 2 < 2 ^ 64)
        (by omega : j < 2 ^ 64), Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, rsN_low _ _ hq6 hcx,
        rsN_z8 _ (Nat.mod_lt _ (by omega : 0 < 2)),
        Kraken.Examples.Sbr.Reset.cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
        decide_eq_true_eq] at hc2
      refine Or.inl (Table.ofLabels_at ⟨S.L2c89, T.L2c89.mpr ⟨hC, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption)⟩, st, fr, nm, k0, hMa, hsp, hfm,
        hF, h40, ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), h50, h80, by omega⟩, hm⟩, by edge_step⟩)
    case vc3 =>
      rename_i hc0 hc1 hc2
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h9, h8, rsN_ne64 _ _ (by omega : q - q % 2 < 2 ^ 64)
        (by omega : j < 2 ^ 64), Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, rsN_low _ _ hq6 hcx,
        rsN_z8 _ (Nat.mod_lt _ (by omega : 0 < 2)),
        Kraken.Examples.Sbr.Reset.cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
        decide_eq_true_eq] at hc0
      try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h9, h8, rsN_ne64 _ _ (by omega : q - q % 2 < 2 ^ 64)
        (by omega : j < 2 ^ 64), Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, rsN_low _ _ hq6 hcx,
        rsN_z8 _ (Nat.mod_lt _ (by omega : 0 < 2)),
        Kraken.Examples.Sbr.Reset.cc_nz_sub, Bool.not_eq_true', Bool.not_eq_false', decide_eq_false_iff_not,
        decide_eq_true_eq] at hc2
      refine ⟨T.L2c5b.mpr ⟨hC, ⟨(by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption)⟩, st, fr, nm, k0, hMa, hsp, hfm,
        hF, h40, ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), h50, h80, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), by omega, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption), ?_, (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; assumption)⟩, hm⟩,
        by var_step⟩
      simp only [Reg64s.get64_set64, ↓reduceIte, rsE_inc j (by omega)]; congr 1; omega

set_option maxRecDepth 100000 in
/-- The last entry: `f_tablenoise[n_q] = f_tablelow[n0]`. -/
theorem blk_L2c5b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2c5b" ⟨"sbr_reset.L2c5b", B.L2c5b, some "sbr_reset.L2c89"⟩ := by
  info_off
  measure_hb "L2c5b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, nm, k0, hMa, hsp, hfm, hF, h40,
      ⟨hk2, hf1, hf2, h30, h38, q, j, hq1, hq6, hx, h11, h12, h50, h80, hcx, hjq, h15, h8, hsi⟩,
      hm⟩ := T.L2c5b.mp hs
    clear hs
    obtain ⟨hxo, hnm, -, -⟩ := master_bounds hMa
    have hn0 : (nm - xoOf a + 1) / 2 ≤ 24 := by omega
    have ht := ntemp_le ((nm - xoOf a + 1) / 2) q j
    have ht1 := ntemp_le ((nm - xoOf a + 1) / 2) q (j + 1)
    have hfl : st.x.ftLow.length = 50 := by rw [hx]; simp [derived2, LowM]
    have hfn : st.x.ftNoise = NzM (dD2 a k0 nm (fOf st)) q j := by rw [hx]
    have hn0' : (dD2 a k0 nm (fOf st)).n0 = (nm - xoOf a + 1) / 2 := rfl
    have hfl' : (dD2 a k0 nm (fOf st)).ftLow = st.x.ftLow := by rw [hx]
    have hld : ∀ i, i = ntemp ((nm - xoOf a + 1) / 2) q (j + 1) →
        s₀.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 311890#64) 2
          = some (u16 st.x.ftLow (ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) : Int) := by
      intro i hi; subst hi
      rw [region_load (o := 2 * ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) (n := 2) (focus (Mm_ftLow ..) hm)
        (rsN_ad _ _ _ _ _ (by omega) (by omega)) (by rw [hfl]; omega) (by rw [hfl]; omega)]
      rw [ofBytes_slice2 _ _ (by omega)]
    have hfnl : st.x.ftNoise.length = 12 := by rw [hfn]; exact rsN_NzM_len _ _ _
    have hstore : ∀ i (v : Int), i = j + 1 →
        (v % 65536).toNat = u16 st.x.ftLow (ntemp ((nm - xoOf a + 1) / 2) q (j + 1)) →
        s₀.dmem.storeInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 0x4c2e6#64) 2 v
          =⋆ Mm k e a ra t₀ ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St) fr := by
      intro i v hi hv; rw [hi]
      have h := region_store (o := 2 * (j + 1)) (n := 2) (focus (Mm_ftNoise ..) hm)
        (rsN_ad (arg1 t₀) (j + 1) 0x4c2e6 0x4c2e6 (2 * (j + 1)) (by omega) (by omega)) (by rw [hfnl]; omega) (by rw [hfnl]; omega) v
      rw [hfn, rsN_NzM_step _ _ (by omega) v (by rw [hn0', hfl']; exact hv), Mm_upd_ftNoise] at h
      exact h
    have hx' : ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) q (j + 1) } } : St).x
        = dNz a k0 nm (fOf st) q (j + 1) := by
      show ({ st.x with ftNoise := _ } : Args) = _
      rw [hx]
    have hlds : ∀ i, i = j + 1 → (s₀.dmem.loadInt (arg1 t₀ + BitVec.ofNat 64 i * 2#64 + 0x4c2e6#64) 2).isSome = true := by
      intro i hi; rw [hi]
      rw [region_load (o := 2 * (j + 1)) (n := 2) (focus (Mm_ftNoise ..) hm)
        (rsN_ad (arg1 t₀) (j + 1) 0x4c2e6 0x4c2e6 (2 * (j + 1)) (by omega) (by omega)) (by rw [hfnl]; omega) (by rw [hfnl]; omega)]; rfl
    have hnt : ntemp ((nm - xoOf a + 1) / 2) q (j + 1) = ntemp ((nm - xoOf a + 1) / 2) q j
        + (0 * 2 ^ 32 + ((nm - xoOf a + 1) / 2 - ntemp ((nm - xoOf a + 1) / 2) q j)) / (q + 1 - (j + 1)) := by
      rw [Nat.zero_mul, Nat.zero_add]; rfl
    have P30 := PLift.up (And.intro h30 (And.intro h38 (And.intro h40 (And.intro h50 h80))))
    have Px := PLift.up hx'
    have Pld := PLift.up hld
    have Pst := PLift.up hstore
    have Plds := PLift.up hlds
    have PB := PLift.up (And.intro hC (And.intro hMa (And.intro hsp (And.intro hfm hF))))
    clear h30 h38 h40 h50 h80 hx hx' hm hld hstore hlds hfn hfl' hC hMa hsp hfm hF
    have hW2 : BitVec.ofNat 64 Width.W16.bytes = 2#64 := rfl
    simp only [B.L2c5b]
    vcgen
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h8, h12, hcx]
    rsN_norm
    have hdiv : (0 * 2 ^ 32 + ((nm - xoOf a + 1) / 2 - ntemp ((nm - xoOf a + 1) / 2) (j + 1) j)) / (j + 1 + 1 - (j + 1))
        < 2 ^ 32 := by
      rw [show j + 1 + 1 - (j + 1) = 1 by omega, Nat.div_one, Nat.zero_mul, Nat.zero_add]
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
    refine ⟨⟨by omega, hdiv⟩, fun fl => ?_⟩
    vcgen
    all_goals try subst_vars
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h8, h12, hcx, hW2]
    all_goals try rsN_normS
    case vc1 =>
      rename_i hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h8, h12, hcx, hW2] at hc
      simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_add32, rsN_inc32, rsN_xor, rsN_toNat32,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, Kraken.Examples.Sbr.Reset.cc_a_sub,
        Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth, BitVec.reduceToNat,
        decide_eq_true_eq, BitVec.toNat_ofNat] at hc
      exfalso; omega
    case vc2 => rw [Pld.down _ hnt.symm]; rfl
    case vc3 => rw [h8, hW2]; exact Plds.down _ rfl
    case vc4 =>
      rename_i v hl
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h15, hsi, h8, h12, hcx, hW2] at hl
      simp (disch := omega) only [rsE_sw32, rsN_sw64, rsN_sub32, rsN_add32, rsN_inc32, rsN_xor, rsN_toNat32,
        Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, AddrIndex.offset64,
        Int64.toBitVec_ofNat_norm, BitVec.reduceSetWidth] at hl
      rw [Pld.down _ hnt.symm, Option.some.injEq] at hl
      subst hl
      try simp only [h8, hW2]
      refine ⟨T.L2c89.mpr ⟨PB.down.1, ⟨?_, ?_⟩,
        ({ st with x := { st.x with ftNoise := NzM (dD2 a k0 nm (fOf st)) (j + 1) (j + 1) } } : St), fr, nm, k0,
        PB.down.2.1, PB.down.2.2.1, PB.down.2.2.2.1,
        PB.down.2.2.2.2, P30.down.2.2.1, ⟨hk2, hf1, hf2, P30.down.1, P30.down.2.1, j + 1, j + 1, hq1, hq6, Px.down,
        ?_, ?_, P30.down.2.2.2.1, P30.down.2.2.2.2, rfl⟩,
        Pst.down _ _ rfl (rsE_val _ (rsE_u16_lt _ _))⟩, ?_⟩
      all_goals try rsN_normS
      all_goals try assumption
      var_step

end Kraken.Examples.Sbr.Reset
