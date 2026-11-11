import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1K2
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: `bs_freq_scale = 0`, `n_master` (shard A1)

`L1779`: `dk = bs_alter_scale + 1`, `n_master = ((k[2] - k[0] + (dk & 2)) >> dk) << 1` stored.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

section Mem

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

/-- A store of `n_master`. -/
theorem a1_nm_store (hm : m =⋆ Mm k e a ra t₀ st fr) (v : BitVec 32) :
    m.storeInt (arg1 t₀ + 0x68#64) 4 v.toInt =⋆ Mm k e a ra t₀ { st with nm := v } fr :=
  Mm_upd_nm .. ▸ cell4_store' (focus (Mm_nm ..) hm) v.toInt v rfl

theorem a1_nm_isSome (hm : m =⋆ Mm k e a ra t₀ st fr) :
    (m.loadInt (arg1 t₀ + 0x68#64) 4).isSome = true :=
  cell4_isSome (focus (Mm_nm ..) hm)

end Mem

omit [CodeEnv] in
theorem f0_q0 {d : Nat} (hd : d ≤ 64) : (BitVec.ofNat 32 d).ushiftRight 1 = BitVec.ofNat 32 (d / 2) := by
  show BitVec.ofNat 32 d >>> 1 = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]; omega

omit [CodeEnv] in
theorem f0_q1 {d : Nat} (hd : d ≤ 64) :
    (BitVec.ofNat 32 d + 2#32).ushiftRight 2 = BitVec.ofNat 32 ((d + 2) / 4) := by
  show (BitVec.ofNat 32 d + 2#32) >>> 2 = _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]; omega

omit [CodeEnv] in
theorem f0_dbl (q : Nat) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 q) + BitVec.setWidth 64 (BitVec.ofNat 32 q))
      = BitVec.ofNat 32 (2 * q) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem f0_cc_z_and (x : BitVec 32) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (x &&& x) f) = decide (x = 0) := by
  rw [CondCode.interp_z, BitVec.and_self]
  by_cases h : x = 0
  · simp [h, StatusFlags.from_result]
  · simp [StatusFlags.from_result]; exact rfl

/-- The value simp set of `L1779`. -/
syntax "f0s" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| f0s $[$loc]?) => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      BitVec.reduceOfInt, BitVec.reduceSetWidth,
      BitVec.reduceAdd, BitVec.reduceAnd, BitVec.reduceToNat, Nat.reduceMod, a1_sw_ofNat64,
      AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      sw32_64, f0_cc_z_and, decide_eq_true_eq, decide_eq_false_iff_not] $[$loc]?)

set_option hygiene false in
/-- The `bs_alter_scale` load of `L1779`, by its value. -/
macro "f0_ld " hv:ident : tactic => `(tactic| (
  simp only [h12, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero] at $hv:ident
  rw [ldA] at $hv:ident
  obtain rfl := Option.some.inj $hv:ident
  f0s))

section FM

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

omit [CodeEnv] in
theorem a1_fm_addr (b : BitVec 64) {j : Nat} (_hj : j ≤ 48) :
    b + BitVec.ofNat 64 j * 2#64 + 311792#64 = b + 0x4c1f0#64 + BitVec.ofNat 64 (2 * j) := by
  have : BitVec.ofNat 64 (2 * j) = BitVec.ofNat 64 j * 2#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 j * 2#64)]

/-- A 16-bit store into `f_master[j]`. -/
theorem a1_fm_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {j : Nat} (hj : j ≤ 48)
    (v : Int) :
    m.storeInt (arg1 t₀ + BitVec.ofNat 64 j * 2#64 + 311792#64) 2 v
      =⋆ Mm k e a ra t₀ { st with fm := wr st.fm (2 * j) (Int.toBytes 2 v) } fr :=
  Mm_upd_fm .. ▸ region_store (focus (Mm_fm ..) hm) (o := 2 * j) (a1_fm_addr _ hj) (by omega)
    (by omega) v

theorem a1_fm_isSome (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {j : Nat}
    (hj : j ≤ 48) : (m.loadInt (arg1 t₀ + BitVec.ofNat 64 j * 2#64 + 311792#64) 2).isSome = true := by
  rw [region_load (focus (Mm_fm ..) hm) (o := 2 * j) (n := 2) (a1_fm_addr _ hj) (by omega)
    (by omega)]
  rfl

end FM

omit [CodeEnv] in
theorem a1_ofBytes_slice2 (l : List UInt8) (i : Nat) (h : 2 * i + 2 ≤ l.length) :
    Int.ofBytes (slice l (2 * i) 2) = (u16 l i : Int) := by
  have e : slice l (2 * i) 2 = [l[2 * i], l[2 * i + 1]] := by
    apply List.ext_getElem (by simp only [slice, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]; omega)
    intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [slice, List.getElem_take, List.getElem_drop]
    rcases j with _ | _ | j
    · rfl
    · rfl
    · omega
  rw [e, Int.ofBytes_cons, Int.ofBytes_cons]
  unfold u16 u8
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some, show Int.ofBytes [] = 0 from rfl]
  omega

omit [CodeEnv] in
theorem a1_u16_wr_ne {l v : List UInt8} {o i : Nat} (h : o + v.length ≤ l.length)
    (hi : 2 * i + 2 ≤ o ∨ o + v.length ≤ 2 * i) : u16 (wr l o v) i = u16 l i := by
  unfold u16 u8
  simp only [List.getD_eq_getElem?_getD, getElem?_wr_ne h (by omega : 2 * i < o ∨ o + v.length ≤ 2 * i),
    getElem?_wr_ne h (by omega : 2 * i + 1 < o ∨ o + v.length ≤ 2 * i + 1)]

omit [CodeEnv] in
theorem a1_u16_wr_same {l : List UInt8} {j : Nat} {v : Nat} (h : 2 * j + 2 ≤ l.length) (hv : v < 65536) :
    u16 (wr l (2 * j) (Int.toBytes 2 v)) j = v := by
  have hb : (Int.toBytes 2 (v : Int)).length = 2 := Int.toBytes_length ..
  have h1 := a1_ofBytes_slice2 (wr l (2 * j) (Int.toBytes 2 v)) j (by rw [wr_length (by omega)]; omega)
  have h2 := slice_wr_same (l := l) (o := 2 * j) (v := Int.toBytes 2 v) (by omega)
  rw [hb] at h2
  rw [h2, Int.ofBytes_toBytes_of_lt 2 v (by omega) (by simp only [Nat.reduceMul]; omega)] at h1
  omega

omit [CodeEnv] in
theorem a1_filled_step {l : List UInt8} {dk j : Nat} (hl : l.length = 98) (hj : j ≤ 48)
    (hd : dk < 65536) (hf : Filled l dk j) : Filled (wr l (2 * j) (Int.toBytes 2 dk)) dk (j + 1) := by
  intro i h1 h2
  have hb : (Int.toBytes 2 (dk : Int)).length = 2 := Int.toBytes_length ..
  rcases (show i < j ∨ i = j by omega) with h | rfl
  · rw [a1_u16_wr_ne (by omega) (by omega)]; exact hf i h1 h
  · exact a1_u16_wr_same (by omega) hd

omit [CodeEnv] in
theorem a1_dk_val (x : Nat) (hx : x ≤ 1) :
    (BitVec.setWidth 16 (BitVec.ofNat 64 (x + 1))).toInt = ((x + 1 : Nat) : Int) := by
  rcases (show x = 0 ∨ x = 1 by omega) with rfl | rfl <;> decide

/-- A 16-bit store into `f_master[0]`. -/
theorem a1_fm_store0 {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) (v : Int) :
    m.storeInt (arg1 t₀ + 311792#64) 2 v
      =⋆ Mm k e a ra t₀ { st with fm := wr st.fm (2 * 0) (Int.toBytes 2 v) } fr :=
  Mm_upd_fm .. ▸ region_store (focus (Mm_fm ..) hm) (o := 2 * 0) (by bv_omega) (by omega) (by omega) v

theorem a1_fm_isSome0 {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) :
    (m.loadInt (arg1 t₀ + 311792#64) 2).isSome = true := by
  rw [region_load (focus (Mm_fm ..) hm) (o := 0) (n := 2) (by bv_omega) (by omega) (by omega)]
  rfl

omit [CodeEnv] in
theorem a1_mask8 : ∀ n, n < 49 → (BitVec.ofNat 32 n &&& 4294967288#32) = BitVec.ofNat 32 (n / 8 * 8) := by
  decide

omit [CodeEnv] in
theorem a1_mask8' (n : Nat) (h : n < 49) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)))
      &&& BitVec.setWidth 32 4294967288#64) = BitVec.ofNat 64 (n / 8 * 8) := by
  have e1 : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)))
      = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have e2 : BitVec.setWidth 32 4294967288#64 = 4294967288#32 := by decide
  rw [e1, e2, a1_mask8 n h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem a1_summed0 {l : List UInt8} (hl : l.length = 98) {k0 dk nm : Nat} {diff : Int} (_hnm : nm ≤ 48)
    (hk : k0 < 32768) (hs : Stepped l dk nm diff) :
    Summed (wr l (2 * 0) (Int.toBytes 2 k0)) k0 dk nm diff 0 := by
  have hb : (Int.toBytes 2 (k0 : Int)).length = 2 := Int.toBytes_length ..
  constructor
  · intro i hi
    obtain rfl : i = 0 := by omega
    rw [a1_u16_wr_same (by omega) (by omega)]
    rfl
  · intro i h1 h2
    rw [a1_u16_wr_ne (by omega) (by omega)]
    exact hs i (by omega) h2

omit [CodeEnv] in
theorem a1_k0_w (k0 : Nat) (hk : k0 < 32768) :
    (BitVec.setWidth 16 (BitVec.ofNat 64 k0)).toInt = k0 := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split <;> omega

omit [CodeEnv] in
theorem a1_k0_w' (k0 : Nat) (hk : k0 < 32768) :
    BitVec.setWidth 16 (BitVec.ofNat 64 k0) = BitVec.ofInt 16 (k0 : Int) := by
  apply BitVec.eq_of_toInt_eq
  rw [a1_k0_w k0 hk, BitVec.toInt_ofInt]
  simp only [Int.bmod]
  split <;> omega

theorem blk_L1779 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1779" ⟨"sbr_reset.L1779", B.L1779, some "sbr_reset.L17a0"⟩ := by
  info_off
  measure_hb "L1779"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨row, k2, hr, hk2, hle, hq, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF, hk2s, hm⟩,
      h12, h15, hsi, h13, hcx⟩, h3⟩ := T.L1779.mp hs
    clear hs
    have hl : st.sp.length = 6 := by rw [hsp]; exact hC.1
    have ldA := a1_sp_load hm hl (i := 4) (by decide)
    rw [a1_slice_one (by rw [hl]; decide), a1_ofBytes_one, hsp,
      show BitVec.ofNat 64 (0x1c + 4) = 32#64 from rfl] at ldA
    have ldN := a1_nm_isSome hm
    have hst := fun v => a1_nm_store hm v
    have ldV := fun v => avctx_load (hst v)
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = (if (a.sp.getD 4 0).toNat = 0 then (k2 - k0N a row) / 2
        else (k2 - k0N a row + 2) / 4) ∧ True := ⟨_, rfl, trivial⟩
    have hN : nmOf (k2 - k0N a row) (u8 a.sp 4) = 2 * Q := by
      rw [hQ.1]; simp only [nmOf, u8]; split <;> rfl
    have hd : k2 - k0N a row ≤ 64 := by omega
    have hA4 : (a.sp.getD 4 0).toNat ≤ 1 := hC.2.2.2.1
    rcases (show (a.sp.getD 4 0).toNat = 0 ∨ (a.sp.getD 4 0).toNat = 1 by omega) with hA | hA
    all_goals
      rw [hA] at ldA
      first | rw [show ((0 : Nat) : Int) = 0 from rfl] at ldA | rw [show ((1 : Nat) : Int) = 1 from rfl] at ldA
      simp (config := { decide := true }) only [hA, ↓reduceIte] at hQ
      simp only [B.L1779]
      vcgen
      all_goals try subst_vars
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      · exact ldA ▸ rfl
      · rename_i v hv b1 b2 b3 b4
        f0_ld hv
        simp only [h12]; exact ldN
      · rename_i v hv b1 b2 b3 b4
        f0_ld hv
        simp only [hcx, h12, h15, a1_sw_ofNat64, f0_q0 hd, f0_q1 hd, ← hQ.1, f0_dbl Q]
        rw [ldV]; rfl
      · rename_i v hv b1 b2 b3 b4 w hw b5 hz
        f0_ld hv
        f0s at hw hz ⊢
        simp only [hcx, h12, h15, a1_sw_ofNat64, f0_q0 hd, f0_q1 hd, ← hQ.1,
          f0_dbl Q] at hw hz ⊢
        rw [ldV] at hw; obtain rfl := Option.some.inj hw
        refine Or.inl (Table.ofLabels_at ⟨S.L1d0d, T.L1d0d.mpr ⟨a1_K0S_fail (P := fun _ _ _ => True)
          ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, { st with nm := BitVec.ofNat 32 (2 * Q) }, fr, hx, hsp, hfm,
          hF, trivial, hst _⟩, ?_, ?_⟩, ?_⟩, by edge_step⟩)
        all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
          BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hx]
      · rename_i v hv b1 b2 b3 b4 w hw b5 hz
        f0_ld hv
        f0s at hw hz ⊢
        simp only [hcx, h12, h15, a1_sw_ofNat64, f0_q0 hd, f0_q1 hd, ← hQ.1,
          f0_dbl Q] at hw hz ⊢
        rw [ldV] at hw; obtain rfl := Option.some.inj hw
        have hQ0 : Q ≠ 0 := fun h => hz (by rw [h])
        refine ⟨T.L17a0.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩,
          { st with nm := BitVec.ofNat 32 (2 * Q) }, fr, hx, hsp, hfm, hF,
          ⟨hk2s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hst _⟩, ?_, ?_⟩, by var_step⟩
        all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
          hsi, h13, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hx, hN]
        all_goals first
          | omega
          | (apply BitVec.eq_of_toNat_eq
             simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, u8]
             omega)
          | with_reducible rfl

omit [CodeEnv] in
theorem f0_nm_le (d alt : Nat) : nmOf d alt ≤ d := by
  unfold nmOf; split <;> omega

omit [CodeEnv] in
theorem f0_maxQ_le (x : Int) : maxQ x ≤ 48 := by
  unfold maxQ; split
  · omega
  · split <;> omega

omit [CodeEnv] in
/-- `n_master ≤ 48` from the checks on `k[0]`, `k[2]`. -/
theorem f0_nm_48 {a : RArgs} {row k2 : Nat} (hr : rateRow (srI a) = some row) (h0 : u8 a.sp 0 < 16)
    (hq : (k2 : Int) - k0A a row ≤ maxQ (srI a)) :
    nmOf (k2 - k0N a row) (u8 a.sp 4) ≤ 48 := by
  have h1 := k0Of_range hr (st := u8 a.sp 0) h0
  have h2 := f0_maxQ_le (srI a)
  have h3 := f0_nm_le (k2 - k0N a row) (u8 a.sp 4)
  simp only [k0N, k0A] at *
  omega

set_option hygiene false in
/-- The simp set of `L17a0`. -/
syntax "f1s" (Lean.Parser.Tactic.location)? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| f1s $[$loc]?) => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      h12, h15, hcx, a1_sw_ofNat64, a1_zx_byte32, a1_zx_byte, cc_be_sub, cc_c_sub, cc_nc_sub, cc_z_sub,
      decide_eq_true_eq, decide_eq_false_iff_not, BitVec.toNat_ofNat, Nat.reducePow,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, sw32_64, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, AddrIndex.offset64_none, BitVec.add_zero, BitVec.reduceSetWidth] $[$loc]?)

set_option hygiene false in
/-- The `bs_xover_band` load of `L17a0`. -/
macro "f1_ld " hv:ident : tactic => `(tactic| (
  simp only [h12, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero] at $hv:ident
  rw [ldX] at $hv:ident
  obtain rfl := Option.some.inj $hv:ident))

omit [CodeEnv] in
theorem f1_dec {N : Nat} (h1 : 1 ≤ N) (h2 : N ≤ 48) :
    BitVec.setWidth 32 (BitVec.ofNat 64 N + (-1 : Int64).toBitVec) = BitVec.ofNat 32 (N - 1) := by
  rw [show (-1 : Int64).toBitVec = -1#64 by decide]
  have e : BitVec.ofNat 64 N + -1#64 = BitVec.ofNat 64 (N - 1) := by
    rw [← BitVec.sub_eq_add_neg]; bv_omega
  rw [e]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega

omit [CodeEnv] in
theorem f1_min {N : Nat} (h2 : N ≤ 48) :
    (if (BitVec.ofNat 32 (N - 1)).toNat < 48 % 4294967296 then BitVec.ofNat 32 (N - 1) else 48#32)
      = BitVec.ofNat 32 (N - 1) := by
  split
  · rfl
  · rename_i h; simp only [BitVec.toNat_ofNat] at h; omega

theorem blk_L17a0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L17a0" ⟨"sbr_reset.L17a0", B.L17a0, some "sbr_reset.L17d6"⟩ := by
  info_off
  measure_hb "L17a0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, h2, hnm, hcx, hsi, h13, hax, hdi⟩, hm⟩, h12, h15⟩ := T.L17a0.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hl : st.sp.length = 6 := by rw [hsp]; exact hC.1
    have ldX := a1_sp_load hm hl (i := 2) (by decide)
    rw [a1_slice_one (by rw [hl]; decide), a1_ofBytes_one, hsp,
      show BitVec.ofNat 64 (0x1c + 2) = 30#64 from rfl] at ldX
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    simp only [B.L17a0]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · exact ldX ▸ rfl
    · rename_i v hv g1
      f1_ld hv
      f1s at g1 ⊢
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1d1b, T.L1d1b.mpr ⟨a1_K0S_fail (P := fun _ _ _ => True)
        ⟨row, hr, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, trivial, hm⟩, ?_, ?_⟩, ?_⟩, by edge_step⟩)
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi, hsi,
            h13, hax, hcx]; done)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi, hsi,
            h13, hax, hcx]; rfl)
        | omega
        | (intro i hi1 hi2; omega)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hcx]
           apply BitVec.eq_of_toNat_eq
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
           omega)
        | (have := (a.sp.getD 2 0).toNat_lt; omega)
    · rename_i v hv g1 g2
      f1_ld hv
      f1s at g1 g2 ⊢
      simp only [f1_dec (by omega) h48, f1_min h48] at g2
      exfalso
      have := congrArg BitVec.toNat g2
      simp only [BitVec.toNat_ofNat] at this
      omega
    · rename_i v hv g1 g2 g3
      f1_ld hv
      f1s at g1 g2 g3 ⊢
      simp only [f1_dec (by omega) h48, f1_min h48] at g2 g3 ⊢
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1ea8, T.L1ea8.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, ⟨hk2s, ⟨⟨h2, ?_, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, 1, ?_,
        Nat.le_refl 1, ?_, ?_⟩, hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi, hsi,
            h13, hax, hcx]; done)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi, hsi,
            h13, hax, hcx]; rfl)
        | omega
        | (intro i hi1 hi2; omega)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hcx]
           apply BitVec.eq_of_toNat_eq
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
           omega)
        | (have := (a.sp.getD 2 0).toNat_lt; omega)
    · rename_i v hv g1 g2 g3
      f1_ld hv
      f1s at g1 g2 g3 ⊢
      simp only [f1_dec (by omega) h48, f1_min h48] at g2 g3 ⊢
      subst hNdef
      refine ⟨T.L17d6.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
        ⟨hk2s, ⟨⟨h2, ?_, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hm⟩, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi, hsi,
            h13, hax, hcx]; done)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdi, hsi,
            h13, hax, hcx]; rfl)
        | omega
        | (intro i hi1 hi2; omega)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hcx]
           apply BitVec.eq_of_toNat_eq
           simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
           omega)
        | (have := (a.sp.getD 2 0).toNat_lt; omega)

theorem blk_L17d6 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L17d6" ⟨"sbr_reset.L17d6", B.L17d6, some "sbr_reset.L17e7"⟩ := by
  info_off
  measure_hb "L17d6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, h8, hdi⟩, hm⟩, h12, h15⟩ := T.L17d6.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    simp only [B.L17d6]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · rename_i g1
      try f1s at g1 ⊢
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1e09, T.L1e09.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩,
        hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
            h13, hax, hcx]; done)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
            h13, hax, hcx]; rfl)
        | omega
        | (intro i hi1 hi2; omega)
        | (simp only [Reg64s.get64_set64, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth, ↓reduceIte]; done)
    · rename_i g1
      try f1s at g1 ⊢
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1e6b, T.L1e6b.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF, ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, 0, ?_,
        rfl, ?_, ?_⟩, hm⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
            h13, hax, hcx]; done)
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
            h13, hax, hcx]; rfl)
        | omega
        | (intro i hi1 hi2; omega)
        | (simp only [Reg64s.get64_set64, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth, ↓reduceIte]; done)

theorem blk_L1ea8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1ea8" ⟨"sbr_reset.L1ea8", B.L1ea8, some "sbr_reset.L1eb0"⟩ := by
  info_off
  measure_hb "L1ea8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, j, hdi, hj1, hjn, hfill⟩, hm⟩, h12, h15⟩ :=
      T.L1ea8.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    simp only [B.L1ea8]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    subst hNdef
    refine ⟨T.L1eb0.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_, j, ?_, hj1, hjn, hfill⟩, hm⟩, ?_, ?_⟩, by var_step⟩
    all_goals try simp only [k0N, k0A, u8, srI]
    all_goals first
      | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
          h13, hax, hcx, hdi]; done)
      | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
          h13, hax, hcx, hdi]; rfl)
      | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hdx]
         apply BitVec.eq_of_toNat_eq
         simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
         omega)

theorem blk_L1eb0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1eb0" ⟨"sbr_reset.L1eb0", B.L1eb0, some "sbr_reset.L1ec1"⟩ := by
  info_off
  measure_hb "L1eb0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, h8, j, hdi, hj1, hjn, hfill⟩, hm⟩, h12, h15⟩ :=
      T.L1eb0.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hA4 : (a.sp.getD 4 0).toNat ≤ 1 := hC.2.2.2.1
    have hst := a1_fm_store hm hfm (j := j) (by omega)
    have hsome := a1_fm_isSome hm hfm (j := j) (by omega)
    have hfill' := a1_filled_step (dk := (a.sp.getD 4 0).toNat + 1) (j := j) hfm (by omega) (by omega) hfill
    have hinc : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hinc1 : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) := hinc
    simp only [B.L1eb0]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    all_goals try simp only [h8, hdi, hax, a1_dk_val _ hA4, AddrIndex.offset64_scale2]
    · exact hsome
    · rename_i g1
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, hdi, hinc, hinc1, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, cc_nz_sub] at g1
      have hjN : j < N := by
        rcases Nat.lt_or_ge j N with h | h
        · exact h
        · exfalso
          obtain rfl : j = N := by omega
          exact g1 rfl
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1eb0, T.L1eb0.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, { st with fm := wr st.fm (2 * j) (Int.toBytes 2 (((a.sp.getD 4 0).toNat + 1 : Nat) : Int)) }, fr, hx, hsp, ?_, hF, ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_,
        ?_, ?_⟩, ?_, j + 1, ?_, ?_, ?_, hfill'⟩, ?_⟩, ?_, ?_⟩, ?_⟩)
      all_goals try simp only [AddrIndex.offset64_scale2, hdi, hax, a1_dk_val _ hA4, hinc]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
            h13, hax, hcx, hdi, h8, hinc]; done)
        | (show (wr _ _ _).length = 98
           have := h48
           try simp only [k0N, k0A, u8, srI] at this ⊢
           rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm])
        | (simp only [k0N, k0A, u8, srI]; omega)
        | omega
        | (with_reducible exact hst _)
        | (left
           simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdi,
             BitVec.toNat_ofNat]
           refine Kraken.lex_cons_lt_cons (by lex_len) ?_
           refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
           simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdi, BitVec.toNat_ofNat]
           lex_digit)
    · rename_i g1
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h8, hdi, hinc, hinc1, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, cc_nz_sub] at g1
      have hjN : j = N := by
        have := congrArg BitVec.toNat g1
        simp only [BitVec.toNat_ofNat] at this
        omega
      subst hjN
      subst hNdef
      refine ⟨T.L1ec1.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, { st with fm := wr st.fm (2 * nmOf (k2 - k0N a row) (u8 a.sp 4)) (Int.toBytes 2 (((a.sp.getD 4 0).toNat + 1 : Nat) : Int)) }, fr, hx, hsp, ?_, hF, ⟨hk2s, ⟨⟨h2, hxo, hnm, ?_⟩, ?_, ?_,
        ?_, ?_⟩, hfill'⟩, ?_⟩, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [AddrIndex.offset64_scale2, hdi, hax, a1_dk_val _ hA4, hinc]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, hsi,
            h13, hax, hcx, hdi, h8, hinc]; done)
        | (show (wr _ _ _).length = 98
           have := h48
           try simp only [k0N, k0A, u8, srI] at this ⊢
           rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm])
        | (simp only [k0N, k0A, u8, srI]; omega)
        | omega
        | (with_reducible exact hst _)
        | (left
           simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdi,
             BitVec.toNat_ofNat]
           refine Kraken.lex_cons_lt_cons (by lex_len) ?_
           refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
           simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hdi, BitVec.toNat_ofNat]
           lex_digit)

theorem blk_L1f08 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1f08" ⟨"sbr_reset.L1f08", B.L1f08, some "sbr_reset.L1f30"⟩ := by
  info_off
  measure_hb "L1f08"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨h2, hxo, hnm, hdx⟩, h13, hcx, hstep⟩, hm⟩, h12, h15⟩ :=
      T.L1f08.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hk0 := k0Of_range hr (st := u8 a.sp 0) hC.2.1
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hk0' : k0N a row < 32768 := by simp only [k0N, u8] at *; omega
    have hst := a1_fm_store0 hm hfm
    have hsum := a1_summed0 hfm h48 hk0' hstep
    have hsome := a1_fm_isSome0 hm hfm
    simp only [B.L1f08]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · exact hsome
    · rename_i g1
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, cc_c_sub, decide_eq_true_eq,
        BitVec.reduceSetWidth, a1_sw_ofNat64] at g1
      rw [show (BitVec.setWidth 32 (Int64.toBitVec 8)).toNat = 8 from rfl, BitVec.toNat_ofNat] at g1
      have hN8 : N < 8 := by omega
      subst hNdef
      refine Or.inl (Table.ofLabels_at ⟨S.L1fd5, T.L1fd5.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, { st with fm := wr st.fm (2 * 0) (Int.toBytes 2 ((k0N a row : Nat) : Int)) }, fr, hx, hsp, ?_, hF,
        ⟨hk2s, ⟨h2, hxo, hnm, ?_⟩, 0, ?_, rfl, ?_, ?_, hsum, ?_⟩, ?_⟩, ?_, ?_⟩, by edge_step⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h13, hdx, hcx,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, h13, hcx]; done)
        | (show (wr _ _ _).length = 98
           rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm])
        | omega
        | (rw [a1_k0_w _ (by omega)]; exact hst _)
        | (rw [a1_k0_w' _ (by omega)]; rfl)
        | (simp only [Reg64s.get64_set64, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth, ↓reduceIte]; done)
        | (simp only [BitVec.reduceSetWidth]; done)
        | (rw [a1_mask8' _ (by omega)])
    · rename_i g1 b1 b2
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, cc_c_sub, decide_eq_false_iff_not,
        BitVec.reduceSetWidth, a1_sw_ofNat64, Bool.not_eq_true, decide_eq_true_eq, Nat.not_lt, decide_eq_false_iff_not] at g1
      rw [show (BitVec.setWidth 32 (Int64.toBitVec 8)).toNat = 8 from rfl, BitVec.toNat_ofNat] at g1
      have hN8 : 8 ≤ N := by omega
      subst hNdef
      refine ⟨T.L1f30.mpr ⟨row, k2, hr, hk2, hle, hq, h3,
        ⟨hC, hBO, ⟨?_, ?_⟩, { st with fm := wr st.fm (2 * 0) (Int.toBytes 2 ((k0N a row : Nat) : Int)) }, fr, hx, hsp, ?_, hF,
        ⟨hk2s, ⟨h2, hxo, hnm, ?_⟩, ?_, 0, ?_, rfl, ?_, hsum, ?_⟩, ?_⟩, ?_, ?_⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h13, hdx, hcx,
        AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      all_goals try simp only [k0N, k0A, u8, srI]
      all_goals first
        | (simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15, hdx, h13, hcx]; done)
        | (show (wr _ _ _).length = 98
           rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm])
        | omega
        | (rw [a1_k0_w _ (by omega)]; exact hst _)
        | (rw [a1_k0_w' _ (by omega)]; rfl)
        | (simp only [Reg64s.get64_set64, BitVec.xor_self, BitVec.setWidth_zero, BitVec.reduceSetWidth, ↓reduceIte]; done)
        | (simp only [BitVec.reduceSetWidth]; done)
        | (rw [a1_mask8' _ (by omega)])

end Kraken.Examples.Sbr.Reset
