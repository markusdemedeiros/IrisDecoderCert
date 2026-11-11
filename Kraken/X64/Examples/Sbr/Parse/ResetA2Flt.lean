import Kraken.X64.Examples.Sbr.Parse.ResetA2Blk

/-!
# `sbr_reset`, shard A2: the float / vector blocks of `bs_freq_scale > 0`
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
theorem a2_sw32_ofInt128 (x : Int) : (BitVec.ofInt 128 x).setWidth 32 = BitVec.ofInt 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have h1 := Int.emod_nonneg x (show ((2 ^ 128 : Nat) : Int) ≠ 0 by decide)
  have h3 := Int.emod_nonneg x (show ((2 ^ 32 : Nat) : Int) ≠ 0 by decide)
  have h2 := Int.emod_emod_of_dvd x (show ((2 ^ 32 : Nat) : Int) ∣ ((2 ^ 128 : Nat) : Int) from
    ⟨2 ^ 96, by decide⟩)
  omega

omit [CodeEnv] in
/-- The low lane of a 16-byte frame load is the 4-byte slot. -/
theorem a2_lo32_slice16 (fr : List UInt8) (o : Nat) :
    (BitVec.ofInt 128 (Int.ofBytes (slice fr o 16))).setWidth 32
      = BitVec.ofInt 32 (Int.ofBytes (slice fr o 4)) := by
  rw [a2_sw32_ofInt128, BitVec.ofInt_ofBytes_take 32 4 rfl]
  simp only [slice, List.take_take]
  rfl

omit [CodeEnv] in
theorem a2_al16_fr (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) (c : BitVec 64)
    (hc : c.toNat % 16 = 0) : isAligned 16 (r - 8#64 + c) = true := by
  simp only [isAligned, beq_iff_eq] at *
  bv_omega

set_option maxRecDepth 100000 in
/-- `num_bands_1 ≤ 8`: straight to the remainder loop of the second `make_bands`. -/
theorem blk_L1cea (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1cea" ⟨"sbr_reset.L1cea", B.L1cea, some "sbr_reset.L1cf4"⟩ := by
  info_off
  measure_hb "L1cea"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h13, hle8, hax, hcx, hdx, vm, hvm, hvm', hTB, h30⟩,
      hm⟩⟩ := T.L1cea.mp hs
    clear hs
    have hl80 := fr_load hm hF (d := 0x80) (n := 16) (by omega) (by omega)
    have hal := a2_al16_fr _ hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18446744073709551488#64 (by decide)
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1cea]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      rw [hs1]
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp]
      exact hal
    case vc2 =>
      rename_i s1 hs1
      rw [hs1]
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 v hv
      rw [hs1] at hv
      simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80] at hv
      obtain rfl := Option.some.inj hv
      subst hs1 hP
      have h8 : A2.n1N e a (k0N a row) k2 ≤ 8 := hle8
      have hD : (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 = 0 := by omega
      have hlo1 : (BitVec.ofInt 128 (Int.ofBytes (slice fr (1392 - 128) 16))).setWidth 32
          = chain (A2.b1 e a (k0N a row) k2)
            (A2.fl (A2.k1Of (k0N a row) k2)) ((A2.n1N e a (k0N a row) k2 - 1) / 8 * 8) := by
        rw [hD, a2_lo32_slice16]
        exact hTB.2.1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L21e6.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, hcx,
        hdx.trans (congrArg _ hD.symm), ?_,
        by simp only [lo32, RegZmms.get_set_xmm_same]; exact hlo1, vm, hvm, hvm', hTB, h30,
        fun i h1 h2 => by have : i ≤ 0 := hD ▸ h2; omega⟩, hm⟩⟩, ?_⟩
      · rw [hD, h13]
        simp only [A2.pv, ↓reduceIte, a2_setWidth32_ofNat64, BitVec.ofInt_natCast]
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
theorem a2_cc_nc_sub {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  show (!(((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) = _
  rw [borrow_sub]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

omit [CodeEnv] in
/-- `lea -c(%rbx), %e..` with `rbx = N ≥ c` small. -/
theorem a2_lea_sub (N c : Nat) (hc : c ≤ N) (hN : N < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ 64 - c % 2 ^ 64)))
      = BitVec.ofNat 64 (N - c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
  rw [this]
  omega

omit [CodeEnv] in
/-- `mov %eax, %ecx; and $7, %ecx` after `lea -1(%rbx), %eax`. -/
theorem a2_and7 (N : Nat) (h1 : 1 ≤ N) (hN : N < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)))))) &&& BitVec.setWidth 32 7#64)
      = BitVec.ofNat 64 ((N - 1) % 8) := by
  rw [a2_lea_sub N 1 h1 hN, sw32_64, a2_setWidth32_ofNat64]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have e : (7 : Nat) = 2 ^ 3 - 1 := rfl
  rw [show 7 % 2 ^ 64 % 2 ^ 32 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

omit [CodeEnv] in
/-- `lea -2(%rbx), %edx; cmp $7, %edx; jae`: taken iff `N ≥ 9`. -/
theorem a2_cc_nb9 (N : Nat) (h2 : 2 ≤ N) (hN : N < 2 ^ 32) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ 64 - 2 % 2 ^ 64)))) - BitVec.setWidth 32 7#64)
      { cf := (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ 64 - 2 % 2 ^ 64)))) - BitVec.setWidth 32 7#64).unsigned
          != (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
          (BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ 64 - 2 % 2 ^ 64))))).unsigned
          - (BitVec.setWidth 32 7#64).unsigned, af := af, of := of })
      = decide (9 ≤ N) := by
  rw [a2_cc_nc_sub, a2_lea_sub N 2 h2 hN]
  simp only [sw32_64, a2_setWidth32_ofNat64, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  omega

omit [CodeEnv] in
/-- The frame facts `SE` survive the 8-byte store to `-0x48`. -/
theorem a2_SE_wr48 {fr : List UInt8} (hF : FrOk fr) (v : Int) {e : REnv} {a : RArgs}
    {t₀ : MachineData} {k0 k2 : Nat} (h : A2.SE fr e a t₀ k0 k2) :
    A2.SE (wr fr (rb 0x48) (Int.toBytes 8 v)) e a t₀ k0 k2 := by
  obtain ⟨⟨⟨⟨⟨h80, h88⟩, h38⟩, h50, h40⟩, h30⟩, h100⟩ := h
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [frSlot32_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x80) (by omega)
      (by omega) (by omega)]; exact h80
  · rw [frSlot32_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x88) (by omega)
      (by omega) (by omega)]; exact h88
  · rw [frSlot32_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x38) (by omega)
      (by omega) (by omega)]; exact h38
  · rw [frSlot32_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x50) (by omega)
      (by omega) (by omega)]; exact h50
  · rw [frSlot64_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x40) (by omega)
      (by omega) (by omega)]; exact h40
  · rw [frSlot64_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x30) (by omega)
      (by omega) (by omega)]; exact h30
  · rw [frSlot32_wr_other hF (d := 0x48) (n := 8) (by omega) (by omega) _ (d' := 0x100) (by omega)
      (by omega) (by omega)]; exact h100

set_option maxRecDepth 100000 in
/-- `-0x48 = num_bands_0`; the unrolled loop (`num_bands_0 ≥ 9`) or the remainder loop. -/
theorem blk_L173b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L173b" ⟨"sbr_reset.L173b", B.L173b, some "sbr_reset.L1762"⟩ := by
  info_off
  measure_hb "L173b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h15, h13, h14, hSE, hN0, hbx, hlo0⟩, hm⟩⟩ := T.L173b.mp hs
    clear hs
    have st48 := fr_store hm hF (d := 0x48) (n := 8) (by omega) (by omega)
    have hl48 := fr_load hm hF (d := 0x48) (n := 8) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x48) (n := 8) (by simp only [rb]; omega) v
    have e48 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by bv_omega
    have e100 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551360#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x100 := by bv_omega
    have hal := a2_al16_fr _ hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18446744073709551360#64 (by decide)
    have hN : 2 ≤ A2.n0N e a (k0N a row) k2 ∧ A2.n0N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 0 < A2.n0I e a (k0N a row) k2 := hN0.1
      have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
      have h3 : (A2.n0I e a (k0N a row) k2).toNat % 2 = 0 := hN0.2.2
      show 2 ≤ (A2.n0I e a (k0N a row) k2).toNat ∧ (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L173b]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e48, hl48, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1 b hc
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e48, hbx] at hc ⊢
      rw [a2_cc_nb9 _ hN.1 (by omega)] at hc
      have h9 : 9 ≤ A2.n0N e a (k0N a row) k2 := of_decide_eq_true hc
      subst hP
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1830.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        wr fr (rb 0x48) (Int.toBytes 8 (BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2)).toInt), hx,
        hsp, hfm, hF1 _, ⟨hk2v, hk1v, ?_, ?_, ⟨a2_SE_wr48 hF _ hSE, ?_⟩, hN0, h9, ?_, ?_, hlo0⟩,
        st48 _⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h13
      · exact h14
      · rw [frSlot64_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
      · exact a2_lea_sub _ 1 (by omega) (by omega)
      · exact a2_and7 _ (by omega) (by omega)
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)
    case vc3 =>
      rename_i s1 hs1 b hc b'
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp]
      exact hal
    case vc4 =>
      rename_i s1 hs1 b hc b'
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e48, e100, hbx]
      rw [fr_load (st48 _) (hF1 _) (d := 0x100) (n := 16) (by omega) (by omega)]
      rfl
    case vc5 =>
      rename_i s1 hs1 b hc b' v hv
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e48, e100, hbx] at hc hv ⊢
      rw [a2_cc_nb9 _ hN.1 (by omega)] at hc
      have h8' : ¬ 9 ≤ A2.n0N e a (k0N a row) k2 := of_decide_eq_false hc
      have h8 : A2.n0N e a (k0N a row) k2 ≤ 8 := by omega
      rw [fr_load (st48 _) (hF1 _) (d := 0x100) (n := 16) (by omega) (by omega)] at hv
      obtain rfl := Option.some.inj hv
      have hD : (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 = 0 := by omega
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1908.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        wr fr (rb 0x48) (Int.toBytes 8 (BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2)).toInt), hx,
        hsp, hfm, hF1 _, ⟨hk2v, hk1v, ⟨a2_SE_wr48 hF _ hSE, ?_⟩, hN0, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        fun i h1 h2 => by have : i ≤ 0 := hD ▸ h2; omega⟩, st48 _⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · rw [frSlot64_wr_same hF (by omega) (by omega), BitVec.ofInt_toInt]
      · exact h14
      · exact a2_lea_sub _ 1 (by omega) (by omega)
      · exact a2_and7 _ (by omega) (by omega)
      · simp only [lo32, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq, not_false_eq_true]
        exact hlo0
      · rw [hD, BitVec.xor_self]; rfl
      · rw [hD, h13]
        simp only [A2.pv, ↓reduceIte, a2_setWidth32_ofNat64, BitVec.ofInt_natCast]
      · simp only [lo32, RegZmms.get_set_xmm_same]
        rw [hD, a2_lo32_slice16, slice_wr_other hF (by simp only [rb]; omega) _
          (by simp only [rb]; omega)]
        exact hSE.2
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)


omit [CodeEnv] in
theorem a2_cc_l_ge2 (N : Nat) (h2 : 2 ≤ N) (hN : N < 2 ^ 31) (cf af : Bool) :
    CondCode.l.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 2#64)
      { cf := cf, af := af,
        of := (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 2#64).signed
          != (BitVec.setWidth 32 (BitVec.ofNat 64 N)).signed - (BitVec.setWidth 32 2#64).signed })
      = false := by
  have e1 : BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 2#64
      = BitVec.ofNat 32 (N - 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have e2 : BitVec.setWidth 32 2#64 = BitVec.ofNat 32 2 := rfl
  rw [e1, a2_setWidth32_ofNat64, e2]
  simp only [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result,
    BitVec.signed_eq]
  rw [a2_toInt_ofNat32 (by omega), a2_toInt_ofNat32 (by omega), a2_toInt_ofNat32 (by omega)]
  have : (BitVec.ofNat 32 (N - 2)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [this]
  simp
  omega

omit [CodeEnv] in
/-- `lea -1(,%r15,2), %eax` with `2 * low32(r15) = N`. -/
theorem a2_lea_r15 (R : BitVec 64) (N : Nat) (h : R.setWidth 32 + R.setWidth 32 = BitVec.ofNat 32 N)
    (h1 : 1 ≤ N) (hN : N < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (R * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)))
      = BitVec.ofNat 64 (N - 1) := by
  have e : BitVec.setWidth 32 (R * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64))
      = R.setWidth 32 + R.setWidth 32 + 0xffffffff#32 := by
    rw [BitVec.setWidth_add, BitVec.setWidth_mul]
    · have : (2#64).setWidth 32 = 2#32 := rfl
      have h2 : (BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)).setWidth 32 = 0xffffffff#32 := rfl
      rw [this, h2, BitVec.mul_two]
    all_goals decide
  rw [e, h]
  have e2 : BitVec.ofNat 32 N + 0xffffffff#32 = BitVec.ofNat 32 (N - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have m1 : N % 2 ^ 32 = N := Nat.mod_eq_of_lt hN
    have m2 : (N - 1) % 2 ^ 32 = N - 1 := Nat.mod_eq_of_lt (by omega)
    have m3 : (4294967295 : Nat) % 2 ^ 32 = 4294967295 := rfl
    rw [m1, m2, m3]
    have : N + 4294967295 = (N - 1) + 2 ^ 32 := by omega
    rw [this, Nat.add_mod_right, m2]
  rw [e2, a2_setWidth64_ofNat32 (by omega)]

omit [CodeEnv] in
theorem a2_sw_ofNat (M : Nat) (hM : M < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 M)) = BitVec.ofNat 64 M := by
  rw [a2_setWidth32_ofNat64, a2_setWidth64_ofNat32 hM]

omit [CodeEnv] in
theorem a2_and7' (Y : BitVec 64) (M : Nat) (hY : Y = BitVec.ofNat 64 M) (hM : M < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 Y)))) &&& BitVec.setWidth 32 7#64)
      = BitVec.ofNat 64 (M % 8) := by
  rw [hY, a2_sw_ofNat M hM, a2_sw_ofNat M hM, a2_setWidth32_ofNat64]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show 7 % 2 ^ 64 % 2 ^ 32 = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

omit [CodeEnv] in
/-- `TB` after the stores of `nb1` to `-0x38` and `nb1 - 1` to `-0x100`; `-0x30` kept. -/
theorem a2_TB_wr {fr : List UInt8} (hF : FrOk fr) {t₀ : MachineData} {k1 n0 n1 : Nat} {vm : Int}
    (hTA : A2.TA fr t₀ n0 vm) (h80 : frSlot32 fr 0x80 = A2.fl k1) (h30 : frSlot64 fr 0x30 = arg1 t₀)
    (v1 v2 : Int) (hv1 : BitVec.ofInt 64 v1 = BitVec.ofNat 64 n1)
    (hv2 : BitVec.ofInt 64 v2 = BitVec.ofNat 64 (n1 - 1)) :
    A2.TB (wr (wr fr (rb 0x38) (Int.toBytes 8 v1)) (rb 0x100) (Int.toBytes 8 v2)) t₀ k1 n0 n1 vm
    ∧ frSlot64 (wr (wr fr (rb 0x38) (Int.toBytes 8 v1)) (rb 0x100) (Int.toBytes 8 v2)) 0x30
      = arg1 t₀ := by
  have hF1 := fr_wr_len hF (o := rb 0x38) (n := 8) (by simp only [rb]; omega) v1
  obtain ⟨h40, h48, h88, h50⟩ := hTA
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [frSlot64_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x40) (by omega)
      (by omega) (by omega), frSlot64_wr_other hF (d := 0x38) (n := 8) (by omega) (by omega) _
      (d' := 0x40) (by omega) (by omega) (by omega)]; exact h40
  · rw [frSlot64_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x48) (by omega)
      (by omega) (by omega), frSlot64_wr_other hF (d := 0x38) (n := 8) (by omega) (by omega) _
      (d' := 0x48) (by omega) (by omega) (by omega)]; exact h48
  · rw [frSlot64_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x88) (by omega)
      (by omega) (by omega), frSlot64_wr_other hF (d := 0x38) (n := 8) (by omega) (by omega) _
      (d' := 0x88) (by omega) (by omega) (by omega)]; exact h88
  · rw [frSlot32_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x50) (by omega)
      (by omega) (by omega), frSlot32_wr_other hF (d := 0x38) (n := 8) (by omega) (by omega) _
      (d' := 0x50) (by omega) (by omega) (by omega)]; exact h50
  · rw [frSlot32_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x80) (by omega)
      (by omega) (by omega), frSlot32_wr_other hF (d := 0x38) (n := 8) (by omega) (by omega) _
      (d' := 0x80) (by omega) (by omega) (by omega)]; exact h80
  · rw [frSlot64_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x38) (by omega)
      (by omega) (by omega), frSlot64_wr_same hF (by omega) (by omega)]; exact hv1
  · rw [frSlot64_wr_same hF1 (by omega) (by omega)]; exact hv2
  · rw [frSlot64_wr_other hF1 (d := 0x100) (n := 8) (by omega) (by omega) _ (d' := 0x30) (by omega)
      (by omega) (by omega), frSlot64_wr_other hF (d := 0x38) (n := 8) (by omega) (by omega) _
      (d' := 0x30) (by omega) (by omega) (by omega)]; exact h30

omit [CodeEnv] in
/-- An 8-byte frame write above the array at `o` keeps `Inc`. -/
theorem a2_inc_wr8 {fr : List UInt8} {p o n : Nat} {v0 v1 : Int} (v : Int) (h : p + 8 ≤ fr.length)
    (hd : o + 2 * n + 2 ≤ p) (hI : A2.Inc fr o n v0 v1) :
    A2.Inc (wr fr p (Int.toBytes 8 v)) o n v0 v1 := by
  have hl : (Int.toBytes 8 v).length = 8 := Int.toBytes_length 8 v
  have key : ∀ i, i ≤ n → A2.fv (wr fr p (Int.toBytes 8 v)) o i = A2.fv fr o i := by
    intro i hi
    unfold A2.fv
    rw [slice_wr_disj (by rw [hl]; omega) (by rw [hl]; omega)]
  obtain ⟨h0, h1, h2⟩ := hI
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [key 0 (by omega)]; exact h0
  · rw [key n (by omega)]; exact h1
  · rw [key i (by omega), key (i + 1) (by omega)]; exact h2 i hi

set_option maxRecDepth 100000 in
/-- `num_bands_1` stored; the unrolled loop (`≥ 9`) or straight to the remainder loop. -/
theorem blk_L1cb9 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1cb9" ⟨"sbr_reset.L1cb9", B.L1cb9, some "sbr_reset.L1cea"⟩ := by
  info_off
  measure_hb "L1cb9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h12, h30, h13, h14, h15, hbx, h80, hlo0, vm, hvm, hvm', hTA,
        -⟩, hm⟩⟩ := T.L1cb9.mp hs
    clear hs
    have st38 := fr_store hm hF (d := 0x38) (n := 8) (by omega) (by omega)
    have hl38 := fr_load hm hF (d := 0x38) (n := 8) (by omega) (by omega)
    have hF1 := fun v => fr_wr_len hF (o := rb 0x38) (n := 8) (by simp only [rb]; omega) v
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    have e100 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551360#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x100 := by bv_omega
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hNa : 2 ≤ A2.n1N e a (k0N a row) k2 := hN.1
    have hNb : A2.n1N e a (k0N a row) k2 ≤ 48 := hN.2
    have hN32 : A2.n1N e a (k0N a row) k2 < 2 ^ 32 := Nat.lt_of_le_of_lt hNb (by decide)
    have hN32' : A2.n1N e a (k0N a row) k2 - 1 < 2 ^ 32 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN32
    have hN1' : 1 ≤ A2.n1N e a (k0N a row) k2 := Nat.le_trans (by decide) hNa
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1cb9]
    vcgen
    case vc1 =>
      rename_i s1 hs1 hc
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hbx] at hc
      rw [a2_cc_l_ge2 _ hN.1 (by omega)] at hc
      exact absurd hc (by decide)
    case vc2 =>
      rename_i s1 hs1 hc
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e38, hl38, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 hc hc'
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e38, e100, Option.isSome_some]
      rw [fr_load (st38 _) (hF1 _) (d := 0x100) (n := 8) (by omega) (by omega)]
      rfl
    case vc4 =>
      rename_i s1 hs1 hc hc' hc''
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, e100, hbx] at hc'' ⊢
      rw [a2_cc_nb9 (A2.n1N e a (k0N a row) k2) hNa hN32] at hc''
      have h9 : 9 ≤ A2.n1N e a (k0N a row) k2 := of_decide_eq_true hc''
      have hY := a2_lea_r15 _ (A2.n1N e a (k0N a row) k2) h15 hN1' hN32
      have hrax : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
          (s1.regs.get64 .r15 * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)))))
          = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2 - 1) := by
        rw [hY, a2_sw_ofNat _ hN32']
      obtain ⟨hTB, h30'⟩ := a2_TB_wr hF hTA h80 h30
        (BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2)).toInt _ BitVec.ofInt_toInt
        (BitVec.ofInt_toInt.trans hrax)
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2112.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        wr (wr fr (rb 0x38) (Int.toBytes 8 (BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2)).toInt))
          (rb 0x100) (Int.toBytes 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
            (BitVec.setWidth 32 (s1.regs.get64 .r15 * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)))))).toInt),
        hx,
        hsp, hfm, fr_wr_len (hF1 _) (by simp only [rb]; omega) _, ⟨hk2v, hk1v, hlt,
        a2_inc_wr8 _ (by rw [hF1 _]; simp only [rb]; omega) (by simp only [rb]; omega)
          (a2_inc_wr8 _ (by rw [hF]; simp only [rb]; omega) (by simp only [rb]; omega) hInc), hN0, hN1,
        ?_, ?_, hlo0, ?_, h9, ?_, ?_, vm, hvm, hvm', hTB, h30'⟩,
        fr_store (st38 _) (hF1 _) (d := 0x100) (n := 8) (by omega) (by omega) _⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · exact h13
      · exact hrax
      · exact a2_and7' _ _ hY hN32'
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)
    case vc5 =>
      rename_i s1 hs1 hc hc' hc'' hc'''
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, e100, hbx] at hc'' hc''' ⊢
      first
        | rw [a2_cc_nb9 (A2.n1N e a (k0N a row) k2) hNa hN32] at hc''
        | rw [a2_cc_nb9 (A2.n1N e a (k0N a row) k2) hNa hN32] at hc'''
      have h8 : ¬ 9 ≤ A2.n1N e a (k0N a row) k2 := by
        first | exact of_decide_eq_false hc'' | exact of_decide_eq_false hc'''
      have h8' : A2.n1N e a (k0N a row) k2 ≤ 8 := by omega
      have hY := a2_lea_r15 _ (A2.n1N e a (k0N a row) k2) h15 hN1' hN32
      have hrax : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
          (s1.regs.get64 .r15 * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)))))
          = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2 - 1) := by
        rw [hY, a2_sw_ofNat _ hN32']
      obtain ⟨hTB, h30'⟩ := a2_TB_wr hF hTA h80 h30
        (BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2)).toInt _ BitVec.ofInt_toInt
        (BitVec.ofInt_toInt.trans hrax)
      have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      refine ⟨T.L1cea.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st,
        wr (wr fr (rb 0x38) (Int.toBytes 8 (BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2)).toInt))
          (rb 0x100) (Int.toBytes 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
            (BitVec.setWidth 32 (s1.regs.get64 .r15 * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64)))))).toInt),
        hx,
        hsp, hfm, fr_wr_len (hF1 _) (by simp only [rb]; omega) _, ⟨hk2v, hk1v, hlt,
        a2_inc_wr8 _ (by rw [hF1 _]; simp only [rb]; omega) (by simp only [rb]; omega)
          (a2_inc_wr8 _ (by rw [hF]; simp only [rb]; omega) (by simp only [rb]; omega) hInc), hN0, hN1,
        ?_, ?_, hlo0, ?_, h8', ?_, ?_, ?_, vm, hvm, hvm', hTB, h30'⟩,
        fr_store (st38 _) (hF1 _) (d := 0x100) (n := 8) (by omega) (by omega) _⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · exact h13
      · exact hrax
      · exact a2_and7' _ _ hY hN32'
      · rw [BitVec.xor_self]; rfl
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
/-- `and $0x7ffffff8, %esi`: round `M` down to a multiple of 8. -/
theorem a2_and8 (M : Nat) (h : M < 48) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 M) &&& BitVec.setWidth 32 2147483640#64)
      = BitVec.ofNat 64 (M / 8 * 8) := by
  have key : ∀ m : Fin 48, BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m.val)
      &&& BitVec.setWidth 32 2147483640#64) = BitVec.ofNat 64 (m.val / 8 * 8) := by decide
  exact key ⟨M, h⟩

set_option maxRecDepth 100000 in
/-- Entry of the unrolled loop of the second `make_bands`. -/
theorem blk_L2112 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2112" ⟨"sbr_reset.L2112", B.L2112, some "sbr_reset.L2130"⟩ := by
  info_off
  measure_hb "L2112"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, h14, hlo0, h13, h9, hax, hcx, vm, hvm, hvm', hTB, h30⟩,
      hm⟩⟩ := T.L2112.mp hs
    clear hs
    have hl80 := fr_load hm hF (d := 0x80) (n := 16) (by omega) (by omega)
    have hal := a2_al16_fr _ hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18446744073709551488#64 (by decide)
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2112]
    vcgen
    case vc1 =>
      rename_i s1 hs1 af1 af2
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp]
      exact hal
    case vc2 =>
      rename_i s1 hs1 af1 af2
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 af1 af2 v hv
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80] at hv ⊢
      obtain rfl := Option.some.inj hv
      have hNb : A2.n1N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
        show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
        omega
      have h9' : 9 ≤ A2.n1N e a (k0N a row) k2 := h9
      have hM : A2.n1N e a (k0N a row) k2 - 1 < 48 := by omega
      have hD : 0 + 8 ≤ (A2.n1N e a (k0N a row) k2 - 1) / 8 * 8 := by omega
      refine ⟨T.L2130.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, ?_, hlo0, h9, ?_, ?_, vm, hvm, hvm', hTB, h30,
        0, ?_, rfl, hD, ?_,
        by simp only [lo32, RegZmms.get_set_xmm_same]; rw [a2_lo32_slice16]; exact hTB.2.1,
        fun i h1 h2 => by omega⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h14
      · rw [hax]; exact a2_and8 _ hM
      · exact hcx
      · rw [BitVec.xor_self]; rfl
      · rw [h13]
        simp only [A2.pv, ↓reduceIte, a2_setWidth32_ofNat64, BitVec.ofInt_natCast]
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
set_option maxRecDepth 100000 in
/-- Entry of the unrolled loop of the first `make_bands`. -/
theorem blk_L1830 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1830" ⟨"sbr_reset.L1830", B.L1830, some "sbr_reset.L1850"⟩ := by
  info_off
  measure_hb "L1830"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, h13, h14, hSF, hN0, h9, hax, hcx, hlo0⟩,
      hm⟩⟩ := T.L1830.mp hs
    clear hs
    have hl80 := fr_load hm hF (d := 0x100) (n := 16) (by omega) (by omega)
    have hal := a2_al16_fr _ hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1 18446744073709551360#64 (by decide)
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551360#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x100 := by bv_omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1830]
    vcgen
    case vc1 =>
      rename_i s1 hs1 af1 af2
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp]
      exact hal
    case vc2 =>
      rename_i s1 hs1 af1 af2
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 af1 af2 v hv
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, hrbp, e80, hl80] at hv ⊢
      obtain rfl := Option.some.inj hv
      have hNb : A2.n0N e a (k0N a row) k2 ≤ 48 := by
        have h2 : A2.n0I e a (k0N a row) k2 ≤ 48 := hN0.2.1
        show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
        omega
      have h9' : 9 ≤ A2.n0N e a (k0N a row) k2 := h9
      have hM : A2.n0N e a (k0N a row) k2 - 1 < 48 := by omega
      have hD : 0 + 8 ≤ (A2.n0N e a (k0N a row) k2 - 1) / 8 * 8 := by omega
      refine ⟨T.L1850.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, h9, ?_, ?_, ?_, ?_, hlo0,
        0, ?_, rfl, hD, ?_,
        by simp only [lo32, RegZmms.get_set_xmm_same]; rw [a2_lo32_slice16]; exact hSF.1.2,
        fun i h1 h2 => by omega⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h14
      · exact hax
      · exact hcx
      · rw [hax, a2_sw_ofNat _ (by omega)]; exact a2_and8 _ hM
      · rw [BitVec.xor_self]; rfl
      · rw [h13]
        simp only [A2.pv, ↓reduceIte, a2_setWidth32_ofNat64, BitVec.ofInt_natCast]
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
/-- `lea -c(,%rdx,2), %rdx; add %rbp, %rdx`. -/
theorem a2_lea2x (r : BitVec 64) (D c : Nat) (hc : c < 2 ^ 64) :
    r + (BitVec.ofNat 64 D * 2#64 + BitVec.ofNat 64 (2 ^ 64 - c % 2 ^ 64))
      = r - BitVec.ofNat 64 c + BitVec.ofNat 64 (2 * D) := by
  have h1 : BitVec.ofNat 64 (2 * D) = BitVec.ofNat 64 D * 2#64 := by
    rw [Nat.mul_comm, BitVec.ofNat_mul]
  have h2 : BitVec.ofNat 64 (2 ^ 64 - c % 2 ^ 64) = - BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
  rw [h1, h2]; bv_omega

set_option maxRecDepth 100000 in
/-- Entry of the remainder loop of the first `make_bands`. -/
theorem blk_L1908 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1908" ⟨"sbr_reset.L1908", B.L1908, some "sbr_reset.L1920"⟩ := by
  info_off
  measure_hb "L1908"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h14, hax, hcx, hlo0, hdx, h13, hlo1, hMB⟩, hm⟩⟩ := T.L1908.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1908]
    vcgen
    rename_i s1 hs1 af1
    subst hs1 hP
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdx]
    have hNb : 1 ≤ A2.n0N e a (k0N a row) k2 ∧ A2.n0N e a (k0N a row) k2 % 2 = 0 := by
      have h1 : 0 < A2.n0I e a (k0N a row) k2 := hN0.1
      have h2 : A2.n0N e a (k0N a row) k2 % 2 = 0 := hN0.2.2
      refine ⟨?_, h2⟩
      show 1 ≤ (A2.n0I e a (k0N a row) k2).toNat
      omega
    have hlt : 0 < (A2.n0N e a (k0N a row) k2 - 1) % 8 := by omega
    refine ⟨T.L1920.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
      hx, hsp, hfm, hF, ⟨hk2v, hk1v, hSF, hN0, ?_, ?_, ?_, hlo0, ?_, ?_, 0, ?_, hlt,
      by rw [Nat.add_zero]; simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]; exact h13, by rw [Nat.add_zero]; exact hlo1,
      by rw [Nat.add_zero]; exact hMB⟩, hm⟩⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · exact hrsp
    · exact hrbp
    · exact h14
    · exact hax
    · exact hcx
    · rw [hrbp]; bv_omega
    · rw [hrbp]; exact a2_lea2x _ _ 366 (by decide)
    · rw [BitVec.xor_self]; rfl
    · rw [← hn]; simp only [lex_var]
      exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)
set_option maxRecDepth 100000 in
/-- Entry of the remainder loop of the second `make_bands`. -/
theorem blk_L21e6 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L21e6" ⟨"sbr_reset.L21e6", B.L21e6, some "sbr_reset.L2200"⟩ := by
  info_off
  measure_hb "L21e6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt0, hInc, hN0, hN1, h15, h14, hlo0, hcx, hdx, h13, hlo1, vm, hvm, hvm', hTB, h30, hMB⟩, hm⟩⟩ := T.L21e6.mp hs
    clear hs
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L21e6]
    vcgen
    rename_i s1 hs1 af1
    subst hs1 hP
    simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdx]
    have hNb : 1 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 % 2 = 0 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1N e a (k0N a row) k2 % 2 = 0 := hN1.2.2
      refine ⟨?_, h2⟩
      show 1 ≤ (A2.n1I e a (k0N a row) k2).toNat
      omega
    have hlt : 0 < (A2.n1N e a (k0N a row) k2 - 1) % 8 := by omega
    refine ⟨T.L2200.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
      hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt0, hInc, hN0, hN1, ?_, ?_, hlo0, ?_, ?_, 0, ?_, hlt,
      by rw [Nat.add_zero]; simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]; exact h13, by rw [Nat.add_zero]; exact hlo1,
      vm, hvm, hvm', hTB, h30, by rw [Nat.add_zero]; exact hMB⟩, hm⟩⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · exact hrsp
    · exact hrbp
    · exact h15
    · exact h14
    · exact hcx
    · rw [hrbp]; exact a2_lea2x _ _ 238 (by decide)
    · rw [BitVec.xor_self]; rfl
    · rw [← hn]; simp only [lex_var]
      exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
/-- `cmp $5, %r13d; jae` with `r13 = N` small. -/
theorem a2_cc_nb5 (N : Nat) (hN : N < 2 ^ 32) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 5#64)
      { cf := (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 5#64).unsigned
          != (BitVec.setWidth 32 (BitVec.ofNat 64 N)).unsigned - (BitVec.setWidth 32 5#64).unsigned,
        af := af, of := of })
      = decide (5 ≤ N) := by
  rw [a2_cc_nc_sub]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  apply decide_eq_decide.mpr
  omega

set_option maxRecDepth 100000 in
/-- After the second `make_bands`: `num_bands_1 ≥ 5` or straight to the scalar prefix loop. -/
theorem blk_L2230 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2230" ⟨"sbr_reset.L2230", B.L2230, some "sbr_reset.L2252"⟩ := by
  info_off
  measure_hb "L2230"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, vm, hvm, hvm', hTB, h30⟩, hm⟩⟩ := T.L2230.mp hs
    clear hs
    have hlee := fr_load hm hF (d := 0xee) (n := 2) (by omega) (by omega)
    have hl38 := fr_load hm hF (d := 0x38) (n := 8) (by omega) (by omega)
    have hl30 := fr_load hm hF (d := 0x30) (n := 8) (by omega) (by omega)
    have eee : t₀.regs.get64 .rsp - 8#64 + 18446744073709551378#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0xee := by bv_omega
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    have e30 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by bv_omega
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hN32 : A2.n1N e a (k0N a row) k2 < 2 ^ 32 := Nat.lt_of_le_of_lt hN.2 (by decide)
    have h38 : BitVec.ofInt 64 (Int.ofBytes (slice fr (1392 - 56) 8))
        = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2) := hTB.2.2.1
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr (1392 - 48) 8)) = arg1 t₀ := h30
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2230]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, eee, hlee, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1 v1 hv1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e38, hl38, Option.isSome_some]
    case vc3 =>
      rename_i s1 hs1 v1 hv1 v2 hv2 hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, eee, e38, hlee, hl38] at hv1 hv2 hc ⊢
      obtain rfl := Option.some.inj hv2
      rw [h38, a2_cc_nb5 _ hN32] at hc
      have h5 : 5 ≤ A2.n1N e a (k0N a row) k2 := of_decide_eq_true hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2252.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, vm, hvm, hvm', hTB, h30,
        h5⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h38
      · rw [h38]; exact a2_sw_ofNat _ hN32
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)
    case vc4 =>
      rename_i s1 hs1 v1 hv1 v2 hv2 hc
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, Option.isSome_some]
    case vc5 =>
      rename_i s1 hs1 v1 hv1 v2 hv2 hc v3 hv3
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, eee, e38, e30, hlee, hl38, hl30] at hv1 hv2 hv3 hc ⊢
      obtain rfl := Option.some.inj hv2
      obtain rfl := Option.some.inj hv3
      rw [h38, a2_cc_nb5 _ hN32] at hc
      have h5 : ¬ 5 ≤ A2.n1N e a (k0N a row) k2 := of_decide_eq_false hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2340.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        1, ?_, Nat.le_refl 1, Nat.lt_of_lt_of_le (by decide) hN.1⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h30'
      · exact h38
      · rw [h38]; exact a2_sw_ofNat _ hN32
      · rfl
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)

omit [CodeEnv] in
/-- `cmp $c, %r13d; jae` with `r13 = N` small. -/
theorem a2_cc_nbc (N c : Nat) (hN : N < 2 ^ 32) (hc : c < 2 ^ 32) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 (BitVec.ofNat 64 c))
      { cf := (BitVec.setWidth 32 (BitVec.ofNat 64 N) - BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned
          != (BitVec.setWidth 32 (BitVec.ofNat 64 N)).unsigned
            - (BitVec.setWidth 32 (BitVec.ofNat 64 c)).unsigned,
        af := af, of := of })
      = decide (c ≤ N) := by
  rw [a2_cc_nc_sub, a2_setWidth32_ofNat64, a2_setWidth32_ofNat64, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hc]

omit [CodeEnv] in
theorem a2_dec64 (N : Nat) (h1 : 1 ≤ N) (hN : N < 2 ^ 64) :
    BitVec.ofNat 64 N + BitVec.ofNat 64 (2 ^ 64 - 1 % 2 ^ 64) = BitVec.ofNat 64 (N - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN),
    show 1 % 2 ^ 64 = 1 from rfl, Nat.mod_eq_of_lt (show 2 ^ 64 - 1 < 2 ^ 64 by decide)]
  have e : N + (2 ^ 64 - 1) = (N - 1) + 1 * 2 ^ 64 := by omega
  rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN)]

set_option maxRecDepth 100000 in
/-- `num_bands_1 ≥ 17`: the 16-wide prefix loop, else the 4-wide one. -/
theorem blk_L2252 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2252" ⟨"sbr_reset.L2252", B.L2252, some "sbr_reset.L2267"⟩ := by
  info_off
  measure_hb "L2252"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h13, hax, vm, hvm, hvm', hTB, h30, h5⟩, hm⟩⟩ :=
      T.L2252.mp hs
    clear hs
    have hl30 := fr_load hm hF (d := 0x30) (n := 8) (by omega) (by omega)
    have e30 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by bv_omega
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hN32 : A2.n1N e a (k0N a row) k2 < 2 ^ 32 := Nat.lt_of_le_of_lt hN.2 (by decide)
    have hN64 : A2.n1N e a (k0N a row) k2 < 2 ^ 64 := Nat.lt_of_le_of_lt hN.2 (by decide)
    have h5' : 5 ≤ A2.n1N e a (k0N a row) k2 := h5
    have hN1' : 1 ≤ A2.n1N e a (k0N a row) k2 := Nat.le_trans (by decide) h5'
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr (1392 - 48) 8)) = arg1 t₀ := h30
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2252]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1 v hv hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, h13, hax] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      rw [a2_cc_nbc _ 17 hN32 (by decide)] at hc
      have h17 : 17 ≤ A2.n1N e a (k0N a row) k2 := of_decide_eq_true hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2267.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        h17, ?_⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h30'
      · exact h13
      · exact hax
      · exact a2_dec64 _ hN1' hN64
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)
    case vc3 =>
      rename_i s1 hs1 v hv hc af
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, e30, hl30, h13, hax] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L22fa.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        ?_, 0, ?_, rfl, by rw [Nat.zero_add]; exact Nat.le_sub_of_add_le h5'⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h30'
      · exact h13
      · exact hax
      · exact a2_dec64 _ hN1' hN64
      · rw [BitVec.xor_self]; rfl
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)


omit [CodeEnv] in
theorem a2_beq_ofNat (N M : Nat) (hN : N < 2 ^ 64) (hM : M < 2 ^ 64) :
    (BitVec.ofNat 64 N == BitVec.ofNat 64 M) = decide (N = M) := by
  by_cases h : N = M
  · subst h; simp
  · have h' : BitVec.ofNat 64 N ≠ BitVec.ofNat 64 M := by
      intro he
      have := congrArg BitVec.toNat he
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hM] at this
      exact h this
    simp [h, h']

omit [CodeEnv] in
/-- `rbp + 2 c - 0xee` is the frame slot `rbp - (0xee - 2 c)`. -/
theorem a2_idx_ee (r : BitVec 64) (c : Nat) (hc : 2 * c ≤ 238) :
    r + BitVec.ofNat 64 c * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 238 % 2 ^ 64)
      = r - BitVec.ofNat 64 (238 - 2 * c) := by
  have hy : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hz : (BitVec.ofNat 64 (238 - 2 * c)).toNat = 238 - 2 * c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hw : BitVec.ofNat 64 (2 ^ 64 - 238 % 2 ^ 64) = 18446744073709551378#64 := rfl
  rw [hw]
  generalize BitVec.ofNat 64 c = y at hy ⊢
  generalize BitVec.ofNat 64 (238 - 2 * c) = z at hz ⊢
  bv_omega

set_option maxRecDepth 100000 in
/-- The scalar `min` loop over `vk1[1 ..]`. -/
theorem blk_L2340 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2340" ⟨"sbr_reset.L2340", B.L2340, some "sbr_reset.L2357"⟩ := by
  info_off
  measure_hb "L2340"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hvm, hvm', hTB, h30,
        c, hcx, hc1, hcN⟩, hm⟩⟩ := T.L2340.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hcN' : c < A2.n1N e a (k0N a row) k2 := hcN
    have hc48 : c < 48 := Nat.lt_of_lt_of_le hcN' hN.2
    have hN64 : A2.n1N e a (k0N a row) k2 < 2 ^ 64 := Nat.lt_of_le_of_lt hN.2 (by decide)
    have hl := fr_load hm hF (d := 238 - 2 * c) (n := 2) (by omega) (by omega)
    have ea := a2_idx_ee (t₀.regs.get64 .rsp - 8#64) c (by omega)
    have hinc : BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) := (BitVec.ofNat_add c 1).symm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2340]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hcx, ea, hl, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1 v hv hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hcx, ea, hl, hax, hinc, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      rw [a2_beq_ofNat _ _ hN64 (by omega)] at hc
      have hne : ¬ (A2.n1N e a (k0N a row) k2 = c + 1) := by
        intro h
        have hd : decide (A2.n1N e a (k0N a row) k2 = c + 1) = true := decide_eq_true h
        simp only [hd, Bool.not_true, Bool.false_eq_true] at hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2340.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        c + 1, ?_, Nat.le_add_left 1 c,
        Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hcN') (fun h => hne h.symm)⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact hax
      · left; rw [← hn]; simp only [lex_var]
        simp only [VD.L2340, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hax, hcx]
        apply Kraken.lex_cons_lt_cons (by lex_len)
        apply Kraken.lex_cons_lt_of_lt (by lex_len)
        simp only [BitVec.toNat_ofNat]
        have h1 : (c + 1) % 2 ^ 64 = c + 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : c % 2 ^ 64 = c := Nat.mod_eq_of_lt (by omega)
        have h3 : A2.n1N e a (k0N a row) k2 % 2 ^ 64 = A2.n1N e a (k0N a row) k2 :=
          Nat.mod_eq_of_lt hN64
        rw [h1, h2, h3]
        have h4 : c + 1 < A2.n1N e a (k0N a row) k2 :=
          Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hcN') (fun h => hne h.symm)
        rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN64),
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hN64)]
        omega
    case vc3 =>
      rename_i s1 hs1 v hv hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hcx, ea, hl, hax, hinc, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      refine ⟨T.L2357.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30⟩,
        hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact hax
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)


omit [CodeEnv] in
/-- `and $-4, %rdx`. -/
theorem a2_and4 (M : Nat) (h : M < 48) :
    BitVec.ofNat 64 M &&& BitVec.setWidth 64 (BitVec.ofNat 64 (2 ^ 64 - 4 % 2 ^ 64))
      = BitVec.ofNat 64 (M / 4 * 4) := by
  have key : ∀ m : Fin 48, BitVec.ofNat 64 m.val &&& BitVec.setWidth 64 (BitVec.ofNat 64 (2 ^ 64 - 4 % 2 ^ 64))
      = BitVec.ofNat 64 (m.val / 4 * 4) := by decide
  exact key ⟨M, h⟩

omit [CodeEnv] in
theorem a2_div4 (M i : Nat) (h4 : i % 4 = 0) (h : i + 4 ≤ M) : i < M / 4 * 4 := by omega

set_option maxRecDepth 100000 in
/-- Entry of the 4-wide `min` loop. -/
theorem blk_L22fa (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L22fa" ⟨"sbr_reset.L22fa", B.L22fa, some "sbr_reset.L2310"⟩ := by
  info_off
  measure_hb "L22fa"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hvm, hvm', hTB, h30,
        hdx, i, hsi, hi4, hiN⟩, hm⟩⟩ := T.L22fa.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hM : A2.n1N e a (k0N a row) k2 - 1 < 48 :=
      Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) hN.1) (by decide)) hN.2
    have hand := a2_and4 _ hM
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L22fa]
    vcgen
    all_goals rename_i s1 hs1 af
    all_goals subst hs1 hP
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdx]
    rw [hand]
    refine ⟨T.L2310.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
      hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
      ?_, ?_, i, ?_, hi4, a2_div4 _ _ hi4 hiN⟩, hm⟩⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · exact hrsp
    · exact hrbp
    · exact h15
    · exact h12
    · exact h13
    · exact hax
    · exact (BitVec.ofNat_add _ 1).symm
    · exact hsi
    · rw [← hn]; simp only [lex_var]
      exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)


omit [CodeEnv] in
/-- `and $-16, %rsi`. -/
theorem a2_and16 (M : Nat) (h : M < 48) :
    BitVec.ofNat 64 M &&& BitVec.setWidth 64 (BitVec.ofNat 64 (2 ^ 64 - 16 % 2 ^ 64))
      = BitVec.ofNat 64 (M / 16 * 16) := by
  have key : ∀ m : Fin 48, BitVec.ofNat 64 m.val &&& BitVec.setWidth 64 (BitVec.ofNat 64 (2 ^ 64 - 16 % 2 ^ 64))
      = BitVec.ofNat 64 (m.val / 16 * 16) := by decide
  exact key ⟨M, h⟩

set_option maxRecDepth 100000 in
/-- Entry of the 16-wide `min` loop. -/
theorem blk_L2267 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2267" ⟨"sbr_reset.L2267", B.L2267, some "sbr_reset.L2289"⟩ := by
  info_off
  measure_hb "L2267"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hvm, hvm', hTB, h30,
        h17, hdx⟩, hm⟩⟩ := T.L2267.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hM : A2.n1N e a (k0N a row) k2 - 1 < 48 :=
      Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) hN.1) (by decide)) hN.2
    have hand := a2_and16 _ hM
    have h17' : 17 ≤ A2.n1N e a (k0N a row) k2 := h17
    have hlt0 : 0 < (A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 := by omega
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2267]
    vcgen
    all_goals rename_i s1 hs1 af1 af2
    all_goals subst hs1 hP
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdx]
    rw [hand]
    refine ⟨T.L2289.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
      hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
      h17, ?_, ?_, ?_, 0, ?_, rfl, hlt0⟩, hm⟩⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    · exact hrsp
    · exact hrbp
    · exact h15
    · exact h12
    · exact h13
    · exact hax
    · exact hdx
    · exact (BitVec.ofNat_add _ 1).symm
    · rw [BitVec.xor_self]; rfl
    · rw [← hn]; simp only [lex_var]
      exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)


omit [CodeEnv] in
/-- `test $0xc, %dl`. -/
theorem a2_test12 (M : Nat) (h : M < 48) :
    (BitVec.setWidth 8 (BitVec.ofNat 64 M) &&& BitVec.setWidth 8 12#64 == BitVec.zero 8)
      = decide (M % 16 < 4) := by
  have key : ∀ m : Fin 48, (BitVec.setWidth 8 (BitVec.ofNat 64 m.val) &&& BitVec.setWidth 8 12#64
      == BitVec.zero 8) = decide (m.val % 16 < 4) := by decide
  exact key ⟨M, h⟩

omit [CodeEnv] in
theorem a2_c16 (N : Nat) (hN : 17 ≤ N) (he : N % 2 = 0) : (N - 1) / 16 * 16 + 1 < N := by omega

omit [CodeEnv] in
theorem a2_i16 (M : Nat) (h : ¬ M % 16 < 4) : M / 16 * 16 + 4 ≤ M := by omega

omit [CodeEnv] in
theorem a2_m16 (M : Nat) : M / 16 * 16 % 4 = 0 := by omega

set_option maxRecDepth 100000 in
/-- After the 16-wide `min` loop: the 4-wide loop or the scalar tail. -/
theorem blk_L22d3 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L22d3" ⟨"sbr_reset.L22d3", B.L22d3, some "sbr_reset.L22fa"⟩ := by
  info_off
  measure_hb "L22d3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hvm, hvm', hTB, h30,
        h17, hdx, hsi, hcx⟩, hm⟩⟩ := T.L22d3.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hM : A2.n1N e a (k0N a row) k2 - 1 < 48 :=
      Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.lt_of_lt_of_le (by decide) hN.1) (by decide)) hN.2
    have hev : A2.n1N e a (k0N a row) k2 % 2 = 0 := hN1.2.2
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L22d3]
    vcgen
    all_goals rename_i s1 hs1 af hc
    all_goals subst hs1 hP
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hdx, CondCode.interp_z,
        StatusFlags.zf_from_result] at hc
    case vc1 =>
      rw [a2_test12 _ hM] at hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2340.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        (A2.n1N e a (k0N a row) k2 - 1) / 16 * 16 + 1, ?_, Nat.le_add_left 1 _,
        a2_c16 _ h17 hev⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact hax
      · exact hcx
      · left; rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_lt_of_lt (by lex_len) (by decide)
    case vc2 =>
      rw [a2_test12 _ hM] at hc
      have h4 : ¬ (A2.n1N e a (k0N a row) k2 - 1) % 16 < 4 := of_decide_eq_false hc
      refine ⟨T.L22fa.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        ?_, (A2.n1N e a (k0N a row) k2 - 1) / 16 * 16, ?_, a2_m16 _, a2_i16 _ h4⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact hax
      · exact hdx
      · exact hsi
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)


omit [CodeEnv] in
theorem a2_idx_ec (r : BitVec 64) (c : Nat) (hc : 2 * c ≤ 236) :
    r + BitVec.ofNat 64 c * 2#64 + BitVec.ofNat 64 (2 ^ 64 - 236 % 2 ^ 64)
      = r - BitVec.ofNat 64 (236 - 2 * c) := by
  have hy : (BitVec.ofNat 64 c).toNat = c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hz : (BitVec.ofNat 64 (236 - 2 * c)).toNat = 236 - 2 * c := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hw : BitVec.ofNat 64 (2 ^ 64 - 236 % 2 ^ 64) = 18446744073709551380#64 := rfl
  rw [hw]
  generalize BitVec.ofNat 64 c = y at hy ⊢
  generalize BitVec.ofNat 64 (236 - 2 * c) = z at hz ⊢
  bv_omega

omit [CodeEnv] in
theorem a2_step4 (D i : Nat) (h4 : i % 4 = 0) (hD : D % 4 = 0) (hi : i < D) (hne : ¬ D = i + 4) :
    i + 4 < D := by omega

omit [CodeEnv] in
theorem a2_c4 (N : Nat) (h2 : 2 ≤ N) (he : N % 2 = 0) : (N - 1) / 4 * 4 + 1 < N := by omega

set_option maxRecDepth 100000 in
/-- The 4-wide `min` loop and its horizontal reduction. -/
theorem blk_L2310 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L2310" ⟨"sbr_reset.L2310", B.L2310, some "sbr_reset.L2340"⟩ := by
  info_off
  measure_hb "L2310"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, h15, hMB, h12, h13, hax, vm, hvm, hvm', hTB, h30,
        hdx, hcx, i, hsi, hi4, hiD⟩, hm⟩⟩ := T.L2310.mp hs
    clear hs
    have hN : 2 ≤ A2.n1N e a (k0N a row) k2 ∧ A2.n1N e a (k0N a row) k2 ≤ 48 := by
      have h1 : 2 ≤ A2.n1I e a (k0N a row) k2 := hN1.1
      have h2 : A2.n1I e a (k0N a row) k2 ≤ 48 := hN1.2.1
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat ∧ (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      omega
    have hiD' : i < (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 := hiD
    have hD48 : (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 ≤ 47 := by
      have := hN.2; omega
    have hi48 : i < 48 := by omega
    have hD64 : (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 < 2 ^ 64 := by omega
    have hl := fr_load hm hF (d := 236 - 2 * i) (n := 8) (by omega) (by omega)
    have ea := a2_idx_ec (t₀.regs.get64 .rsp - 8#64) i (by omega)
    have hinc : BitVec.setWidth 64 4#64 + BitVec.ofNat 64 i = BitVec.ofNat 64 (i + 4) := by
      rw [BitVec.setWidth_eq, BitVec.add_comm]; exact (BitVec.ofNat_add i 4).symm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L2310]
    vcgen
    case vc1 =>
      rename_i s1 hs1
      subst hs1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hsi, ea, hl, Option.isSome_some]
    case vc2 =>
      rename_i s1 hs1 v hv hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hsi, ea, hl, hdx, hinc, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      rw [a2_beq_ofNat _ _ hD64 (by omega)] at hc
      have hne : ¬ ((A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 = i + 4) := by
        intro h
        have hd : decide ((A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 = i + 4) = true := decide_eq_true h
        simp only [hd, Bool.not_true, Bool.false_eq_true] at hc
      have hlt4 := a2_step4 _ i hi4 (by omega) hiD' hne
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2310.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        ?_, ?_, i + 4, ?_, by omega, hlt4⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact hax
      · exact hdx
      · exact hcx
      · left; rw [← hn]; simp only [lex_var]
        simp only [VD.L2310, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hdx, hsi]
        apply Kraken.lex_cons_lt_cons (by lex_len)
        apply Kraken.lex_cons_lt_of_lt (by lex_len)
        simp only [BitVec.toNat_ofNat]
        have h1 : (i + 4) % 2 ^ 64 = i + 4 := Nat.mod_eq_of_lt (by omega)
        have h2 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
        have h3 : (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 % 2 ^ 64
            = (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 := Nat.mod_eq_of_lt hD64
        rw [h1, h2, h3]
        rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hD64),
          Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hD64)]
        omega
    case vc3 =>
      rename_i s1 hs1 v hv hc
      subst hs1 hP
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbp, hsi, ea, hl, hdx, hinc, CondCode.interp_nz, StatusFlags.zf_from_result_sub] at hv hc ⊢
      obtain rfl := Option.some.inj hv
      have hev : A2.n1N e a (k0N a row) k2 % 2 = 0 := hN1.2.2
      have hc1 : (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 + 1 < A2.n1N e a (k0N a row) k2 :=
        a2_c4 _ hN.1 hev
      refine ⟨T.L2340.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, fr,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc, hN0, hN1, ?_, hMB, ?_, ?_, ?_, vm, hvm, hvm', hTB, h30,
        (A2.n1N e a (k0N a row) k2 - 1) / 4 * 4 + 1, ?_, Nat.le_add_left 1 _, hc1⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · exact hrsp
      · exact hrbp
      · exact h15
      · exact h12
      · exact h13
      · exact hax
      · exact hcx
      · rw [← hn]; simp only [lex_var]
        exact Kraken.lex_cons_le_of_lt (by lex_len) (by decide)

end Kraken.Examples.Sbr.Reset
