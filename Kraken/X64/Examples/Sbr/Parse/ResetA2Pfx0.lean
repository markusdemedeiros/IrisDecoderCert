import Kraken.X64.Examples.Sbr.Parse.ResetA2Pfx1

/-!
# `sbr_reset`, shard A2: the prefix sums of `vk0` (`L1bbd`, `L1bf0`)

`L1bbd` stores `vk0[0] = k0`, keeps `vk0[n0]` (the last difference, `vdk0_max` for the two-region
case) in `edi` and enters the loop; `L1bf0` is one prefix-sum step, failing to `L1cf4` on a
non-positive entry, and at the end branches on `49 k2 ≤ 110 k0` (one region, `L1da7`).
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
theorem a2_cc_nc_sub' {w : Nat} (a b : BitVec w) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  show (!(((a - b).toNat : Int) != (a.toNat : Int) - (b.toNat : Int))) = _
  rw [borrow_sub]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

omit [CodeEnv] in
theorem a2_faddr (x K : BitVec 64) (d : Nat) (hK : K.toNat + d = 2 ^ 64) :
    x - 8#64 + K = x - 8#64 - BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  have := K.isLt
  omega

theorem a2_k0_load {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x40#64) 2 = some (Int.ofBytes (Int.toBytes 2 (st.x.k0 : Int))) := by
  have h := region_load (o := 0) (n := 2) (focus (Mm_k0 ..) hm) (addr := arg1 t₀ + 0x40#64)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [h]; simp [slice, Int.toBytes]

omit [CodeEnv] in
/-- A 2-byte write below `rb 0x100` keeps the `SF` slots. -/
theorem a2_sf_wr {fr : List UInt8} {e : REnv} {a : RArgs} {t₀ : MachineData} {k0 k2 : Nat}
    (p : Nat) (v : Int) (h : p + 2 ≤ fr.length) (hd : p + 2 ≤ rb 0x100)
    (hS : A2.SF fr e a t₀ k0 k2) : A2.SF (wr fr p (Int.toBytes 2 v)) e a t₀ k0 k2 := by
  simp only [rb] at hd
  simp (disch := (simp only [rb]; omega)) only [A2.SF, A2.SE, A2.SD, A2.SC, A2.SB, A2.SA,
    a2_slot32_wr fr p _ v h, a2_slot64_wr fr p _ v h]
  exact hS

omit [CodeEnv] in
/-- The start of the prefix sums: `vk[0] = v0` written, `vk[1 ..= n]` from `Arr`. -/
theorem a2_pfx_startB {fr : List UInt8} {o n : Nat} {B tot : Int} (hA : A2.Arr fr o n B tot)
    (hlen : o + 2 ≤ fr.length) (V v0 : Int) (hV : (BitVec.ofInt 16 V).toInt = v0) :
    ∃ A, A2.Pfx (wr fr (o + 2 * 0) (Int.toBytes 2 V)) o n 1 B v0 tot A
      ∧ ∀ i, 1 ≤ i → i ≤ n → A2.fv fr o i = A i := by
  obtain ⟨A, hA, hs⟩ := hA
  refine ⟨A, ⟨fun i h1 h2 => (hA i h1 h2).2, hs, fun i hi => ?_, fun i h1 h2 => by omega,
    fun i h1 h2 => ?_⟩, fun i h1 h2 => (hA i h1 h2).1⟩
  · rw [a2_fv_wr fr o 0 i V (by omega), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    obtain rfl : i = 0 := by omega
    simp [A2.ssum, hV]
  · rw [a2_fv_wr fr o 0 i V (by omega), ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    exact (hA i (by omega) h2).1

omit [CodeEnv] in
theorem a2_vaddrO (x : BitVec 64) (c o j : Nat) (K : BitVec 64) (Kn : Nat) (hKv : K.toNat = Kn)
    (h : Kn + 2 * c + 0x570 = o + 2 * j + 2 ^ 64) :
    x - 8#64 + BitVec.ofNat 64 c * 2#64 + K = x - 0x578#64 + BitVec.ofNat 64 (o + 2 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, hKv]
  have := x.isLt
  omega

omit [CodeEnv] in
theorem a2_addrO (x K : BitVec 64) (o : Nat) (Kn : Nat) (hKv : K.toNat = Kn)
    (hK : Kn + 0x570 = o + 2 ^ 64) :
    x - 8#64 + K = x - 0x578#64 + BitVec.ofNat 64 (o + 2 * 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hKv]
  have := x.isLt
  omega

omit [CodeEnv] in
theorem a2_sw32_ofInt64 (x : Int) : (BitVec.ofInt 64 x).setWidth 32 = BitVec.ofInt 32 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have h1 := Int.emod_nonneg x (show ((2 ^ 64 : Nat) : Int) ≠ 0 by decide)
  have h3 := Int.emod_nonneg x (show ((2 ^ 32 : Nat) : Int) ≠ 0 by decide)
  have h2 := Int.emod_emod_of_dvd x (show ((2 ^ 32 : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) from
    ⟨2 ^ 32, by decide⟩)
  omega

omit [CodeEnv] in
/-- The low half of an 8-byte frame load is the 4-byte slot. -/
theorem a2_lo32_sl8 (fr : List UInt8) (o : Nat) :
    (BitVec.ofInt 64 (Int.ofBytes (slice fr o 8))).setWidth 32
      = BitVec.ofInt 32 (Int.ofBytes (slice fr o 4)) := by
  rw [a2_sw32_ofInt64, BitVec.ofInt_ofBytes_take 32 4 rfl]
  simp only [slice, List.take_take]
  rfl

omit [CodeEnv] in
theorem a2_sx_lo (X : BitVec 16) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.signExtend 32 X)) = BitVec.ofInt 32 X.toInt := by
  have : ∀ y : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 y) = y := fun y => by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := y.isLt
    omega
  rw [this]; rfl

omit [CodeEnv] in
theorem a2_k0_val (K : Nat) (hK : K ≤ 128) (x : Int)
    (hx : x = Int.ofBytes (Int.toBytes 2 (K : Int))) :
    (BitVec.ofInt 16 (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 16 x)))).toInt).toInt = (K : Int) := by
  rw [a2_sw16_32, BitVec.ofInt_toInt, hx, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl,
    a2_toInt16_small _ (by omega) (by omega)]

omit [CodeEnv] in
theorem a2_rsi1 (n : Nat) (h : n ≤ 48) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + 1#64))
      = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 100000 in
theorem blk_L1bbd (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1bbd" ⟨"sbr_reset.L1bbd", B.L1bbd, some "sbr_reset.L1bf0"⟩ := by
  info_off
  measure_hb "L1bbd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, hArr⟩, hm⟩⟩ := T.L1bbd.mp hs
    clear hs
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hn0p : 1 ≤ A2.n0N e a (k0N a row) k2 := by
      show 1 ≤ (A2.n0I e a (k0N a row) k2).toNat
      have := hN0.1; omega
    have hk0 : k0N a row ≤ 128 := by omega
    have e48 : s₀.regs.get64 .rbp + 18446744073709551544#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by
      rw [hrbp]; exact a2_faddr _ _ _ rfl
    have ld48 := fr_load hm hF (d := 0x48) (n := 8) (by omega) (by omega)
    rw [← e48] at ld48
    have hrcx : BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x48) 8))
        = BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2) := hSF.2
    have hcv : (BitVec.setWidth 32 (BitVec.ofNat 64 (A2.n0N e a (k0N a row) k2))).toNat
        = A2.n0N e a (k0N a row) k2 := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hav : s₀.regs.get64 .rbp + s₀.regs.get64 .rax * 2#64 + 18446744073709551248#64
        = t₀.regs.get64 .rsp - 0x578#64
          + BitVec.ofNat 64 (0x400 + 2 * A2.n0N e a (k0N a row) k2) := by
      rw [hrbp, hax]; exact a2_vaddrO _ _ _ _ _ (Kn := 18446744073709551248) rfl (by omega)
    have ldv := a2_vk_load hm hF (o := 0x400) (i := A2.n0N e a (k0N a row) k2) (by omega) hav
    have hk0v : st.x.k0 = k0N a row := by rw [hx]
    have hld0 := a2_k0_load hm
    rw [hk0v] at hld0
    have ha0 : s₀.regs.get64 .rbp + 18446744073709551248#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x400 + 2 * 0) := by
      rw [hrbp]; exact a2_addrO _ _ _ (Kn := 18446744073709551248) rfl (by omega)
    have hlen : 0x400 + 2 ≤ fr.length := by rw [hF]; omega
    have ld0 := a2_vk_load hm hF (o := 0x400) (i := 0) (by omega) ha0
    have hm1 := fun V => a2_vk_store hm hF (o := 0x400) (i := 0) (by omega) ha0 V
    have hF1 : ∀ V, FrOk (wr fr (0x400 + 2 * 0) (Int.toBytes 2 V)) := fun V => by
      show List.length _ = _
      rw [wr_length (by rw [Int.toBytes_length]; omega), hF]
    have e50 : s₀.regs.get64 .rbp + 18446744073709551536#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by
      rw [hrbp]; exact a2_faddr _ _ _ rfl
    have ld50 := fun V => (fr_load (hm1 V) (hF1 V) (d := 0x50) (n := 8) (by omega)
      (by omega)).trans (by rw [a2_slice_wr2 fr _ _ _ V hlen (by simp only [rb]; omega)])
    have hr50 : BitVec.setWidth 32 (BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x50) 8)))
        + BitVec.setWidth 32 (BitVec.ofInt 64 (Int.ofBytes (slice fr (rb 0x50) 8)))
        = BitVec.ofNat 32 (A2.n0N e a (k0N a row) k2) := by
      rw [a2_lo32_sl8]; exact hSF.1.1.1.2.1
    have hrax := a2_neg_r15 _ _ hn0 hr50
    have hSF1 := fun V => a2_sf_wr (0x400 + 2 * 0) V hlen (by simp only [rb]; omega) hSF
    have hP := fun x hx => a2_pfx_startB hArr hlen
      (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 x)))).toInt _
      (a2_k0_val _ hk0 x hx)
    have hrsi := a2_rsi1 _ hn0
    generalize hP' : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1bbd]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some]
    · rw [ld48]; rfl
    · rename_i x8 hl8 hnc
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, ld48] at hl8
      obtain rfl := Option.some.inj hl8
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, a2_cc_nc_sub', hrcx, hcv, decide_eq_true_eq] at hnc
      have : (BitVec.setWidth 32 49#64).toNat = 49 := rfl
      omega
    · rw [ldv]; rfl
    · simp only [h12, hld0, Option.isSome_some]
    · rw [ld0]; rfl
    · rw [e50, ld50]; rfl
    · rename_i x8 hl8 hnc x5 hl5 x3 hl3 x1 hl1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hl8 hl5 hl3 hl1
      rw [ld48] at hl8; rw [ldv] at hl5; rw [h12, hld0] at hl3; rw [e50, ld50] at hl1
      obtain rfl := Option.some.inj hl8
      obtain rfl := Option.some.inj hl5
      obtain rfl := Option.some.inj hl1
      obtain ⟨A, hPA, hAeq⟩ := hP x3 (Option.some.inj hl3).symm
      refine ⟨T.L1bf0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp,
        hfm, hF1 _, ⟨hk2v, hk1v, hSF1 _, hN0, ?_, ?_, ?_, ?_, 1, A, ?_, Nat.le_refl 1, hn0p, hPA,
        ?_⟩, hm1 _⟩⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        hrcx, hrax, hrsi]
      · rfl
      · rw [a2_sx_lo]; exact congrArg (BitVec.ofInt 32) (hAeq _ hn0p (Nat.le_refl _))

omit [CodeEnv] in
theorem a2_sx_16 (X : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.signExtend 32 X)) = X := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.signExtend, BitVec.toNat_ofInt]
  have := X.isLt
  rw [BitVec.toInt_eq_toNat_bmod]
  simp only [Int.bmod_def]
  split <;> omega

omit [CodeEnv] in
/-- One prefix-sum step computed as `Y + X`, entries in `[-B, B]` with `B ≤ 256`. -/
theorem a2_pfx_add_stepB {fr : List UInt8} {o n j : Nat} {B v0 tot : Int} {A : Nat → Int}
    (hP : A2.Pfx fr o n j B v0 tot A) (hB : B ≤ 256) (hj1 : 1 ≤ j) (hjn : j ≤ n) (hn : n ≤ 48)
    (hv0 : 0 ≤ v0) (hv1 : v0 ≤ 128) (hpos : 0 < A j) (hlen : o + 2 * j + 2 ≤ fr.length)
    (X Y : BitVec 16) (hX : X.toInt = A j) (hY : Y.toInt = v0 + A2.ssum A (j - 1)) :
    A2.Pfx (wr fr (o + 2 * j) (Int.toBytes 2 (Y + X).toInt)) o n (j + 1) B v0 tot A := by
  have hsb := a2_ssum_bound A n (fun i h1 h2 => by
    have := hP.1 i h1 h2; constructor <;> omega) (j - 1) (by omega)
  have hAj := hP.1 j hj1 hjn
  have hs : A2.ssum A j = A2.ssum A (j - 1) + A j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp [A2.ssum]
  refine a2_pfx_step hP hj1 hjn hpos hlen _ ?_
  rw [BitVec.ofInt_toInt, a2_add16 Y X hY hX (by omega) (by omega), hs]
  omega

omit [CodeEnv] in
theorem a2_toInt32_16 (X : BitVec 16) : (BitVec.ofInt 32 X.toInt).toInt = X.toInt := by
  rw [BitVec.toInt_ofInt]
  have h1 := BitVec.toInt_lt (x := X)
  have h2 := BitVec.le_toInt (x := X)
  simp only [Int.bmod_def] at *
  split <;> omega

omit [CodeEnv] in
theorem a2_sw32_64 (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 y) = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := y.isLt
  omega

omit [CodeEnv] in
theorem a2_negn_inc (n j : Nat) (hn : n ≤ 64) (hj : j ≤ 64) :
    (BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 j + 1#64 - BitVec.setWidth 64 1#64
      == BitVec.zero 64) = decide (j = n) := by
  by_cases h : j = n
  · subst h
    have : BitVec.ofInt 64 (-(j : Int)) + BitVec.ofNat 64 j + 1#64 - BitVec.setWidth 64 1#64
        = BitVec.zero 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth]
      simp; omega
    rw [this]; simp
  · have : BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 j + 1#64 - BitVec.setWidth 64 1#64
        ≠ BitVec.zero 64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth] at this
      simp at this; omega
    simp only [h, decide_false, beq_eq_false_iff_ne]; exact this

omit [CodeEnv] in
theorem a2_inc1 (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 100000 in
theorem blk_L1bf0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1bf0" ⟨"sbr_reset.L1bf0", B.L1bf0, some "sbr_reset.L1c33"⟩ := by
  info_off
  measure_hb "L1bf0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hSF, hN0, h12, h15, hax, hsi, j, A, hcx, hj1, hjn, hP, hdi⟩, hm⟩⟩ :=
      T.L1bf0.mp hs
    clear hs
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hk0a : (0 : Int) ≤ ((k0N a row : Nat) : Int) := by omega
    have hk0b : ((k0N a row : Nat) : Int) ≤ 128 := by omega
    have haj : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551248#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x400 + 2 * j) := by
      rw [hrbp, hcx]; exact a2_vaddrO _ _ _ _ _ (Kn := 18446744073709551248) rfl (by omega)
    have haj1 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551246#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x400 + 2 * (j - 1)) := by
      rw [hrbp, hcx]; exact a2_vaddrO _ _ _ _ _ (Kn := 18446744073709551246) rfl (by omega)
    have hlenj : 0x400 + 2 * j + 2 ≤ fr.length := by rw [hF]; omega
    have ldj := a2_vk_load hm hF (o := 0x400) (i := j) (by omega) haj
    have ldj1 := a2_vk_load hm hF (o := 0x400) (i := j - 1) (by omega) haj1
    have hmS := fun V => a2_vk_store hm hF (o := 0x400) (i := j) (by omega) haj V
    have hF1 : ∀ V, FrOk (wr fr (0x400 + 2 * j) (Int.toBytes 2 V)) := fun V => by
      show List.length _ = _
      rw [wr_length (by rw [Int.toBytes_length]; omega), hF]
    have hXj : ∀ x, some (Int.ofBytes (slice fr (0x400 + 2 * j) 2)) = some x →
        (BitVec.ofInt 16 x).toInt = A j := fun x hx => by
      obtain rfl := Option.some.inj hx; exact hP.2.2.2.2 j (by omega) hjn
    have hYj : ∀ y, some (Int.ofBytes (slice fr (0x400 + 2 * (j - 1)) 2)) = some y →
        (BitVec.ofInt 16 y).toInt = ((k0N a row : Nat) : Int) + A2.ssum A (j - 1) :=
      fun y hy => by obtain rfl := Option.some.inj hy; exact hP.2.2.1 (j - 1) (by omega)
    have hstep := fun X Y hX hY hpos =>
      a2_pfx_add_stepB hP (by decide) hj1 hjn hn0 hk0a hk0b hpos hlenj X Y hX hY
    have hzz := a2_negn_inc (A2.n0N e a (k0N a row) k2) j (by omega) (by omega)
    rw [← hax, ← hcx] at hzz
    have hcx1 : s₀.regs.get64 .rcx + 1#64 = BitVec.ofNat 64 (j + 1) := by
      rw [hcx]; exact a2_inc1 j
    have hlt1 : j ≠ A2.n0N e a (k0N a row) k2 → j + 1 ≤ A2.n0N e a (k0N a row) k2 :=
      fun h => by omega
    have hvar : ∀ s : MachineData, s.regs.get64 .rsi = s₀.regs.get64 .rsi →
        s.regs.get64 .rcx = BitVec.ofNat 64 (j + 1) →
        var "sbr_reset.L1bf0" s < var "sbr_reset.L1bf0" s₀ := fun s h1 h2 => by
      simp only [lex_var, h1, h2, hcx, hsi]
      refine Kraken.lex_cons_lt_cons (by lex_len) ?_
      refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
      have e1 := congrArg BitVec.toNat h1
      have e2 := congrArg BitVec.toNat h2
      have e3 := congrArg BitVec.toNat hcx
      have e4 := congrArg BitVec.toNat hsi
      simp only [BitVec.toNat_ofNat] at e2 e3 e4
      omega
    have hM : Reset (spOf a) (lbN a) a.x st.x.turnoff := by
      rw [hx]; exact Reset.badMaster hC.2.1 (Master.fail hrow)
    have e88 : s₀.regs.get64 .rbp + 18446744073709551480#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x88 := by
      rw [hrbp]; exact a2_faddr _ _ _ rfl
    have e80 : s₀.regs.get64 .rbp + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by
      rw [hrbp]; exact a2_faddr _ _ _ rfl
    have ld88 := fun V => (fr_load (hmS V) (hF1 V) (d := 0x88) (n := 4) (by omega)
      (by omega)).trans (by rw [a2_slice_wr2 fr _ _ _ V (by omega) (by simp only [rb]; omega)])
    have ld80 := fun V => (fr_load (hmS V) (hF1 V) (d := 0x80) (n := 4) (by omega)
      (by omega)).trans (by rw [a2_slice_wr2 fr _ _ _ V (by omega) (by simp only [rb]; omega)])
    have h88 : BitVec.ofInt 32 (Int.ofBytes (slice fr (rb 0x88) 4))
        = BitVec.ofNat 32 (110 * k0N a row) := hSF.1.1.1.1.1.2
    have h80 : BitVec.ofInt 32 (Int.ofBytes (slice fr (rb 0x80) 4))
        = BitVec.ofNat 32 (49 * k2) := hSF.1.1.1.1.1.1
    have hcv88 : (BitVec.ofNat 32 (110 * k0N a row)).toNat = 110 * k0N a row := by
      simp only [BitVec.toNat_ofNat]; omega
    have hcv80 : (BitVec.ofNat 32 (49 * k2)).toNat = 49 * k2 := by
      simp only [BitVec.toNat_ofNat]; omega
    have hSF1 := fun V => a2_sf_wr (0x400 + 2 * j) V hlenj (by simp only [rb]; omega) hSF
    have hfin : ∀ fr', A2.Pfx fr' 0x400 (A2.n0N e a (k0N a row) k2) (j + 1) 64 (k0N a row)
        (((A2.k1Of (k0N a row) k2 : Nat) : Int) - ((k0N a row : Nat) : Int)) A →
        j = A2.n0N e a (k0N a row) k2 →
        A2.Inc fr' 0x400 (A2.n0N e a (k0N a row) k2) (k0N a row) (A2.k1Of (k0N a row) k2) :=
      fun fr' hP' h => a2_pfx_inc' hP' (by omega) _ (by omega)
    have hk1k2 : ¬ 110 * k0N a row < 49 * k2 → A2.k1Of (k0N a row) k2 = k2 := fun h => by
      simp only [A2.k1Of]; exact ite_eq_right_iff.mpr (fun h' => absurd h' h)
    have hfin2 : ∀ fr', A2.Pfx fr' 0x400 (A2.n0N e a (k0N a row) k2) (j + 1) 64 (k0N a row)
        (((A2.k1Of (k0N a row) k2 : Nat) : Int) - ((k0N a row : Nat) : Int)) A →
        j = A2.n0N e a (k0N a row) k2 → ¬ 110 * k0N a row < 49 * k2 →
        A2.Inc fr' 0x400 (A2.n0N e a (k0N a row) k2) (k0N a row) k2 := fun fr' hP' h hn => by
      have h' := hfin fr' hP' h
      rw [hk1k2 hn] at h'
      exact h'
    have hvm := hP.1 (A2.n0N e a (k0N a row) k2) (by omega) (Nat.le_refl _)
    have hbe1 : 49 * k2 ≤ 110 * k0N a row → ¬ 110 * k0N a row < 49 * k2 := fun h => by omega
    have hbe2 : ¬ 49 * k2 ≤ 110 * k0N a row → 110 * k0N a row < 49 * k2 := fun h => by omega
    generalize hP' : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L1bf0]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some, a2_sx_16, a2_sw16_rl]
    · rw [ldj]; rfl
    · rename_i x hx1 af ht
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hx1
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1cf4.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]
      edge_step
    · rw [ldj1]; rfl
    · rw [ldj]; rfl
    · rename_i x hx1 af ht y hy hz
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, a2_cc_le_test,
        a2_sx_lo, a2_toInt32_16, decide_eq_false_iff_not, Int.not_le, CondCode.interp_nz,
        StatusFlags.zf_from_result, hzz, Bool.not_eq_true', decide_eq_false_iff_not] at hx1 ht hy hz
      rw [ldj] at hx1; rw [ldj1] at hy
      have hX := hXj _ hx1
      have hP1 := hstep _ _ hX (hYj _ hy) (by omega)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1bf0.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _,
        hx, hsp, hfm, hF1 _, ⟨hk2v, hk1v, hSF1 _, hN0, ?_, ?_, ?_, ?_, j + 1, A, ?_, by omega,
        hlt1 hz, hP1, ?_⟩, hmS _⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        hax, hsi, hcx1, hdi]
      left; apply hvar
      · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      · simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hcx1]
    · rw [e88, ld88]; rfl
    · rw [e80, ld80]; rfl
    · rename_i x hx1 af ht y hy hz w88 hw88 w80 hw80 hbe
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, a2_cc_le_test,
        a2_sx_lo, a2_toInt32_16, decide_eq_false_iff_not, Int.not_le, CondCode.interp_nz,
        StatusFlags.zf_from_result, hzz, Bool.not_eq_false',
        decide_eq_true_eq] at hx1 ht hy hz hw88 hw80
      rw [ldj] at hx1; rw [ldj1] at hy; rw [e88, ld88] at hw88; rw [e80, ld80] at hw80
      obtain rfl := Option.some.inj hw88
      obtain rfl := Option.some.inj hw80
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, a2_sw32_64, cc_be_sub, h80, h88,
        hcv80, hcv88, decide_eq_true_eq, decide_eq_false_iff_not] at hbe
      have hX := hXj _ hx1
      have hP1 := hstep _ _ hX (hYj _ hy) (by omega)
      have hnot := hbe1 hbe
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L1da7.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _,
        hx, hsp, hfm, hF1 _, ⟨hk2v, hk1v, hSF1 _, hN0, ?_, ?_, hnot, hfin2 _ hP1 hz hnot⟩,
        hmS _⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15]
      edge_step
    · rename_i x hx1 af ht y hy hz w88 hw88 w80 hw80 hbe
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, a2_cc_le_test,
        a2_sx_lo, a2_toInt32_16, decide_eq_false_iff_not, Int.not_le, CondCode.interp_nz,
        StatusFlags.zf_from_result, hzz, Bool.not_eq_false',
        decide_eq_true_eq] at hx1 ht hy hz hw88 hw80
      rw [ldj] at hx1; rw [ldj1] at hy; rw [e88, ld88] at hw88; rw [e80, ld80] at hw80
      obtain rfl := Option.some.inj hw88
      obtain rfl := Option.some.inj hw80
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, a2_sw32_64, cc_be_sub, h80, h88,
        hcv80, hcv88, decide_eq_true_eq, decide_eq_false_iff_not] at hbe
      have hX := hXj _ hx1
      have hP1 := hstep _ _ hX (hYj _ hy) (by omega)
      have hI := hfin _ hP1 hz
      refine ⟨T.L1c33.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _,
        hx, hsp, hfm, hF1 _, ⟨hk2v, hk1v, hSF1 _, hbe2 hbe, hI, hN0, ?_, ?_, ?_,
        A (A2.n0N e a (k0N a row) k2), hvm.1, hvm.2, ?_⟩, hmS _⟩⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h15,
        hsi, hdi]

end Kraken.Examples.Sbr.Reset
