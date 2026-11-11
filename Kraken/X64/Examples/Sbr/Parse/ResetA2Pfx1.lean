import Kraken.X64.Examples.Sbr.Parse.ResetA2Pfx

/-!
# `sbr_reset`, shard A2: the prefix sums of `vk1`, loop entry and body (`L287a` … `L28e7`)

`L287a` stores `vk1[0] = k1` and enters the 4× unrolled loop; `L289b` and `L28e7` each do two
prefix-sum steps (`a2_pfx_add_step`), failing to `L29cd` … `L29dc` on a non-positive entry.
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
theorem a2_sw16_32 (x : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

omit [CodeEnv] in
theorem a2_sw16_rl (old : BitVec 64) (new : BitVec 16) :
    (old.replaceLow new).setWidth 16 = new := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow16_mod]

omit [CodeEnv] in
theorem a2_cc_le_test16 (V : BitVec 16) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (V &&& V) { cf := false, af := af, of := false })
      = decide (V.toInt ≤ 0) := by
  rw [BitVec.and_self]
  simp only [CondCode.interp_le, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
    StatusFlags.of_from_result]
  have hz : (V == BitVec.zero 16) = decide (V.toNat = 0) := by
    by_cases h : V.toNat = 0
    · have : V = BitVec.zero 16 := BitVec.eq_of_toNat_eq (by simp [h])
      simp [this]
    · have : V ≠ 0#16 := fun h' => h (by simp [h'])
      simpa [h] using this
  rw [hz, BitVec.toInt_eq_msb_cond]
  have := V.isLt
  cases hm : V.msb <;> simp <;> omega

omit [CodeEnv] in
theorem a2_add16 (X Y : BitVec 16) {p q : Int} (hx : X.toInt = p) (hy : Y.toInt = q)
    (h1 : -32768 ≤ p + q) (h2 : p + q < 32768) : (X + Y).toInt = p + q := by
  rw [BitVec.toInt_add, hx, hy]; simp only [Int.bmod_def]; split <;> omega

omit [CodeEnv] in
theorem a2_sub52 (c : Nat) (hc : c ≤ 64) :
    (BitVec.ofNat 64 c - BitVec.setWidth 64 52#64 == BitVec.zero 64) = decide (c = 52) := by
  by_cases h : c = 52
  · subst h; decide
  · have : BitVec.ofNat 64 c - BitVec.setWidth 64 52#64 ≠ BitVec.zero 64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_setWidth] at this
      simp at this; omega
    simp only [h, decide_false, beq_eq_false_iff_ne]; exact this

omit [CodeEnv] in
/-- One prefix-sum step computed as `Y + X` (`Y = vk[j-1]`, `X = vk[j]` as `int16`). -/
theorem a2_pfx_add_step {fr : List UInt8} {o n j : Nat} {v0 tot : Int} {A : Nat → Int}
    (hP : A2.Pfx fr o n j 256 v0 tot A) (hj1 : 1 ≤ j) (hjn : j ≤ n) (hn : n ≤ 48)
    (hv0 : 0 ≤ v0) (hv1 : v0 ≤ 128) (hpos : 0 < A j) (hlen : o + 2 * j + 2 ≤ fr.length)
    (X Y : BitVec 16) (hX : X.toInt = A j) (hY : Y.toInt = v0 + A2.ssum A (j - 1)) :
    A2.Pfx (wr fr (o + 2 * j) (Int.toBytes 2 (Y + X).toInt)) o n (j + 1) 256 v0 tot A := by
  have hsb := a2_ssum_bound A n hP.1 (j - 1) (by omega)
  have hAj := hP.1 j hj1 hjn
  have hs : A2.ssum A j = A2.ssum A (j - 1) + A j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp [A2.ssum]
  refine a2_pfx_step hP hj1 hjn hpos hlen _ ?_
  rw [BitVec.ofInt_toInt, a2_add16 Y X hY hX (by omega) (by omega), hs]
  omega

omit [CodeEnv] in
/-- The address of `vk1[j]` as `rbp + 2 rcx - K`. -/
theorem a2_vaddr (x : BitVec 64) (c o : Nat) (K : BitVec 64)
    (hK : K.toNat + 2 * c + 0x570 = o + 2 ^ 64) :
    x - 8#64 + BitVec.ofNat 64 c * 2#64 + K = x - 0x578#64 + BitVec.ofNat 64 o := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem a2_k1_load {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) :
    m.loadInt (arg1 t₀ + 0x44#64) 2 = some (Int.ofBytes (Int.toBytes 2 st.k1.toInt)) := by
  have h := region_load (o := 0) (n := 2) (focus (Mm_k1 ..) hm) (addr := arg1 t₀ + 0x44#64)
    (by simp) (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [h]; simp [slice, Int.toBytes]

omit [CodeEnv] in
theorem a2_k1_val (K : Nat) (hK : K ≤ 128) (x : Int)
    (hx : x = Int.ofBytes (Int.toBytes 2 (BitVec.ofNat 32 K).toInt)) :
    (BitVec.ofInt 16 (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 16 x)))).toInt).toInt = (K : Int) := by
  rw [a2_sw16_32, BitVec.ofInt_toInt, hx, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl]
  have h1 : (BitVec.ofNat 32 K).toInt = (K : Int) := by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]; simp only [Int.bmod_def]
    split <;> omega
  rw [h1, a2_toInt16_small _ (by omega) (by omega)]

omit [CodeEnv] in
theorem a2_neg_r15 (r : BitVec 64) (n : Nat) (hn : n ≤ 48)
    (h : BitVec.setWidth 32 r + BitVec.setWidth 32 r = BitVec.ofNat 32 n) :
    -BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32 r)
      = BitVec.ofInt 64 (-((n : Nat) : Int)) := by
  rw [h]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_neg, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem a2_addr0 (x K : BitVec 64) (hK : K.toNat + 0x570 = 0x480 + 2 ^ 64) :
    x - 8#64 + K = x - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

omit [CodeEnv] in
/-- The start of the prefix sums: `vk[0] = v0` written, `vk[1 ..= n]` from `Arr`. -/
theorem a2_pfx_start {fr : List UInt8} {o n : Nat} {tot : Int} (hA : A2.Arr fr o n 256 tot)
    (hlen : o + 2 ≤ fr.length) (V v0 : Int) (hV : (BitVec.ofInt 16 V).toInt = v0) :
    ∃ A, A2.Pfx (wr fr (o + 2 * 0) (Int.toBytes 2 V)) o n 1 256 v0 tot A := by
  obtain ⟨A, hA, hs⟩ := hA
  refine ⟨A, fun i h1 h2 => (hA i h1 h2).2, hs, fun i hi => ?_, fun i h1 h2 => by omega,
    fun i h1 h2 => ?_⟩
  · rw [a2_fv_wr fr o 0 i V (by omega), ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
    obtain rfl : i = 0 := by omega
    simp [A2.ssum, hV]
  · rw [a2_fv_wr fr o 0 i V (by omega), ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
    exact (hA i (by omega) h2).1


set_option maxRecDepth 100000 in
theorem blk_L287a (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L287a" ⟨"sbr_reset.L287a", B.L287a, some "sbr_reset.L289b"⟩ := by
  info_off
  measure_hb "L287a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h15, h12, h13, vm, hTA, h30, hArr⟩, hm⟩⟩ := T.L287a.mp hs
    clear hs
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hn12 : 2 ≤ A2.n1N e a (k0N a row) k2 := by
      show 2 ≤ (A2.n1I e a (k0N a row) k2).toNat
      have := hN1.1; omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have h4 : 4 ≤ A2.n1N e a (k0N a row) k2 + 2 := by omega
    have hk1 : A2.k1Of (k0N a row) k2 ≤ 128 := by simp only [A2.k1Of]; split <;> omega
    have hld := a2_k1_load hm
    rw [hk1v] at hld
    have hlen : 0x480 + 2 ≤ fr.length := by rw [hF]; omega
    have ha : s₀.regs.get64 .rbp + 18446744073709551376#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * 0) := by
      rw [hrbp]; exact a2_addr0 _ _ rfl
    have hm2 := fun V => a2_vk_store hm hF (o := 0x480) (i := 0) (by omega) ha V
    have hl2 := a2_vk_load hm hF (o := 0x480) (i := 0) (by omega) ha
    have hFr : ∀ V, FrOk (wr fr (0x480 + 2 * 0) (Int.toBytes 2 V)) := fun V => by
      show List.length _ = _
      rw [wr_length (by rw [Int.toBytes_length]; omega), hF]
    have hI0 := fun V => a2_inc_wr2 (p := 0x480 + 2 * 0) V hlen (by omega) hInc0
    have hTA' := fun V => a2_ta_wr (0x480 + 2 * 0) V hlen (by simp only [rb]; omega) hTA
    have h30' := fun V => (a2_slot64_wr fr (0x480 + 2 * 0) 0x30 V hlen
      (by simp only [rb]; omega)).trans h30
    have hP := fun x hx => a2_pfx_start hArr hlen
      (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 x)))).toInt _
      (a2_k1_val _ hk1 x hx)
    have hr15 := a2_neg_r15 _ _ hn1 h15
    have hle : ∀ af, CondCode.le.interp (StatusFlags.from_result
        (BitVec.setWidth 32 (s₀.regs.get64 .r13) &&& BitVec.setWidth 32 (s₀.regs.get64 .r13))
        { cf := false, af := af, of := false }) = false := by
      intro af; rw [a2_cc_le_test, h13]
      have : (BitVec.setWidth 32 (BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2))).toInt
          = (A2.n1N e a (k0N a row) k2 : Int) := by
        rw [BitVec.toInt_eq_toNat_bmod]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        simp only [Int.bmod_def]; split <;> omega
      rw [this]; simp; omega
    generalize hP' : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L287a]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some]
    · simp only [h12, hld, Option.isSome_some]
    · rw [hl2]; rfl
    · rename_i hle'
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hle] at hle'
    · rename_i x hxl af hle'
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, h12, hld] at hxl
      obtain ⟨A, hPA⟩ := hP x (Option.some.inj hxl).symm
      refine ⟨T.L289b.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp,
        hfm, hFr _, ⟨hk2v, hk1v, hlt, hI0 _, hN0, hN1, ?_, ?_, ?_, vm, hTA' _, h30' _, 4, A, ?_,
        rfl, by omega, h4, hPA⟩, hm2 _⟩⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13, hr15]
      rfl

omit [CodeEnv] in
theorem a2_vaddr' (x : BitVec 64) (c j : Nat) (K : BitVec 64) (Kn : Nat) (hKv : K.toNat = Kn)
    (h : Kn + 2 * c + 0x570 = 0x480 + 2 * j + 2 ^ 64) :
    x - 8#64 + BitVec.ofNat 64 c * 2#64 + K = x - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_mul, BitVec.toNat_ofNat, hKv]
  have := x.isLt
  omega

set_option maxRecDepth 100000 in
theorem blk_L289b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L289b" ⟨"sbr_reset.L289b", B.L289b, some "sbr_reset.L28e7"⟩ := by
  info_off
  measure_hb "L289b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h13, h15, vm, hTA, h30, c, A, hcx, hc4, hc4le, hcn,
        hP⟩, hm⟩⟩ := T.L289b.mp hs
    clear hs
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hk1 : A2.k1Of (k0N a row) k2 ≤ 128 := by simp only [A2.k1Of]; split <;> omega
    have hc50 : c ≤ 50 := by omega
    have hk1a : (0 : Int) ≤ ((A2.k1Of (k0N a row) k2 : Nat) : Int) := by omega
    have hk1b : ((A2.k1Of (k0N a row) k2 : Nat) : Int) ≤ 128 := by omega
    have hlen1 : 0x480 + 2 * (c - 3) + 2 ≤ fr.length := by rw [hF]; omega
    have ha1 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551370#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * (c - 3)) := by
      rw [hrbp, hcx]; exact a2_vaddr' _ _ _ (Kn := 18446744073709551370) _ rfl (by omega)
    have ha0 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551368#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * (c - 3 - 1)) := by
      rw [hrbp, hcx]; exact a2_vaddr' _ _ _ (Kn := 18446744073709551368) _ rfl (by omega)
    have ha2 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551372#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * (c - 3 + 1)) := by
      rw [hrbp, hcx]; exact a2_vaddr' _ _ _ (Kn := 18446744073709551372) _ rfl (by omega)
    have hF1 : ∀ V, FrOk (wr fr (0x480 + 2 * (c - 3)) (Int.toBytes 2 V)) := fun V => by
      show List.length _ = _
      rw [wr_length (by rw [Int.toBytes_length]; omega), hF]
    have hl1 := a2_vk_load hm hF (o := 0x480) (i := c - 3) (by omega) ha1
    have hl0 := a2_vk_load hm hF (o := 0x480) (i := c - 3 - 1) (by omega) ha0
    have hl2 := fun V => a2_vk_load (a2_vk_store hm hF (by omega) ha1 V) (hF1 V) (o := 0x480)
      (i := c - 3 + 1) (by omega) ha2
    have hl1' := fun V => a2_vk_load (a2_vk_store hm hF (by omega) ha1 V) (hF1 V) (o := 0x480)
      (i := c - 3) (by omega) ha1
    have hm1 := fun V => a2_vk_store hm hF (o := 0x480) (i := c - 3) (by omega) ha1 V
    have hm2 := fun V W => a2_vk_store (a2_vk_store hm hF (by omega) ha1 V) (hF1 V) (o := 0x480)
      (i := c - 3 + 1) (by omega) ha2 W
    have hX1 : ∀ x, some x = some (Int.ofBytes (slice fr (0x480 + 2 * (c - 3)) 2)) →
        (BitVec.ofInt 16 x).toInt = A (c - 3) := fun x hx => by
      obtain rfl := Option.some.inj hx; exact hP.2.2.2.2 (c - 3) (by omega) (by omega)
    have hY0 : ∀ y, some y = some (Int.ofBytes (slice fr (0x480 + 2 * (c - 3 - 1)) 2)) →
        (BitVec.ofInt 16 y).toInt = ((A2.k1Of (k0N a row) k2 : Nat) : Int) + A2.ssum A (c - 3 - 1)
            :=
      fun y hy => by obtain rfl := Option.some.inj hy; exact hP.2.2.1 (c - 3 - 1) (by omega)
    have hz52 := a2_sub52 c (by omega)
    rw [← hcx] at hz52
    have hc52 : c ≠ 52 := by omega
    have hTA1 := fun V => a2_ta_wr (0x480 + 2 * (c - 3)) V hlen1 (by simp only [rb]; omega) hTA
    generalize hP' : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L289b]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some, a2_sw16_rl, a2_sw16_32]
    · rename_i hz
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, CondCode.interp_z,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, StatusFlags.zf_from_result, hz52] at hz
      exact absurd (of_decide_eq_true hz) hc52
    · rw [hl1]; rfl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L29cd.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
        hTA.1, hm⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
      edge_step
    · rw [hl0]; rfl
    · rw [hl1]; rfl
    · rw [hl2]; rfl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L29d3.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1 _,
        (hTA1 _).1, hm1 _⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
      edge_step
    · first | (rw [hl1']; rfl) | (rw [hl2]; rfl)
    · first | (rw [hl2]; rfl) | (rw [hl1']; rfl)
    · rename_i hz x1 hx1 af1 ht1 y0 hy0 x2 hx2 af2 ht2 y1 hy1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, a2_sw16_rl, a2_sw16_32, a2_cc_le_test16,
        decide_eq_false_iff_not, Int.not_le] at hx1 ht1 hy0 hx2 ht2 hy1
      rw [hl1] at hx1; rw [hl0] at hy0; rw [hl2] at hx2; rw [hl1'] at hy1
      have hX := hX1 _ hx1.symm
      have hP1 := a2_pfx_add_step hP (j := c - 3) (by omega) (by omega) hn1 hk1a hk1b
        (by omega) hlen1 _ _ hX (hY0 _ hy0.symm)
      have hF1' := hF1 (BitVec.ofInt 16 y0 + BitVec.ofInt 16 x1).toInt
      have hlen2 : 0x480 + 2 * (c - 3 + 1) + 2
          ≤ (wr fr (0x480 + 2 * (c - 3)) (Int.toBytes 2 (BitVec.ofInt 16 y0
            + BitVec.ofInt 16 x1).toInt)).length := by rw [hF1']; omega
      have hX2 : (BitVec.ofInt 16 x2).toInt = A (c - 3 + 1) := by
        obtain rfl := Option.some.inj hx2; exact hP1.2.2.2.2 (c - 3 + 1) (by omega) (by omega)
      have hY2 : (BitVec.ofInt 16 y1).toInt = ((A2.k1Of (k0N a row) k2 : Nat) : Int)
          + A2.ssum A (c - 3 + 1 - 1) := by
        obtain rfl := Option.some.inj hy1; rw [Nat.add_sub_cancel]
        exact hP1.2.2.1 (c - 3) (by omega)
      have hP2 := a2_pfx_add_step hP1 (j := c - 3 + 1) (by omega) (by omega) hn1 hk1a
        hk1b (by rw [← hX2]; omega) hlen2 _ _ hX2 hY2
      rw [show c - 3 + 1 + 1 = c - 1 by omega] at hP2
      have hF2 : FrOk (wr (wr fr (0x480 + 2 * (c - 3)) (Int.toBytes 2 (BitVec.ofInt 16 y0
          + BitVec.ofInt 16 x1).toInt)) (0x480 + 2 * (c - 3 + 1))
          (Int.toBytes 2 (BitVec.ofInt 16 y1 + BitVec.ofInt 16 x2).toInt)) := by
        show List.length _ = _
        rw [wr_length (by rw [Int.toBytes_length]; omega), hF1']
      have hlen1' : 0x480 + 2 * (c - 3) + 2 ≤ fr.length := hlen1
      have hI := a2_inc_wr2 (BitVec.ofInt 16 y1 + BitVec.ofInt 16 x2).toInt (by omega) (by omega)
        (a2_inc_wr2 (BitVec.ofInt 16 y0 + BitVec.ofInt 16 x1).toInt hlen1' (by omega) hInc0)
      have hT := a2_ta_wr _ (BitVec.ofInt 16 y1 + BitVec.ofInt 16 x2).toInt (by omega)
        (by simp only [rb]; omega) (hTA1 (BitVec.ofInt 16 y0 + BitVec.ofInt 16 x1).toInt)
      have h30' := (a2_slot64_wr _ _ 0x30 (BitVec.ofInt 16 y1 + BitVec.ofInt 16 x2).toInt
        (by omega) (by simp only [rb]; omega)).trans ((a2_slot64_wr fr _ 0x30
          (BitVec.ofInt 16 y0 + BitVec.ofInt 16 x1).toInt hlen1' (by simp only [rb]; omega)).trans
              h30)
      refine ⟨T.L28e7.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp,
        hfm, hF2, ⟨hk2v, hk1v, hlt, hI, hN0, hN1, ?_, ?_, ?_, vm, hT, h30', c, A, ?_, hc4, hc4le,
        hcn, hP2⟩, hm2 _ _⟩⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13, h15,
        hcx]

omit [CodeEnv] in
theorem a2_negn_sub2 (n c : Nat) (hn : n ≤ 64) (hc : c ≤ 64) :
    (BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 c - BitVec.setWidth 64 2#64 == BitVec.zero 64)
      = decide (c = n + 2) := by
  by_cases h : c = n + 2
  · subst h
    have : BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 (n + 2) - BitVec.setWidth 64 2#64
        = BitVec.zero 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth]
      simp; omega
    rw [this]; simp
  · have : BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 c - BitVec.setWidth 64 2#64
        ≠ BitVec.zero 64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_ofNat,
        BitVec.toNat_setWidth] at this
      simp at this; omega
    simp only [h, decide_false, beq_eq_false_iff_ne]; exact this

omit [CodeEnv] in
theorem a2_pfx_inc' {fr : List UInt8} {o n j : Nat} {B v0 tot : Int} {A : Nat → Int}
    (hP : A2.Pfx fr o n j B v0 tot A) (hj : j = n + 1) (v1 : Int) (h : v0 + tot = v1) :
    A2.Inc fr o n v0 v1 := by
  subst hj h; exact a2_pfx_inc hP

omit [CodeEnv] in
/-- The last prefix-sum step in a register: `Y + X = v0 + Σ_{l ≤ c} A l` as `int16`. -/
theorem a2_pfx_fin {fr : List UInt8} {o n c : Nat} {v0 tot : Int} {A : Nat → Int}
    (hP : A2.Pfx fr o n c 256 v0 tot A) (hc1 : 1 ≤ c) (hcn : c ≤ n) (hn : n ≤ 48)
    (hv0 : 0 ≤ v0) (hv1 : v0 ≤ 128) (X Y : BitVec 16) (hX : X.toInt = A c)
    (hY : Y.toInt = v0 + A2.ssum A (c - 1)) : Y + X = BitVec.ofInt 16 (v0 + A2.ssum A c) := by
  have hsb := a2_ssum_bound A n hP.1 (c - 1) (by omega)
  have hAc := hP.1 c hc1 hcn
  have hs : A2.ssum A c = A2.ssum A (c - 1) + A c := by
    obtain ⟨i, rfl⟩ : ∃ i, c = i + 1 := ⟨c - 1, by omega⟩
    simp [A2.ssum]
  have hsum := a2_add16 _ _ hY hX (by omega) (by omega)
  rw [hs, ← Int.add_assoc, ← hsum, BitVec.ofInt_toInt]

set_option maxRecDepth 100000 in
theorem blk_L28e7 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L28e7" ⟨"sbr_reset.L28e7", B.L28e7, some "sbr_reset.L292b"⟩ := by
  info_off
  measure_hb "L28e7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h13, h15, vm, hTA, h30, c, A, hcx, hc4, hc4le, hcn,
        hP⟩, hm⟩⟩ := T.L28e7.mp hs
    clear hs
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hn1e : A2.n1N e a (k0N a row) k2 % 2 = 0 := hN1.2.2
    have hk1 : A2.k1Of (k0N a row) k2 ≤ 128 := by simp only [A2.k1Of]; split <;> omega
    have hk1a : (0 : Int) ≤ ((A2.k1Of (k0N a row) k2 : Nat) : Int) := by omega
    have hk1b : ((A2.k1Of (k0N a row) k2 : Nat) : Int) ≤ 128 := by omega
    have hc50 : c ≤ 50 := by omega
    have hnd : ¬ c = A2.n1N e a (k0N a row) k2 + 2 → c ≤ A2.n1N e a (k0N a row) k2 :=
      fun h => by omega
    have hnd1 : ¬ c = A2.n1N e a (k0N a row) k2 + 2 → c - 1 ≤ A2.n1N e a (k0N a row) k2 :=
      fun h => by omega
    have hnd2 : ¬ c = A2.n1N e a (k0N a row) k2 + 2 → c - 1 + 1 ≤ A2.n1N e a (k0N a row) k2 :=
      fun h => by omega
    have hlen1 : 0x480 + 2 * (c - 1) + 2 ≤ fr.length := by rw [hF]; omega
    have ha1 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551374#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * (c - 1)) := by
      rw [hrbp, hcx]; exact a2_vaddr' _ _ _ (Kn := 18446744073709551374) _ rfl (by omega)
    have ha0 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551372#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * (c - 1 - 1)) := by
      rw [hrbp, hcx]; exact a2_vaddr' _ _ _ (Kn := 18446744073709551372) _ rfl (by omega)
    have ha2 : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551376#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * (c - 1 + 1)) := by
      rw [hrbp, hcx]; exact a2_vaddr' _ _ _ (Kn := 18446744073709551376) _ rfl (by omega)
    have hF1 : ∀ V, FrOk (wr fr (0x480 + 2 * (c - 1)) (Int.toBytes 2 V)) := fun V => by
      show List.length _ = _
      rw [wr_length (by rw [Int.toBytes_length]; omega), hF]
    have hl1 := a2_vk_load hm hF (o := 0x480) (i := c - 1) (by omega) ha1
    have hl0 := a2_vk_load hm hF (o := 0x480) (i := c - 1 - 1) (by omega) ha0
    have hl2 := fun V => a2_vk_load (a2_vk_store hm hF (by omega) ha1 V) (hF1 V) (o := 0x480)
      (i := c - 1 + 1) (by omega) ha2
    have hl1' := fun V => a2_vk_load (a2_vk_store hm hF (by omega) ha1 V) (hF1 V) (o := 0x480)
      (i := c - 1) (by omega) ha1
    have hm1 := fun V => a2_vk_store hm hF (o := 0x480) (i := c - 1) (by omega) ha1 V
    have hX1 : c ≤ A2.n1N e a (k0N a row) k2 →
        ∀ x, some x = some (Int.ofBytes (slice fr (0x480 + 2 * (c - 1)) 2)) →
        (BitVec.ofInt 16 x).toInt = A (c - 1) := fun hcn' x hx => by
      obtain rfl := Option.some.inj hx; exact hP.2.2.2.2 (c - 1) (by omega) (by omega)
    have hY0 : ∀ y, some y = some (Int.ofBytes (slice fr (0x480 + 2 * (c - 1 - 1)) 2)) →
        (BitVec.ofInt 16 y).toInt = ((A2.k1Of (k0N a row) k2 : Nat) : Int) + A2.ssum A (c - 1 - 1)
            :=
      fun y hy => by obtain rfl := Option.some.inj hy; exact hP.2.2.1 (c - 1 - 1) (by omega)
    have hzz := a2_negn_sub2 (A2.n1N e a (k0N a row) k2) c (by omega) (by omega)
    rw [← h15, ← hcx] at hzz
    have hI0 := fun V => a2_inc_wr2 (p := 0x480 + 2 * (c - 1)) V hlen1 (by omega) hInc0
    have hTA1 := fun V => a2_ta_wr (0x480 + 2 * (c - 1)) V hlen1 (by simp only [rb]; omega) hTA
    generalize hP' : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L28e7]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some, a2_sw16_rl, a2_sw16_32]
    · rename_i hz
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, CondCode.interp_z,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, StatusFlags.zf_from_result,
        AddrIndex.offset64_scale1, BitVec.add_zero, hzz, decide_eq_true_eq] at hz
      have hI1 := a2_pfx_inc' hP (by omega)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L2949.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _,
        hx, hsp, hfm, hF, ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, ?_, ?_, vm, hTA, h30, hI1 _
          (by rw [Int.add_comm, Int.sub_add_cancel])⟩, hm⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13]
      edge_step
    · rw [hl1]; rfl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L29d9.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, fr, hx, hsp, hfm, hF,
        hTA.1, hm⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
      edge_step
    · rw [hl0]; rfl
    · rw [hl1]; rfl
    · rw [hl2]; rfl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, T.L29dc.mpr ⟨row, hrow, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp, hfm, hF1 _,
        (hTA1 _).1, hm1 _⟩, ?_⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
      edge_step
    · rw [hl1']; rfl
    · rename_i hz x1 hx1 af1 ht1 y0 hy0 x2 hx2 af2 ht2 y1 hy1
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, a2_sw16_rl, a2_sw16_32, a2_cc_le_test16,
        decide_eq_false_iff_not, Int.not_le, CondCode.interp_z, StatusFlags.zf_from_result,
        hzz] at hz hx1 ht1 hy0 hx2 ht2 hy1
      have hcn' := hnd hz
      rw [hl1] at hx1; rw [hl0] at hy0; rw [hl2] at hx2; rw [hl1'] at hy1
      have hX := hX1 hcn' _ hx1.symm
      have hP1 := a2_pfx_add_step hP (j := c - 1) (by omega) (hnd1 hz) hn1 hk1a hk1b
        (by omega) hlen1 _ _ hX (hY0 _ hy0.symm)
      have hX2 : (BitVec.ofInt 16 x2).toInt = A c := by
        obtain rfl := Option.some.inj hx2
        rw [show c = c - 1 + 1 by omega]; exact hP1.2.2.2.2 (c - 1 + 1) (by omega) (hnd2 hz)
      have hY2 : (BitVec.ofInt 16 y1).toInt = ((A2.k1Of (k0N a row) k2 : Nat) : Int)
          + A2.ssum A (c - 1) := by
        obtain rfl := Option.some.inj hy1; exact hP1.2.2.1 (c - 1) (by omega)
      rw [show c - 1 + 1 = c by omega] at hP1
      have hax := a2_pfx_fin hP1 (by omega) hcn' hn1 hk1a hk1b _ _ hX2 hY2
      refine ⟨T.L292b.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx, hsp,
        hfm, hF1 _, ⟨hk2v, hk1v, hlt, hI0 _, hN0, hN1, ?_, ?_, ?_,
        vm, hTA1 _, (a2_slot64_wr fr _ 0x30 _ hlen1 (by simp only [rb]; omega)).trans h30, c, A,
        ?_, hc4, hc4le, hcn', hP1, by omega, ?_⟩, hm1 _⟩⟩, by var_step⟩
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13, h15,
        hcx, a2_sw16_rl, hax]

end Kraken.Examples.Sbr.Reset
