import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib
import Kraken.X64.Examples.Sbr.Parse.ResetA1Lib

/-!
# `sbr_reset`, shard A2: the prefix sums of `vk1` (`L287a` … `L292b`)

The loop turns the sorted differences `vk1[1 ..= n1]` (in `[-256, 256]`, summing to `k2 - k1`)
into `vk1[i] = k1 + Σ_{l ≤ i} vk1[l]`, 4× unrolled, failing (`A2.F`) on a non-positive entry.
`A2.Pfx fr 0x480 n1 j …` is the invariant after `j` entries; `a2_pfx_step` is one entry,
`a2_pfx_inc` the exit.
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
/-- A 2-byte frame write at entry `c` of the array at `o`: entry `c` is the written value,
the others are unchanged. -/
theorem a2_fv_wr (fr : List UInt8) (o c i : Nat) (v : Int) (h : o + 2 * c + 2 ≤ fr.length) :
    A2.fv (wr fr (o + 2 * c) (Int.toBytes 2 v)) o i
      = if i = c then (BitVec.ofInt 16 v).toInt else A2.fv fr o i := by
  have hl : (Int.toBytes 2 v).length = 2 := Int.toBytes_length 2 v
  unfold A2.fv
  split
  · subst_vars
    have := slice_wr_same (l := fr) (o := o + 2 * i) (v := Int.toBytes 2 v) (by rw [hl]; omega)
    rw [hl] at this
    rw [this, BitVec.ofInt_ofBytes_toBytes_eq 16 2 rfl]
  · rw [slice_wr_disj (by rw [hl]; omega) (by rw [hl]; omega)]

omit [CodeEnv] in
/-- A 2-byte write away from a window leaves the window. -/
theorem a2_slice_wr2 (fr : List UInt8) (p o n : Nat) (v : Int) (h : p + 2 ≤ fr.length)
    (hd : o + n ≤ p ∨ p + 2 ≤ o) :
    slice (wr fr p (Int.toBytes 2 v)) o n = slice fr o n := by
  have hl : (Int.toBytes 2 v).length = 2 := Int.toBytes_length 2 v
  exact slice_wr_disj (by rw [hl]; omega) (by rw [hl]; omega)

omit [CodeEnv] in
theorem a2_fv_wr2 (fr : List UInt8) (p o i : Nat) (v : Int) (h : p + 2 ≤ fr.length)
    (hd : o + 2 * i + 2 ≤ p ∨ p + 2 ≤ o + 2 * i) :
    A2.fv (wr fr p (Int.toBytes 2 v)) o i = A2.fv fr o i := by
  unfold A2.fv; rw [a2_slice_wr2 fr p _ _ v h hd]

omit [CodeEnv] in
theorem a2_inc_wr2 {fr : List UInt8} {p o n : Nat} {v0 v1 : Int} (v : Int) (h : p + 2 ≤ fr.length)
    (hd : o + 2 * n + 2 ≤ p ∨ p + 2 ≤ o) (hI : A2.Inc fr o n v0 v1) :
    A2.Inc (wr fr p (Int.toBytes 2 v)) o n v0 v1 := by
  obtain ⟨h0, h1, h2⟩ := hI
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [a2_fv_wr2 fr p o 0 v h (by omega)]; exact h0
  · rw [a2_fv_wr2 fr p o n v h (by omega)]; exact h1
  · rw [a2_fv_wr2 fr p o i v h (by omega), a2_fv_wr2 fr p o (i + 1) v h (by omega)]; exact h2 i hi

omit [CodeEnv] in
theorem a2_ssum_bound (A : Nat → Int) (n : Nat)
    (h : ∀ i, 1 ≤ i → i ≤ n → -256 ≤ A i ∧ A i ≤ 256) :
    ∀ j, j ≤ n → -(256 * (j : Int)) ≤ A2.ssum A j ∧ A2.ssum A j ≤ 256 * (j : Int) := by
  intro j
  induction j with
  | zero => intro _; simp [A2.ssum]
  | succ j ih =>
    intro hj
    have := ih (by omega)
    have := h (j + 1) (by omega) hj
    simp only [A2.ssum]
    push_cast
    omega

omit [CodeEnv] in
/-- One prefix-sum step at entry `c`: store `v0 + Σ_{l ≤ c} A l` (positive `A c`). -/
theorem a2_pfx_step {fr : List UInt8} {o n c : Nat} {B v0 tot : Int} {A : Nat → Int}
    (hP : A2.Pfx fr o n c B v0 tot A) (hc1 : 1 ≤ c) (hcn : c ≤ n) (hpos : 0 < A c)
    (hlen : o + 2 * c + 2 ≤ fr.length) (V : Int)
    (hV : (BitVec.ofInt 16 V).toInt = v0 + A2.ssum A c) :
    A2.Pfx (wr fr (o + 2 * c) (Int.toBytes 2 V)) o n (c + 1) B v0 tot A := by
  obtain ⟨hB, hs, hlt, hpos', hge⟩ := hP
  refine ⟨hB, hs, fun i hi => ?_, fun i h1 hi => ?_, fun i hi hin => ?_⟩
  · rw [a2_fv_wr fr o c i V hlen]
    split
    · subst_vars; exact hV
    · exact hlt i (by omega)
  · by_cases hic : i = c
    · subst hic; exact hpos
    · exact hpos' i h1 (by omega)
  · rw [a2_fv_wr fr o c i V hlen]
    split
    · omega
    · exact hge i (by omega) hin

omit [CodeEnv] in
/-- All prefix sums done: `vk[0 ..= n]` increases from `v0` to `v0 + tot`. -/
theorem a2_pfx_inc {fr : List UInt8} {o n : Nat} {B v0 tot : Int} {A : Nat → Int}
    (hP : A2.Pfx fr o n (n + 1) B v0 tot A) : A2.Inc fr o n v0 (v0 + tot) := by
  obtain ⟨_, hs, hlt, hpos, _⟩ := hP
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [hlt 0 (by omega)]; simp [A2.ssum]
  · rw [hlt n (by omega), hs]
  · rw [hlt i (by omega), hlt (i + 1) (by omega)]
    simp only [A2.ssum]
    have := hpos (i + 1) (by omega) (by omega)
    omega

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

/-- A 2-byte load of a frame array entry. -/
theorem a2_vk_load (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o i : Nat}
    (h : o + 2 * i + 2 ≤ 0x548) {addr : BitVec 64}
    (ha : addr = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (o + 2 * i)) :
    m.loadInt addr 2 = some (Int.ofBytes (slice fr (o + 2 * i) 2)) :=
  region_load (focus (Mm_fr ..) hm) ha (by rw [hF]; omega) (by rw [hF]; omega)

/-- A 2-byte store into a frame array entry. -/
theorem a2_vk_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr) {o i : Nat}
    (h : o + 2 * i + 2 ≤ 0x548) {addr : BitVec 64}
    (ha : addr = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (o + 2 * i)) (v : Int) :
    m.storeInt addr 2 v =⋆ Mm k e a ra t₀ st (wr fr (o + 2 * i) (Int.toBytes 2 v)) := by
  have h' := region_store (o := o + 2 * i) (n := 2) (focus (Mm_fr ..) hm) ha (by rw [hF]; omega)
    (by rw [hF]; omega) v
  rw [← Mm_upd_fr]; exact h'


omit [CodeEnv] in
theorem a2_slot64_wr (fr : List UInt8) (p d : Nat) (v : Int) (h : p + 2 ≤ fr.length)
    (hd : p + 2 ≤ rb d) : frSlot64 (wr fr p (Int.toBytes 2 v)) d = frSlot64 fr d := by
  unfold frSlot64; rw [a2_slice_wr2 fr p _ _ v h (Or.inr hd)]

omit [CodeEnv] in
theorem a2_slot32_wr (fr : List UInt8) (p d : Nat) (v : Int) (h : p + 2 ≤ fr.length)
    (hd : p + 2 ≤ rb d) : frSlot32 (wr fr p (Int.toBytes 2 v)) d = frSlot32 fr d := by
  unfold frSlot32; rw [a2_slice_wr2 fr p _ _ v h (Or.inr hd)]

omit [CodeEnv] in
theorem a2_ta_wr {fr : List UInt8} {t₀ : MachineData} {n0 : Nat} {vm : Int} (p : Nat) (v : Int)
    (h : p + 2 ≤ fr.length) (hd : p + 2 ≤ rb 0x88) (hT : A2.TA fr t₀ n0 vm) :
    A2.TA (wr fr p (Int.toBytes 2 v)) t₀ n0 vm := by
  obtain ⟨h1, h2, h3, h4⟩ := hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a2_slot64_wr fr p _ v h (by simp only [rb] at hd ⊢; omega)]; exact h1
  · rw [a2_slot64_wr fr p _ v h (by simp only [rb] at hd ⊢; omega)]; exact h2
  · rw [a2_slot64_wr fr p _ v h hd]; exact h3
  · rw [a2_slot32_wr fr p _ v h (by simp only [rb] at hd ⊢; omega)]; exact h4

omit [CodeEnv] in
theorem a2_negn_add (n c : Nat) (hn : n ≤ 64) (hc : c ≤ 64) :
    (BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 c == BitVec.zero 64) = decide (c = n) := by
  by_cases h : c = n
  · subst h
    have : BitVec.ofInt 64 (-(c : Int)) + BitVec.ofNat 64 c = BitVec.zero 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      simp; omega
    simp [this]
  · have : BitVec.ofInt 64 (-(n : Int)) + BitVec.ofNat 64 c ≠ BitVec.zero 64 := by
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat] at this
      simp at this; omega
    simp only [h, decide_false, beq_eq_false_iff_ne]; exact this

omit [CodeEnv] in
theorem a2_toInt16_small (x : Int) (h1 : -32768 ≤ x) (h2 : x < 32768) :
    (BitVec.ofInt 16 x).toInt = x := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod_def]; split <;> omega

set_option maxRecDepth 100000 in
theorem blk_L292b (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L292b" ⟨"sbr_reset.L292b", B.L292b, some "sbr_reset.L2949"⟩ := by
  info_off
  measure_hb "L292b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2v, hk1v, hlt, hInc0, hN0, hN1, h12, h13, h15, vm, hTA, h30, c, A, hcx, hc4, hc4le, hcn,
        hP, hAc, hax⟩, hm⟩⟩ := T.L292b.mp hs
    clear hs
    have hn1 : A2.n1N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n1I e a (k0N a row) k2).toNat ≤ 48
      have := hN1.2.1; omega
    have hn0 : A2.n0N e a (k0N a row) k2 ≤ 48 := by
      show (A2.n0I e a (k0N a row) k2).toNat ≤ 48
      have := hN0.2.1; omega
    have hn1e : A2.n1N e a (k0N a row) k2 % 2 = 0 := hN1.2.2
    have hk1 : A2.k1Of (k0N a row) k2 ≤ 128 := by simp only [A2.k1Of]; split <;> omega
    have hlen : 0x480 + 2 * c + 2 ≤ fr.length := by rw [hF]; omega
    have hsb := a2_ssum_bound A (A2.n1N e a (k0N a row) k2) hP.1 c hcn
    have hV : (BitVec.ofInt 16 (BitVec.setWidth 16 (s₀.regs.get64 .rax)).toInt).toInt
        = ((A2.k1Of (k0N a row) k2 : Nat) : Int) + A2.ssum A c := by
      rw [BitVec.ofInt_toInt, hax, a2_toInt16_small _ (by omega) (by omega)]
    have hP2 := a2_pfx_step hP (by omega) hcn hAc hlen _ hV
    have ha : s₀.regs.get64 .rbp + s₀.regs.get64 .rcx * 2#64 + 18446744073709551376#64
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (0x480 + 2 * c) := by
      rw [hrbp, hcx]; bv_omega
    have hm2 := a2_vk_store hm hF (o := 0x480) (i := c) (by omega) ha
      (BitVec.setWidth 16 (s₀.regs.get64 .rax)).toInt
    have hld := a2_vk_load hm hF (o := 0x480) (i := c) (by omega) ha
    have hz : ∀ y : BitVec 64, BitVec.setWidth 64 4#64 + y - BitVec.setWidth 64 4#64 = y :=
      fun y => by simp only [show BitVec.setWidth 64 4#64 = 4#64 from rfl]; bv_omega
    have hzz := a2_negn_add (A2.n1N e a (k0N a row) k2) c (by omega) (by omega)
    rw [← h15, ← hcx] at hzz
    have hFr : (wr fr (0x480 + 2 * c) (Int.toBytes 2 (BitVec.setWidth 16 (s₀.regs.get64 .rax)).toInt)).length = 0x548 := by
      rw [wr_length (by rw [Int.toBytes_length]; omega), hF]
    have hI0 := a2_inc_wr2 (BitVec.setWidth 16 (s₀.regs.get64 .rax)).toInt hlen (by omega) hInc0
    have hTA' := a2_ta_wr (0x480 + 2 * c) (BitVec.setWidth 16 (s₀.regs.get64 .rax)).toInt hlen
      (by simp only [rb]; omega) hTA
    have h30' : frSlot64 (wr fr (0x480 + 2 * c) (Int.toBytes 2 (BitVec.setWidth 16 (s₀.regs.get64 .rax)).toInt)) 0x30
        = BitVec.ofNat 64 (A2.n1N e a (k0N a row) k2) := by
      rw [a2_slot64_wr fr _ 0x30 _ hlen (by simp only [rb]; omega)]; exact h30
    have hcx4 : BitVec.setWidth 64 4#64 + s₀.regs.get64 .rcx = BitVec.ofNat 64 (c + 4) := by
      rw [hcx]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hc2 : c ≠ A2.n1N e a (k0N a row) k2 → c + 4 ≤ A2.n1N e a (k0N a row) k2 + 2 :=
      fun h => by omega
    have hc64 : c + 4 ≤ 64 := by omega
    have hvar : ∀ s : MachineData, s.regs.get64 .rcx = BitVec.ofNat 64 (c + 4) →
        var "sbr_reset.L289b" s < var "sbr_reset.L292b" s₀ := fun s hs => by
      simp only [lex_var, hs, hcx]
      refine Kraken.lex_cons_lt_cons (by lex_len) ?_
      refine Kraken.lex_cons_lt_of_lt (by lex_len) ?_
      have h1 := congrArg BitVec.toNat hs
      have h2 := congrArg BitVec.toNat hcx
      simp only [BitVec.toNat_ofNat] at h1 h2
      omega
    generalize hP' : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L292b]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some, hz]
    · rw [hld]; rfl
    · rename_i hz'
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, hz, CondCode.interp_nz, StatusFlags.zf_from_result] at hz'
      rw [hzz] at hz'
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz'
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L289b.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx,
        hsp, hfm, hFr, ⟨hk2v, hk1v, hlt, hI0, hN0, hN1, ?_, ?_, ?_, vm, hTA', h30', c + 4, A, ?_,
          by omega, by omega, hc2 hz', by rw [show c + 4 - 3 = c + 1 by omega]; exact hP2⟩, hm2⟩⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13, h15]
      · exact hcx4
      · left; apply hvar
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hcx4
    · rename_i hz'
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, hz, CondCode.interp_nz, StatusFlags.zf_from_result] at hz'
      rw [hzz] at hz'
      simp only [Bool.not_eq_false', decide_eq_true_eq] at hz'
      subst hz'
      have hI1 := a2_pfx_inc hP2
      rw [show ((A2.k1Of (k0N a row) k2 : Nat) : Int) + ((k2 : Int) - ((A2.k1Of (k0N a row) k2 : Nat) : Int))
        = (k2 : Int) by omega] at hI1
      refine ⟨T.L2949.mpr ⟨row, k2, hrow, hk2, hk02, hkq, hu, ⟨hC, hB, ⟨?_, ?_⟩, st, _, hx,
        hsp, hfm, hFr, ⟨hk2v, hk1v, hlt, hI0, hN0, hN1, ?_, ?_, vm, hTA', h30', hI1⟩, hm2⟩⟩, by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12, h13, h15]

end Kraken.Examples.Sbr.Reset
