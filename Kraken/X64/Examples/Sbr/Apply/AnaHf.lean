import Kraken.InfoOff
import Kraken.Rules.HbOptApply
import Kraken.X64.Examples.Sbr.ApplyTable

/-! # `ff_aac_sbr_apply`: blocks of shard `AnaHf` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]


/-! ### AnaHf helper lemmas (apply-anahf) -/

omit [CodeEnv] in
/-- A call's share of the callees' area with a callee need `need ≤ 0x290 + k` (lf_gen: `0x30 + k`,
hf_inverse_filter: `0xa8`): the push slot, the callee's reservation, the rest below. -/
theorem call_res_n (k need : Nat) {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat)
    (hn : need ≤ 0x290 + k) (K : Mem 64 → Prop) :
    Reserve (0x298 + k) (r₀ - 0x1c8#64) ⋆ K
      = 8 ?@ (r₀ - 0x1c8#64 - 8#64) ⋆ (Reserve need (r₀ - 0x1c8#64 - 8#64)
        ⋆ ((0x290 + k - need) ?@ (r₀ - 0x1c8#64 - BitVec.ofNat 64 (0x298 + k)) ⋆ K)) := by
  have hr : 0x298 + k ≤ (r₀ - 0x1c8#64).toNat := by bv_omega
  generalize r₀ - 0x1c8#64 = r at hr ⊢
  rw [show 0x298 + k = 8 + (0x290 + k) by omega, Reserve_split 8 (0x290 + k) r (by omega),
    Reserve.excess need (0x290 + k) (r - BitVec.ofNat 64 8) hn (by bv_omega), BitVec.sub_sub_ofNat]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem foldl_add_sum (f : Nat → Nat) :
    ∀ (l : List Nat) (c : Nat), l.foldl (fun a i => a + f i) c = c + (l.map f).sum
  | [], c => by simp
  | i :: l, c => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, foldl_add_sum f l]; omega

omit [CodeEnv] in
theorem ps_zero (f : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun a i => a + f i) 0 = ((List.range' 0 (n - 0)).map f).sum := by
  rw [foldl_add_sum, List.range_eq_range', Nat.sub_zero, Nat.zero_add]

omit [CodeEnv] in
theorem ps_succ (f : Nat → Nat) (j n : Nat) (h : j < n) :
    ((List.range' j (n - j)).map f).sum = f j + ((List.range' (j + 1) (n - (j + 1))).map f).sum := by
  rw [show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ, List.map_cons, List.sum_cons]

omit [CodeEnv] in
theorem lt_of_mono (f : Nat → Nat) : ∀ (n : Nat), (∀ e, e < n → f e < f (e + 1)) → 1 ≤ n → f 0 < f n
  | 0, _, h => by omega
  | m + 1, h, _ => by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact h 0 (by omega)
    · exact Nat.lt_trans (lt_of_mono f m (fun e he => h e (by omega)) hm) (h m (by omega))

/-- The Ypos toggle keeps the invariant (channel 0). -/
theorem ApplyC_ypos0 {y : Args} {t : MachineData} (h : ApplyC y t) (p : Nat) (hp : p ≤ 1) :
    ApplyC { y with d0 := { y.d0 with ypos := p } } t := by
  unfold ApplyC SbrWF DWF at *
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd0, hd1, hps⟩, hL⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, a10, a11, a12, a13, a14, a15, a16⟩ := hd0
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, hp, a10, a11, a12, a13, a14, a15, a16⟩, hd1, hps⟩, hL⟩

/-- The Ypos toggle keeps the invariant (channel 1). -/
theorem ApplyC_ypos1 {y : Args} {t : MachineData} (h : ApplyC y t) (p : Nat) (hp : p ≤ 1) :
    ApplyC { y with d1 := { y.d1 with ypos := p } } t := by
  unfold ApplyC SbrWF DWF at *
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd0, hd1, hps⟩, hL⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -, a10, a11, a12, a13, a14, a15, a16⟩ := hd1
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hd0,
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, hp, a10, a11, a12, a13, a14, a15, a16⟩, hps⟩, hL⟩

omit [CodeEnv] in
theorem Keep_ypos0 {x y : Args} (h : x.Keep y) (p : Nat) :
    x.Keep { y with d0 := { y.d0 with ypos := p } } := h

omit [CodeEnv] in
theorem Keep_ypos1 {x y : Args} (h : x.Keep y) (p : Nat) :
    x.Keep { y with d1 := { y.d1 with ypos := p } } := h

omit [CodeEnv] in
/-- `test $0x1,%cl`'s ZF from the channel-0 bit of `rcx`. -/
theorem zf_test1 {f : StatusFlags.from_result.Remaining} (r : BitVec 64) (ch : Nat)
    (h : r.getLsbD 0 = decide (ch = 0)) :
    (StatusFlags.from_result (BitVec.setWidth 8 r &&& BitVec.setWidth 8 1#64) f).zf
      = decide (ch ≠ 0) := by
  have h1 : (BitVec.setWidth 8 r &&& BitVec.setWidth 8 1#64).toNat = r.toNat % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      Nat.and_one_is_mod]
    omega
  have h2 : r.getLsbD 0 = decide (r.toNat % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit_zero]
  simp only [StatusFlags.from_result]
  rw [h2] at h
  have h3 : ((BitVec.setWidth 8 r &&& BitVec.setWidth 8 1#64) == BitVec.zero 8)
      = decide (r.toNat % 2 = 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← h1]
    constructor
    · intro e; rw [e]; rfl
    · intro e; exact BitVec.eq_of_toNat_eq (by rw [e]; rfl)
  rw [h3]
  by_cases hc : ch = 0
  · subst hc; simp only [decide_true, decide_eq_true_eq] at h; simp only [ne_eq, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
  · simp only [hc, decide_false, decide_eq_false_iff_not] at h
    simp only [ne_eq, hc, not_false_eq_true, decide_true, decide_eq_true_eq]; omega

theorem ApplyC_ypos_le {y : Args} {t : MachineData} (h : ApplyC y t) (ch : Nat) : (y.d ch).ypos ≤ 1 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd0, hd1, -⟩, -⟩ := h
  unfold Args.d; split
  · exact hd0.2.2.2.2.2.2.2.2.1
  · exact hd1.2.2.2.2.2.2.2.2.1

omit [CodeEnv] in
/-- `n` bytes at offset `m` of a `len`-byte block. -/
theorem carve_at (a : BitVec 64) (len m n : Nat) (h : m + n ≤ len) (hw : len < 2 ^ 64) :
    len ?@ a = n ?@ (a + BitVec.ofNat 64 m)
      ⋆ (m ?@ a ⋆ (len - m - n) ?@ (a + BitVec.ofNat 64 m + BitVec.ofNat 64 n)) := by
  have e : (a + BitVec.ofNat 64 m - a).toNat = m := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have c := Mem.Block.carve (a := a) (b := a + BitVec.ofNat 64 m) (len := len) (n := n)
    (by rw [e]; exact h) (by omega)
  rw [e] at c
  exact c

omit [CodeEnv] in
theorem al32_add2 (a : BitVec 64) (c d : Nat) (ha : isAligned 32 a = true) (hc : c % 32 = 0)
    (hd : d % 32 = 0) : isAligned 32 (a + (BitVec.ofNat 64 c + BitVec.ofNat 64 d)) = true := by
  rw [← BitVec.add_assoc]
  exact isAligned_add (by decide) (isAligned_add (by decide) ha (by simp only [BitVec.toNat_ofNat]; omega))
    (by simp only [BitVec.toNat_ofNat]; omega)

omit [CodeEnv] in
theorem al32_add1 (a : BitVec 64) (c : Nat) (ha : isAligned 32 a = true) (hc : c % 32 = 0) :
    isAligned 32 (a + BitVec.ofNat 64 c) = true :=
  isAligned_add (by decide) ha (by simp only [BitVec.toNat_ofNat]; omega)

omit [CodeEnv] in
theorem al16_of_32 {a : BitVec 64} (h : isAligned 32 a = true) : isAligned 16 a = true := by
  simp only [isAligned, beq_iff_eq] at *; omega

omit [CodeEnv] in
theorem ana_r13_step (i : Nat) (hi : i < 32) :
    BitVec.ofNat 64 (128 * i) - 18446744073709551488#64 = BitVec.ofNat 64 (128 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ana_nz (i : Nat) (hi : i < 32)
    (hz : (!(BitVec.ofNat 64 (128 * i) - 18446744073709555584#64 == BitVec.zero 64)) = true) :
    i + 1 < 32 := by
  refine Classical.byContradiction fun h => ?_
  have h31 : i = 31 := by omega
  subst h31
  simp at hz

omit [CodeEnv] in
theorem ana_r15_step (a c : BitVec 64) (p i : Nat) :
    256#64 + (a + (c + BitVec.ofNat 64 (8192 * p + 256 * i)))
      = a + (c + BitVec.ofNat 64 (8192 * p + 256 * (i + 1))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem ana_t128 (j : Nat) (hj : j < 33) : (BitVec.ofNat 64 (128 * j)).toNat = 128 * j := by
  simp only [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem ypos_buf (p : Nat) (h : p ≤ 1) :
    (BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (p : Int)))).toNat % 18446744073709551616 % 4294967296 ≤ 1 := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.toNat_ofInt]; omega

omit [CodeEnv] in
theorem ypos_xor (p : Nat) (hp : p ≤ 1) :
    (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (p : Int))) ^^^ BitVec.setWidth 32 1#64))).toInt
      = ((1 - p : Nat) : Int) := by
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rfl

omit [CodeEnv] in
theorem ypos_xor_rax (p : Nat) (hp : p ≤ 1) :
    (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (p : Int))) ^^^ BitVec.setWidth 32 1#64)).toNat
      % 4294967296 = 1 - p := by
  rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rfl

omit [CodeEnv] in
theorem FnW_ypos0 (e : Env) (y : Args) (t : MachineData) (p : Nat) :
    FnW e { y with d0 := { y.d0 with ypos := p } } t = FnW e y t := rfl
omit [CodeEnv] in
theorem FnW_ypos1 (e : Env) (y : Args) (t : MachineData) (p : Nat) :
    FnW e { y with d1 := { y.d1 with ypos := p } } t = FnW e y t := rfl
omit [CodeEnv] in
theorem AcW_ypos0 (y : Args) (t : MachineData) (p : Nat) :
    AcW { y with d0 := { y.d0 with ypos := p } } t = AcW y t := rfl
omit [CodeEnv] in
theorem AcW_ypos1 (y : Args) (t : MachineData) (p : Nat) :
    AcW { y with d1 := { y.d1 with ypos := p } } t = AcW y t := rfl
omit [CodeEnv] in
theorem OutW_ypos0 (y : Args) (t : MachineData) (p : Nat) :
    OutW { y with d0 := { y.d0 with ypos := p } } t = OutW y t := rfl
omit [CodeEnv] in
theorem OutW_ypos1 (y : Args) (t : MachineData) (p : Nat) :
    OutW { y with d1 := { y.d1 with ypos := p } } t = OutW y t := rfl
omit [CodeEnv] in
theorem ScW_ypos0 (y : Args) (t : MachineData) (p : Nat) :
    ScW { y with d0 := { y.d0 with ypos := p } } t = ScW y t := rfl
omit [CodeEnv] in
theorem ScW_ypos1 (y : Args) (t : MachineData) (p : Nat) :
    ScW { y with d1 := { y.d1 with ypos := p } } t = ScW y t := rfl
omit [CodeEnv] in
theorem TabW_ypos0 (y : Args) (t : MachineData) (p : Nat) :
    TabW { y with d0 := { y.d0 with ypos := p } } t = TabW y t := rfl
omit [CodeEnv] in
theorem TabW_ypos1 (y : Args) (t : MachineData) (p : Nat) :
    TabW { y with d1 := { y.d1 with ypos := p } } t = TabW y t := rfl

omit [CodeEnv] in
theorem al16_rsp456 (a : BitVec 64) (h : isAligned 16 (a + 8#64) = true) :
    isAligned 16 (a - 456#64) = true := by
  simp only [isAligned, beq_iff_eq, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at *; omega

omit [CodeEnv] in
theorem k0_n (n : Nat) (h : n ≤ 32) :
    (BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int))).toNat % 4294967296 = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]; omega

omit [CodeEnv] in
theorem start_ne (v : BitVec 32) (h : (v - BitVec.setWidth 32 0#64 == BitVec.zero 32) = false) : v ≠ 0 := by
  intro hv; subst hv; simp at h

omit [CodeEnv] in
theorem k0_n2 (n : Nat) (h : n ≤ 32) :
    (BitVec.ofInt 32 (n : Int)).toNat % 18446744073709551616 % 4294967296 = n := by
  simp only [BitVec.toNat_ofInt]; omega

omit [CodeEnv] in
theorem list10 (l : List UInt8) (h : l.length = 10) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9, l = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9], _ => exact ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩

omit [CodeEnv] in
theorem byte_toNat (b : UInt8) : (BitVec.ofInt 8 (Int.ofBytes [b])).toNat = b.toNat := by
  have := b.toNat_lt
  simp only [Int.ofBytes_cons, Int.ofBytes, List.foldr, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem sub_off (a : BitVec 64) (c d : Nat) (h : d ≤ c) (hc : c < 2 ^ 64) :
    a + BitVec.ofNat 64 c - (a + BitVec.ofNat 64 d) = BitVec.ofNat 64 (c - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem cf_lt4 (v : BitVec 8) (h : v.toNat ≤ 3) :
    ((BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) - BitVec.setWidth 8 4#64).unsigned !=
      (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v))).unsigned
        - (BitVec.setWidth 8 4#64).unsigned) = true := by
  have hv : v = BitVec.ofNat 8 v.toNat := (BitVec.ofNat_toNat 8 v).symm
  generalize v.toNat = n at hv h
  subst hv
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
theorem nq_rax (n : Nat) (h : n ≤ 5) : BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem split10 (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : UInt8) :
    [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] =@ a
      = [b0] =@ a ⋆ ([b1, b2, b3, b4] =@ (a + 1#64) ⋆ ([b5] =@ (a + 5#64) ⋆ [b6, b7, b8, b9] =@ (a + 6#64))) := by
  rw [show [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] = [b0] ++ ([b1, b2, b3, b4] ++ ([b5] ++ [b6, b7, b8, b9]))
      from rfl,
    Mem.Val.append_eq [b0] _ a (a + 1#64) (by simp) (by simp),
    Mem.Val.append_eq [b1, b2, b3, b4] _ (a + 1#64) (a + 5#64) (by simp [BitVec.add_assoc]) (by simp),
    Mem.Val.append_eq [b5] _ (a + 5#64) (a + 6#64) (by simp [BitVec.add_assoc]) (by simp)]

omit [CodeEnv] in
theorem bw_off (L : BitVec 64) (b : UInt8) (h : b.toNat ≤ 3) :
    (L + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b]))) * 4#64 - L).toNat + 4
      ≤ 16 := by
  have e := byte_toNat b
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
  omega

omit [CodeEnv] in
theorem sext_n (n : Nat) (h : n ≤ 8) : BitVec.signExtend 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
theorem flag_ne (n : Nat) (h : n ≤ 8) (h1 : 1 ≤ n) :
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == BitVec.zero 64) = false := by
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
theorem zx32 (n : Nat) (h : n < 2 ^ 31) : BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem zf_np (n : Nat) (h : n ≤ 6) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int))) &&&
        BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int))) == BitVec.zero 32) = decide (n = 0) := by
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
theorem xz64 (a : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 32 a ^^^ BitVec.setWidth 32 a) = 0#64 := by
  simp

omit [CodeEnv] in
theorem byte_split (l : List UInt8) (a : BitVec 64) (j : Nat) (hj : j < l.length) (hw : l.length ≤ 2 ^ 64) :
    l =@ a = l.take j =@ a ⋆ ([l.getD j 0] =@ (a + BitVec.ofNat 64 j) ⋆
      l.drop (j + 1) =@ (a + BitVec.ofNat 64 j + 1#64)) := by
  have e : l = l.take j ++ ([l.getD j 0] ++ l.drop (j + 1)) := by
    have h1 := (List.take_append_drop j l).symm
    rw [List.drop_eq_getElem_cons hj] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]; exact h1
  have hl : (l.take j).length = j := by simp only [List.length_take]; omega
  rw [show (l =@ a) = ((l.take j ++ ([l.getD j 0] ++ l.drop (j + 1))) =@ a) from by rw [← e]]
  rw [Mem.Val.append_eq (l.take j) _ a (a + BitVec.ofNat 64 j) (by rw [hl])
      (by simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, List.length_drop]; omega),
    Mem.Val.append_eq [l.getD j 0] _ (a + BitVec.ofNat 64 j) (a + BitVec.ofNat 64 j + 1#64) (by simp)
      (by simp only [List.length_cons, List.length_nil, List.length_drop]; omega)]

omit [CodeEnv] in
theorem sx_kk (kk : Nat) (h : kk < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 kk)) = BitVec.ofNat 64 kk := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

omit [CodeEnv] in
theorem zf_byte (b : UInt8) :
    ((BitVec.ofInt 8 (Int.ofBytes [b]) - BitVec.setWidth 8 0#64) == BitVec.zero 8) = decide (b.toNat = 0) := by
  have h := byte_toNat b
  rw [show BitVec.setWidth 8 0#64 = 0#8 from rfl, BitVec.sub_zero]
  generalize BitVec.ofInt 8 (Int.ofBytes [b]) = v at h
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro hv; rw [hv] at h; simp at h; omega
  · intro hb; apply BitVec.eq_of_toNat_eq; rw [h, hb]; rfl

omit [CodeEnv] in
theorem cf_sub64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((BitVec.ofNat 64 a - BitVec.ofNat 64 b).unsigned != (BitVec.ofNat 64 a).unsigned - (BitVec.ofNat 64 b).unsigned)
      = decide (a < b) := by
  rw [BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [decide_eq_true h, bne_iff_ne]; omega
  · rw [decide_eq_false h, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
theorem zf_sub64 (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == BitVec.zero 64) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl, BitVec.sub_self]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h2
    have h3 := congrArg BitVec.toNat h2
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3
    have h4 : (BitVec.zero 64).toNat = 0 := rfl
    omega

omit [CodeEnv] in
theorem ofNat_succ64 (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem zx_ofNat (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem cf_sub32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    ((BitVec.ofNat 32 a - BitVec.ofNat 32 b).unsigned != (BitVec.ofNat 32 a).unsigned - (BitVec.ofNat 32 b).unsigned)
      = decide (a < b) := by
  rw [BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [decide_eq_true h, bne_iff_ne]; omega
  · rw [decide_eq_false h, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
theorem zf_sub32 (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 32 a - BitVec.ofNat 32 b == BitVec.zero 32) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl, BitVec.sub_self]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h2
    have h3 := congrArg BitVec.toNat h2
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3
    have h4 : (BitVec.zero 32).toNat = 0 := rfl
    omega

omit [CodeEnv] in
theorem sw32 (n : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem zx_byte (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b]))) = BitVec.ofNat 64 b.toNat := by
  have h := byte_toNat b
  have := b.toNat_lt
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]; omega

omit [CodeEnv] in
theorem zx32n (n : Nat) (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem word_split (l : List UInt8) (a : BitVec 64) (i : Nat) (hj : 2 * i + 2 ≤ l.length) (hw : l.length ≤ 2 ^ 64) :
    l =@ a = l.take (2 * i) =@ a ⋆ ([l.getD (2 * i) 0, l.getD (2 * i + 1) 0] =@ (a + BitVec.ofNat 64 (2 * i)) ⋆
      l.drop (2 * i + 2) =@ (a + BitVec.ofNat 64 (2 * i) + 2#64)) := by
  have e : l = l.take (2 * i) ++ ([l.getD (2 * i) 0, l.getD (2 * i + 1) 0] ++ l.drop (2 * i + 2)) := by
    have h1 := (List.take_append_drop (2 * i) l).symm
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact h1
  have hl : (l.take (2 * i)).length = 2 * i := by simp only [List.length_take]; omega
  rw [show (l =@ a) = ((l.take (2 * i) ++ ([l.getD (2 * i) 0, l.getD (2 * i + 1) 0] ++ l.drop (2 * i + 2))) =@ a)
    from by rw [← e]]
  rw [Mem.Val.append_eq (l.take (2 * i)) _ a (a + BitVec.ofNat 64 (2 * i)) (by rw [hl])
      (by simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, List.length_drop]; omega),
    Mem.Val.append_eq [l.getD (2 * i) 0, l.getD (2 * i + 1) 0] _ (a + BitVec.ofNat 64 (2 * i))
      (a + BitVec.ofNat 64 (2 * i) + 2#64) (by simp)
      (by simp only [List.length_cons, List.length_nil, List.length_drop]; omega)]

omit [CodeEnv] in
theorem le_test6 (g : Nat) (h : g ≤ 6) (a : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 32 (BitVec.ofNat 64 g) &&&
      BitVec.setWidth 32 (BitVec.ofNat 64 g)) { cf := false, af := a, of := false }) = decide (g = 0) := by
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
theorem add32 (a b : Nat) (h : a + b < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 a) + BitVec.setWidth 32 (BitVec.ofNat 64 b))
      = BitVec.ofNat 64 (b + a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem dec32 (g : Nat) (h1 : 1 ≤ g) (h : g < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 g) - 1#32) = BitVec.ofNat 64 (g - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem shl320 (n : Nat) (h : n < 2 ^ 50) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 4#64) <<< 6 = BitVec.ofNat 64 (320 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
theorem sub32z (a b : Nat) (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 a - BitVec.ofNat 32 b) = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem sw_byte32 (b : UInt8) : BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b])) = BitVec.ofNat 32 b.toNat := by
  have h := byte_toNat b
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]

omit [CodeEnv] in
theorem shl320b (n : Nat) (h : n < 2 ^ 50) :
    BitVec.ofNat 64 n <<< 6 + (BitVec.ofNat 64 n <<< 6) * 4#64 = BitVec.ofNat 64 (320 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
theorem sub_add_lit (a b c : BitVec 64) : a + b - (a + c) = b - c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add]
  omega

omit [CodeEnv] in
theorem take_getD' (l : List UInt8) (n i : Nat) (h : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, h, ite_true]

omit [CodeEnv] in
theorem add_sub_self' (a b : BitVec 64) : a + b - a = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add]
  omega

omit [CodeEnv] in
theorem cf_sub8 (a b : Nat) (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    ((BitVec.ofNat 8 a - BitVec.ofNat 8 b).unsigned != (BitVec.ofNat 8 a).unsigned - (BitVec.ofNat 8 b).unsigned)
      = decide (a < b) := by
  rw [BitVec.unsigned_eq, BitVec.unsigned_eq, BitVec.unsigned_eq]
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  by_cases h : a < b
  · rw [decide_eq_true h, bne_iff_ne]; omega
  · rw [decide_eq_false h, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
theorem zf_sub8 (a b : Nat) (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    (BitVec.ofNat 8 a - BitVec.ofNat 8 b == BitVec.zero 8) = decide (a = b) := by
  by_cases h : a = b
  · subst h; rw [decide_eq_true rfl, BitVec.sub_self]; rfl
  · rw [decide_eq_false h, beq_eq_false_iff_ne]
    intro h2
    have h3 := congrArg BitVec.toNat h2
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h3
    have h4 : (BitVec.zero 8).toNat = 0 := rfl
    omega

omit [CodeEnv] in
theorem sw8b (b : UInt8) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b]))))
      = BitVec.ofNat 8 b.toNat := by
  have h := byte_toNat b
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h]; omega

omit [CodeEnv] in
theorem sw8_3 : BitVec.setWidth 8 3#64 = BitVec.ofNat 8 3 := rfl

omit [CodeEnv] in
theorem bw_off8 (b : UInt8) (hb : b.toNat ≤ 3) : (BitVec.ofNat 64 b.toNat * 4#64).toNat + 4 ≤ 16 := by
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem g4off (g : Nat) (h : g ≤ 4) : 0 + g * 4 + 4 ≤ 20 := by omega

omit [CodeEnv] in
/-- The 20-byte `bw_array` block and the first 4 bytes of the next (`W` at `+0x3920`) as one
24-byte block. Unused: L7bb3_1 reads `bw_array[g]` with `g ≤ n_q - 1 ≤ 4` (M4-F1, closed by the
`TabWF` facts F1–F5), inside `bw_array[5]`; kept from before that bound was proved. -/
theorem bw_merge (d : BitVec 64) (K : Mem 64 → Prop) :
    20 ?@ (d + 0x390c#64) ⋆ (16384 ?@ (d + 0x3920#64) ⋆ K)
      = 24 ?@ (d + 0x390c#64) ⋆ (16380 ?@ (d + 0x3924#64) ⋆ K) := by
  have e1 := Block.split (d + 0x390c#64) 20 4 (by decide)
  have e2 := Block.split (d + 0x3920#64) 4 16380 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2
  rw [e1, e2]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem g5off (g : Nat) (h : g ≤ 5) : 0 + g * 4 + 4 ≤ 24 := by omega

omit [CodeEnv] in
theorem sx_small (r : BitVec 32) (n : Nat) (h : r.toNat = n) (hn : n < 2 ^ 31) :
    r.signExtend 64 = BitVec.ofNat 64 n := by
  have hm : r.msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
/-- `t_env[0]` and `t_env[ne]` as one-byte cells (L7bb3_1). -/
theorem te_split (l : List UInt8) (a : BitVec 64) (ne : Nat) (h1 : 0 < ne) (h2 : ne < l.length)
    (hw : l.length ≤ 2 ^ 64) :
    l =@ a = ((l.take ne).take 0 =@ a ⋆ ([l.getD 0 0] =@ a ⋆ (l.take ne).drop (0 + 1) =@ (a + 1#64)))
      ⋆ ([l.getD ne 0] =@ (a + BitVec.ofNat 64 ne) ⋆ l.drop (ne + 1) =@ (a + BitVec.ofNat 64 ne + 1#64)) := by
  rw [byte_split l a ne h2 hw, byte_split (l.take ne) a 0 (by simp only [List.length_take]; omega)
    (by simp only [List.length_take]; omega), take_getD' l ne 0 h1]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]

omit [CodeEnv] in
theorem te2x (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b]))))
      + BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes [b])))))
      = BitVec.ofNat 64 (2 * b.toNat) := by
  have h := byte_toNat b
  have hb := b.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, h]
  omega

omit [CodeEnv] in
theorem sx2 (n : Nat) (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n :=
  sx_small _ n (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega) h

/-! hf_gen call (L7bb3_1) -/

omit [CodeEnv] in
theorem hg_sz (a b : Nat) (hab : a ≤ b) (hb : b < 2 ^ 40) :
    ((BitVec.ofNat 64 (2 * b) - BitVec.ofNat 64 (2 * a)) * 8#64).toNat = 16 * (b - a) := by
  simp only [BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

omit [CodeEnv] in
theorem hg_even (a b : Nat) :
    (BitVec.ofNat 64 (2 * b) - BitVec.ofNat 64 (2 * a)).toNat % 2 = 0 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow]
  omega

omit [CodeEnv] in
theorem hg_lt (a b : Nat) (hab : a < b) (hb : b < 2 ^ 20) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 (2 * a))).toInt < (BitVec.setWidth 32 (BitVec.ofNat 64 (2 * b))).toInt := by
  rw [BitVec.toInt_eq_toNat_of_msb, BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

omit [CodeEnv] in
theorem hg_xh (r c : BitVec 64) (u a : Nat) :
    r + (c + (BitVec.ofNat 64 u + (16#64 + BitVec.ofNat 64 (2 * a) * 8#64)))
      = r + (c + BitVec.ofNat 64 (u + 16 + 16 * a)) := by
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

omit [CodeEnv] in
theorem hg_xl (r c : BitVec 64) (u a : Nat) :
    r + (c + BitVec.ofNat 64 (u + 16 + 16 * a)) - 16#64 = r + (c + BitVec.ofNat 64 (u + 16 * a)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

omit [CodeEnv] in
theorem hg_m8 (p : Nat) : BitVec.ofNat 64 p * 8#64 = BitVec.ofNat 64 (8 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  omega

omit [CodeEnv] in
theorem hg_al (r c : BitVec 64) (N : Nat) (hr : isAligned 32 r = true) (hc : c.toNat % 16 = 0)
    (hN : N % 16 = 0) : isAligned 16 (r + (c + BitVec.ofNat 64 N)) = true := by
  rw [← BitVec.add_assoc]
  have hr' : isAligned 16 r = true := by simp only [isAligned, beq_iff_eq] at *; omega
  exact isAligned_add (by decide) (isAligned_add (by decide) hr' hc)
    (by simp only [BitVec.toNat_ofNat]; omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682" ⟨"ff_aac_sbr_apply.L7682", B.L7682, some "ff_aac_sbr_apply.L7682_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, hC, ⟨hrsp, hrbp⟩, hch, h9, h12, hdx, hcx, y, hK, hCy, hm⟩ := T.L7682.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  simp only [Mm, ApplyF, AcW, FrL, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm h12
  dsimp only
  simp only [B.L7682]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_1]
                 refine ⟨ch, hC, ⟨?_, ?_⟩, hch, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h12, hdx, hcx, sbrA, arg1, BitVec.add_assoc] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (simp only [Mm, ApplyF, AcW, FrAn1, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd]; rw [← hfd]; sep_close hm)
  all_goals try var_step
  all_goals try (simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_1" ⟨"ff_aac_sbr_apply.L7682_1", B.L7682_1, some "ff_aac_sbr_apply.L7682_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, hC, ⟨hrsp, hrbp⟩, hch, h9, h12, hdx, hcx, h14, y, hK, hCy, hm⟩ := T.L7682_1.mp hs
  clear hs
  have hfd := hK.1.2.2.2.2.2.1
  simp only [Mm, ApplyF, FnW, FrAn1, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm h12
  dsimp only
  simp only [B.L7682_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_2]
                 refine ⟨ch, hC, ⟨?_, ?_⟩, hch, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h12, hdx, hcx, h14, sbrA, arg1, BitVec.add_assoc] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (simp only [Mm, ApplyF, FnW, FrA2, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd]; rw [← hfd]; sep_close hm)
  all_goals try var_step
  all_goals try (simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_2" ⟨"ff_aac_sbr_apply.L7682_2", B.L7682_2, some "ff_aac_sbr_apply.L7682_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, hC, ⟨hrsp, hrbp⟩, hch, h9, h12, hdx, hcx, h14, y, hK, hCy, hm⟩ := T.L7682_2.mp hs
  clear hs
  have hfd := hK.1.2.2.2.2.2.1
  simp only [Mm, ApplyF, FnW, FrA2, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm h12
  dsimp only
  simp only [B.L7682_2]
  obtain ⟨c0, hc0⟩ : ∃ c0, BitVec.setWidth 32 (s₀.regs.get64 .rcx) = c0 := ⟨_, rfl⟩
  have hc0b : c0.getLsbD 0 = decide (ch = 0) := by
    rw [← hc0, BitVec.getLsbD_setWidth, hcx]; rfl
  have hc0' := PLift.up hc0
  clear hc0
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_3]
                 refine ⟨ch, c0, hC, ⟨?_, ?_⟩, hch, hc0b, ?_, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
  all_goals try (exact zf_test1 _ _ hcx)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h12, hdx, hcx, h14, sbrA, arg1, BitVec.add_assoc, hc0'.down] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (simp only [Mm, ApplyF, FnW, FrA3, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd]; sep_close hm)
  all_goals try var_step
  all_goals try (simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_3" ⟨"ff_aac_sbr_apply.L7682_3", B.L7682_3, some "ff_aac_sbr_apply.L7682_4"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h9, h14, hdx, hzf, y, hK, hCy, hm⟩ := T.L7682_3.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA3, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    dsimp only
    simp only [B.L7682_3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_4]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h14, hdx, hzf,
        sbrA, arg1, BitVec.add_assoc, decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true,
        Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64, CondCode.interp, Bool.not_false, Bool.not_true,
        BitVec.setWidth_eq, BitVec.zero_mul, BitVec.one_mul] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_mem hm
    all_goals try (simp only [Mm, ApplyF, FrA4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, Nat.reduceMul, BitVec.ofNat_eq_ofNat]; sep_close hm)
    all_goals try var_step
  all_goals try (simp -implicitDefEqProofs only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod]; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_4" ⟨"ff_aac_sbr_apply.L7682_4", B.L7682_4, some "ff_aac_sbr_apply.L7682_5"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h9, h14, h13, y, hK, hCy, hm⟩ := T.L7682_4.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
  simp only [lex_var, hsl] at hn
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    dsimp only
    simp only [B.L7682_4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_5]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h14, h13, dA, ↓reduceIte,
        sbrA, arg1, BitVec.add_assoc, decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true,
        Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64, CondCode.interp, Bool.not_false, Bool.not_true,
        BitVec.setWidth_eq, BitVec.zero_mul, BitVec.one_mul] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_mem hm
    all_goals try (simp only [Mm, ApplyF, FrA5, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.zero_ne_one, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢)
    all_goals try sep_close hm
    all_goals try (rw [← BitVec.add_assoc, BitVec.add_comm (9344#64), BitVec.add_assoc]; simp only [BitVec.reduceAdd]; done)
    all_goals try var_step
  all_goals try (simp -implicitDefEqProofs only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod]; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_5 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_5" ⟨"ff_aac_sbr_apply.L7682_5", B.L7682_5, some "ff_aac_sbr_apply.L7682_6"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMc, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h9, h14, h13, hcx, hdi, y, hK, hCy, hm⟩ := T.L7682_5.mp hs
  clear hs
  have hyp := ApplyC_ypos_le hCy ch
  simp only [Mm, ApplyF, FrA5, DArrW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hcx
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  -- memcpy(x, x + 0x1000, 0x480) inside the analysis block (d + 0x2480, 5248)
  obtain ⟨H, hH⟩ := Block.carve2_ex (a := dA t₀ ch + 0x2480#64) (b₁ := dA t₀ ch + 0x2480#64)
    (b₂ := dA t₀ ch + 0x3480#64) (len := 5248) (n₁ := 1152) (n₂ := 1152)
    (by simp only [BitVec.sub_self, Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat,
          BitVec.toNat_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff])
    (by simp only [BitVec.sub_self, Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat,
          BitVec.toNat_zero, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff])
    (by decide)
  have hsx : ∀ p : Nat, p ≤ 1 → BitVec.signExtend 64 (BitVec.ofInt 32 (p : Int)) = BitVec.ofNat 64 p := by
    intro p hp; rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rfl
  have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
      a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
    intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hH hm
    rw [hH, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    simp only [DScW, Args.d, ↓reduceIte, Nat.one_ne_zero, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
      Nat.reduceMul, Nat.reduceAdd] at hm hyp
    first
      | have hyl : loadInt s₀.dmem (t₀.regs.get64 .rsi + 197312#64) 4 = some (y.d0.ypos : Int) := by
          sep_mem hm; rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by simp only [Nat.reduceMul, Nat.reducePow]; omega)]
      | have hyl : loadInt s₀.dmem (t₀.regs.get64 .rsi + 286080#64) 4 = some (y.d1.ypos : Int) := by
          sep_mem hm; rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by simp only [Nat.reduceMul, Nat.reducePow]; omega)]
    first
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          1152 ?@ (t₀.regs.get64 .rsi + 175648#64), 1152 ?@ (t₀.regs.get64 .rsi + 179744#64)] as Rc hRc
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          1152 ?@ (t₀.regs.get64 .rsi + 264416#64), 1152 ?@ (t₀.regs.get64 .rsi + 268512#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    dsimp only
    simp only [B.L7682_5]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen [MachineWP.call_proc_spec_at Rc "memcpy" hMc]
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    case vc1 =>
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
      simp only [hyl, Option.isSome_some]
    case vc2 =>
      rename_i v hv
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul] at hv
      rw [hyl, Option.some.injEq] at hv
      subst hv
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
      rotate_left 2
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
        sep_mem hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
        sep_mem hm
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth] at hpost
        obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hrsp'
        have e := hRc'.down
        subst e
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨?_, ?_⟩
        · rw [T.L7682_6]
          refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
          all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h13, h14, hcx, hdi,
          dA, sbrA, arg0, arg1, arg2, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, hbx', h12', h13', h14', h15', hsx _ hyp, Args.d, ↓reduceIte, Nat.one_ne_zero]; done)
          simp only [Mm, ApplyF, FrA5, DArrW, DScW, Blocks, Args.d, ↓reduceIte, Nat.one_ne_zero, dA, sbrA, arg0, arg1, arg3, arg4,
            BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]
          rw [hH, call_res k hSt]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_close hm'
        · simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_mem hm'
          simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
          var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_6 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_6" ⟨"ff_aac_sbr_apply.L7682_6", B.L7682_6, some "ff_aac_sbr_apply.L7682_7"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h12, hbx, h13, y, hK, hCy, h15, hm⟩ := T.L7682_6.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA5, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  dsimp only
  simp only [B.L7682_6]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682_7]
                 refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
      sbrA, arg1, BitVec.add_assoc, lex_var, slot64] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try (simp only [Mm, ApplyF, FrA6, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd] at hm ⊢)
  all_goals try sep_close hm
  all_goals try var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7682_7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_7" ⟨"ff_aac_sbr_apply.L7682_7", B.L7682_7, some "ff_aac_sbr_apply.L7682_8"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMc, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h12, hbx, h13, y, hK, hCy, h15, hm⟩ := T.L7682_7.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, DArrW, OutW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hds : 4096 ≤ 8192 >>> dsN y := by unfold dsN; split <;> decide
  -- memcpy(x + 0x480, L/R, 0x1000): the destination carved from the analysis block
  -- (d + 0x2480, 5248), the source from the output block (L or R, 8192 >>> dsN)
  have hD := Block.carve (a := dA t₀ ch + 0x2480#64) (b := dA t₀ ch + 0x2900#64) (len := 5248) (n := 4096)
    (by simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat,
          Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff])
    (by decide)
  have hL : ∀ a : BitVec 64, (8192 >>> dsN y) ?@ a
      = 4096 ?@ a ⋆ (0 ?@ a ⋆ (8192 >>> dsN y - 0 - 4096) ?@ (a + BitVec.ofNat 64 4096)) := by
    intro a
    have h := Block.carve (a := a) (b := a) (len := 8192 >>> dsN y) (n := 4096)
      (by simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; exact hds)
      (by unfold dsN; split <;> decide)
    simpa only [BitVec.sub_self, BitVec.toNat_zero] using h
  have hA : ∀ a c : BitVec 64, (10496#64) + (a + c) = a + (10496#64 + c) := by intro a c; ac_rfl
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hD hm
    rw [hD, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    first
      | (rw [hL (arg3 t₀)] at hm
         simp only [arg3, arg4] at hm
         have hm0 := hm
         sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          4096 ?@ (t₀.regs.get64 .rsi + 176800#64), 4096 ?@ t₀.regs.get64 .rcx] as Rc hRc)
      | (rw [hL (arg4 t₀)] at hm
         simp only [arg3, arg4] at hm
         have hm0 := hm
         sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          4096 ?@ (t₀.regs.get64 .rsi + 265568#64), 4096 ?@ t₀.regs.get64 .r8] as Rc hRc)
    have hRc' := PLift.up hRc
    clear hRc
    dsimp only
    simp only [B.L7682_7]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen [MachineWP.call_proc_spec_at Rc "memcpy" hMc]
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    case vc1 =>
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
      sep_mem hm0
    case vc2 =>
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul] at *
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
      sep_vals hm0
      try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, ↓reduceIte, Nat.one_ne_zero] at *
      sep_mem hm0
    case vc3 =>
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul] at *
      try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
      sep_vals hm0
      try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, ↓reduceIte, Nat.one_ne_zero] at *
      sep_vals hm0
      try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
      try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, ↓reduceIte, Nat.one_ne_zero] at *
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
      rotate_left 2
      · try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul]
        sep_mem hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
        sep_mem hm
        try (rw [hA]; simp only [BitVec.reduceAdd])
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, Blocks, BitVec.toNat_ofNat, BitVec.toNat_setWidth] at hpost
        obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        try (rw [hA] at hm'; simp only [BitVec.reduceAdd] at hm')
        try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hrsp'
        have e := hRc'.down
        subst e
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨?_, ?_⟩
        · rw [T.L7682_8]
          refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
          all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          dA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc, BitVec.setWidth_eq, BitVec.zero_mul, hbx', h12', h13', h14', h15', Args.d, ↓reduceIte, Nat.one_ne_zero]; done)
          simp only [Mm, ApplyF, FrA6, DArrW, OutW, Blocks, ↓reduceIte, Nat.one_ne_zero, dA, sbrA, arg0, arg1,
            BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]
          rw [hD, call_res k hSt]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
          simp only [ite_true, ite_false, ↓reduceIte, Nat.one_ne_zero, dsN] at hm'
          first
            | (rw [hL (arg3 t₀)]; simp only [arg3, arg4, dsN]; sep_close hm')
            | (rw [hL (arg4 t₀)]; simp only [arg3, arg4, dsN]; sep_close hm')
        · try simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_mem hm'
          simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
          var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7682_8 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7682_8" ⟨"ff_aac_sbr_apply.L7682_8", B.L7682_8, some "ff_aac_sbr_apply.L7750"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h12, hbx, y, hK, hCy, h15, hm⟩ := T.L7682_8.mp hs
  clear hs
  have hyp := ApplyC_ypos_le hCy ch
  simp only [Mm, ApplyF, FrA6, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hsh : ∀ p : Nat, p ≤ 1 → BitVec.ofNat 64 p <<< 13 = BitVec.ofNat 64 (8192 * p + 0) := by
    intro p hp; rcases (by omega : p = 0 ∨ p = 1) with rfl | rfl <;> rfl
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    dsimp only
    simp only [B.L7682_8]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7750]
                   refine ⟨_, c0, 0, hC, ⟨?_, ?_⟩, hch, hc0, by decide, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h14, h15, hbx, dA, ↓reduceIte,
        sbrA, arg1, BitVec.add_assoc, Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64,
        BitVec.setWidth_eq, BitVec.zero_mul, BitVec.one_mul, Args.d, BitVec.toNat_ofNat, Nat.reduceEqDiff,
        BitVec.xor_self, BitVec.setWidth_zero, BitVec.toNat_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try sep_mem hm
    all_goals try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try (simp only [Mm, ApplyF, FrA6, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd] at hm ⊢)
    all_goals try sep_close hm
    all_goals try (rw [hsh _ hyp]; try simp only [BitVec.add_assoc])
    all_goals try simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero, Nat.reduceSub]
    all_goals try var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7750 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750" ⟨"ff_aac_sbr_apply.L7750", B.L7750, some "ff_aac_sbr_apply.L7750_1"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.1
  have hpd : isAligned 32 (lab "pd_reverse") = true := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, DArrW, ArrW, CstW, FnW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal
  simp only [hfd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  have hX := carve_at (dA t₀ ch + 0x2480#64) 5248 (128 * i) 1280 (by omega) (by decide)
  have hax : isAligned 32 (dA t₀ ch + 0x2480#64 + BitVec.ofNat 64 (128 * i)) = true :=
    isAligned_add (by decide) (isAligned_add (by decide) (isAligned_add (by decide) hC.2.2.1
      (by simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega)) (by decide)) (by simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega)
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hX hm hax
    rw [hX, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    have hX' := PLift.up hX
    clear hX
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    -- the call
    obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
    simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h12 h14
    first
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          1280 ?@ (t₀.regs.get64 .rsi + 558560#64), 1280 ?@ lab "sbr_qmf_window_ds",
          1280 ?@ (t₀.regs.get64 .rsi + (175648#64 + BitVec.ofNat 64 (128 * i))), 32 ?@ lab "pd_reverse"] as Rc hRc
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
          1280 ?@ (t₀.regs.get64 .rsi + 558560#64), 1280 ?@ lab "sbr_qmf_window_ds",
          1280 ?@ (t₀.regs.get64 .rsi + (264416#64 + BitVec.ofNat 64 (128 * i))), 32 ?@ lab "pd_reverse"] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hFR'.down
      (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      all_goals decide
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      all_goals decide
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      exact al32_add1 _ 558560 hal (by decide)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      exact halw
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      try simp only [BitVec.ofNat_eq_ofNat] at hax
      exact hax
    · exact hpd
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_1]
        refine ⟨_, c0, i, hC, ⟨hrsp', hrbp'⟩, hch, hc0, hi, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx', h12', h13', h14', h15', dA, sbrA, arg1, Args.d, ↓reduceIte]; done)
        simp only [Mm, ApplyF, FrA6, DArrW, ArrW, CstW, FnW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
        rw [hX'.down, call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', hrbp, h13', h13, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7750_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_1" ⟨"ff_aac_sbr_apply.L7750_1", B.L7750_1, some "ff_aac_sbr_apply.L7750_2"⟩ := by
  info_off
  obtain ⟨hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_1.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, ArrW, DspW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    rw [call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    rw [res_k0 hSt] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    -- the call
    obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
    simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h12 h14
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
      1280 ?@ (t₀.regs.get64 .rsi + 558560#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hFR'.down
      (fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      exact al16_of_32 (al32_add1 _ 558560 hal (by decide))
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_2]
        refine ⟨_, c0, i, hC, ⟨hrsp', hrbp'⟩, hch, hc0, hi, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx', h12', h13', h14', h15', dA, sbrA, arg1, Args.d, ↓reduceIte]; done)
        simp only [Mm, ApplyF, FrA6, ArrW, DspW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero]
        rw [call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        rw [res_k0 hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', hrbp, h13', h13, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7750_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_2" ⟨"ff_aac_sbr_apply.L7750_2", B.L7750_2, some "ff_aac_sbr_apply.L7750_3"⟩ := by
  info_off
  obtain ⟨-, -, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_2.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  have hZ := carve_at (sbrA t₀ + 0x5fcc0#64) 1280 0 512 (by omega) (by decide)
  simp only [sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.sub_zero, Nat.reduceSub] at hZ
  have hZ' := PLift.up hZ
  clear hZ
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    rw [hZ'.down, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    rw [res_k0 hSt] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    -- the call
    obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
    simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h12 h14
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
      512 ?@ (t₀.regs.get64 .rsi + 558560#64), 16 ?@ lab "ff_ps_neg"] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hFR'.down
      (fun ra' => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      exact al16_of_32 (al32_add1 _ 558560 hal (by decide))
    · exact halw
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_3]
        refine ⟨_, c0, i, hC, ⟨hrsp', hrbp'⟩, hch, hc0, hi, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx', h12', h13', h14', h15', dA, sbrA, arg1, Args.d, ↓reduceIte]; done)
        simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero]
        rw [hZ'.down, call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        rw [res_k0 hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', hrbp, h13', h13, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7750_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_3" ⟨"ff_aac_sbr_apply.L7750_3", B.L7750_3, some "ff_aac_sbr_apply.L7750_4"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_3.mp hs
  clear hs
  have hac := hK.1.2.2.2.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, ArrW, FnW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal
  simp only [hac] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  have hZ := carve_at (sbrA t₀ + 0x5fcc0#64) 1280 0 256 (by omega) (by decide)
  have hZ2 := carve_at (sbrA t₀ + 0x5fdc0#64) 1024 0 256 (by omega) (by decide)
  simp only [sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.sub_zero, Nat.reduceSub] at hZ hZ2
  have hZ' := PLift.up hZ
  have hZ2' := PLift.up hZ2
  clear hZ hZ2
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    rw [hZ'.down, hZ2'.down, call_res k hSt] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_3]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    -- the call
    obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
    simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at h12 h14
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64), e.Ctx x.anaCtx, e.TxTab] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hFR'.down
      (fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      exact ⟨by decide, al32_add1 _ 558560 hal (by decide)⟩
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_4]
        refine ⟨_, c0, i, hC, ⟨hrsp', hrbp'⟩, hch, hc0, hi, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx', h12', h13', h14', h15', dA, sbrA, arg1, Args.d, ↓reduceIte]; done)
        simp only [Mm, ApplyF, FrA6, ArrW, FnW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hac]
        rw [hZ'.down, hZ2'.down, call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', hrbp, h13', h13, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7750_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_4" ⟨"ff_aac_sbr_apply.L7750_4", B.L7750_4, some "ff_aac_sbr_apply.L7750_5"⟩ := by
  info_off
  obtain ⟨-, -, -, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_4.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.2.1
  have hlast := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2   -- G2: LayoutC has the ps_noise group and `pd_reverse` before the last conjunct
  have hyp := ApplyC_ypos_le hCy ch
  simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal hlast
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  have hZ := carve_at (sbrA t₀ + 0x5fcc0#64) 1280 0 256 (by omega) (by decide)
  simp only [sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Nat.sub_zero, Nat.reduceSub] at hZ
  have hZ' := PLift.up hZ
  clear hZ
  have hX := carve_at (dA t₀ ch + 0x3920#64) 16384 (8192 * (y.d ch).ypos + 256 * i) 256 (by omega) (by decide)
  have hax : isAligned 32 (dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i)) = true :=
    isAligned_add (by decide) (isAligned_add (by decide) (isAligned_add (by decide) hC.2.2.1
      (by simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega)) (by decide)) (by simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; omega)
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, Args.d,
      ↓reduceIte, Nat.one_ne_zero] at hX hm hax
    rw [hX, hZ'.down, call_res k hSt] at hm
    have hX' := PLift.up hX
    clear hX
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    rw [res_k0 hSt] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    -- the call
    obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
    simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Args.d,
      ↓reduceIte, Nat.one_ne_zero] at h12 h14 h15
    first
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
          256 ?@ (t₀.regs.get64 .rsi + (180928#64 + BitVec.ofNat 64 (8192 * y.d0.ypos + 256 * i))),
          256 ?@ (t₀.regs.get64 .rsi + 558560#64), 16 ?@ lab "ff_ps_neg"] as Rc hRc
      | sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
          256 ?@ (t₀.regs.get64 .rsi + (269696#64 + BitVec.ofNat 64 (8192 * y.d1.ypos + 256 * i))),
          256 ?@ (t₀.regs.get64 .rsi + 558560#64), 16 ?@ lab "ff_ps_neg"] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    refine MachineWP.CallsTo.of_procSpec Rc hFR'.down
      (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      try simp only [BitVec.ofNat_eq_ofNat] at hax
      exact al16_of_32 hax
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, MachineData.pushRa, h14]
      exact al16_of_32 (al32_add1 _ 558560 hal (by decide))
    · exact halw
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, MachineData.pushRa, h14]
      omega
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_5]
        refine ⟨_, c0, i, hC, ⟨hrsp', hrbp'⟩, hch, hc0, hi, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, hbx', h12', h13', h14', h15', dA, sbrA, arg1, Args.d, ↓reduceIte]; done)
        simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero]
        rw [hX'.down, hZ'.down, call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        rw [res_k0 hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', hrbp, h13', h13, BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7750_5 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_5" ⟨"ff_aac_sbr_apply.L7750_5", B.L7750_5, some "ff_aac_sbr_apply.L7750_6"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, hlfe, hFR, -⟩ := hc
  have hFR' := PLift.up hFR
  clear hFR
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, i, hC, ⟨hrsp, hrbp⟩, hch, hc0, hi, h12, h13, h14, hbx, y, hK, hCy, h15, hm⟩ := T.L7750_5.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hal := hC.2.1
  have halw := hC.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, DArrW, DScW, c4, ArrW, FnW, ScW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm hal
  simp only [hfd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl, h13] at hn
  rw [ana_t128 i (by omega)] at hn
  have hyp := ApplyC_ypos_le hCy ch
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd] at hm
    rw [call_res_n k (0x30 + k) hSt (by omega)] at hm
    simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
    have hR := PLift.up (⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_5]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
    all_goals try sep_mem hm
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    case vc1 =>
      obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
      rename_i hz
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result] at hz
      have hi1 := ana_nz i hi hz
      simp only [ana_r13_step i hi, ana_r15_step]
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7750") ?_
      refine ⟨isSome_at L.L7750, ?_, ?_⟩
      · rw [T.L7750]
        refine ⟨_, c0, i + 1, hC, ⟨?_, ?_⟩, hch, hc0, hi1, ?_, ?_, ?_, ?_, y, hK, hCy, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h12, h13,
          h14, h15, hbx, dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, Args.d,
          ↓reduceIte, Nat.one_ne_zero, BitVec.ofNat_eq_ofNat]; done)
        simp only [Mm, ApplyF, FrA6, DArrW, DScW, c4, ArrW, FnW, ScW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
        rw [call_res_n k (0x30 + k) hSt (by omega)]
        try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        first
          | sep_close hm
      · left
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp, h13,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, ana_t128 (i + 1) (by omega)]
        first
          | var_step
    case vc9 =>
      obtain ⟨hrsp, hrbp, h12, h13, h14, h15, hbx, hsl⟩ := hR.down
      simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero] at h12 h14 h15
      first
        | guard_hyp hch :ₛ 0 < 2
          sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (0x30 + k) (t₀.regs.get64 .rsp - 464#64),
            10240 ?@ (t₀.regs.get64 .rsi + 478304#64), 16384 ?@ (t₀.regs.get64 .rsi + 180928#64),
            Int.toBytes 4 (y.kx0 : Int) =@ (t₀.regs.get64 .rsi + 166260#64),
            Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64)] as Rc hRc
        | guard_hyp hch :ₛ 1 < 2
          sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve (0x30 + k) (t₀.regs.get64 .rsp - 464#64),
            10240 ?@ (t₀.regs.get64 .rsi + 478304#64), 16384 ?@ (t₀.regs.get64 .rsi + 269696#64),
            Int.toBytes 4 (y.kx0 : Int) =@ (t₀.regs.get64 .rsi + 166260#64),
            Int.toBytes 4 (y.kx1 : Int) =@ (t₀.regs.get64 .rsi + 166264#64)] as Rc hRc
      have hRc' := PLift.up hRc
      clear hRc
      rw [hlfe]
      refine MachineWP.CallsTo.of_procSpec (⟨Rc, y.kx0, y.kx1⟩ : LfGenArgs) hFR'.down
        (fun ra' => ⟨⟨?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, LfGenF, LfGenKx]
        sep_mem hm
        sep_close hm
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, lfBuf]
        first
          | exact ypos_buf _ hyp
      · exact hCy.1.1
      · exact hCy.1.2.1
      · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, LfGenF, LfGenKx] at hpost
        obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        rw [hsp.down] at hrsp'
        have e := hRc'.down
        subst e
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨?_, ?_⟩
        · rw [T.L7750_6]
          refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, ?_⟩
          all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
          Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h12, h13, h14, h15, hbx,
          BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
          ↓reduceIte, Nat.one_ne_zero, hbx', h12', h13', h14', h15', dA, sbrA, arg1]; done)
          simp only [Mm, ApplyF, FrA6, DArrW, DScW, c4, ArrW, FnW, ScW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
            BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
          rw [call_res_n k (0x30 + k) hSt (by omega)]
          try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm' ⊢
          first
            | sep_close hm'
        · simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_mem hm'
          simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
          first
            | var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7750_6 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_6" ⟨"ff_aac_sbr_apply.L7750_6", B.L7750_6, some "ff_aac_sbr_apply.L7750_7"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h15, hbx, y, hK, hCy, hm⟩ := T.L7750_6.mp hs
  clear hs
  have hyp := ApplyC_ypos_le hCy ch
  have PsW_ypos0 : ∀ p : Nat, PsW { y with d0 := { y.d0 with ypos := p } } t₀ = PsW y t₀ := fun _ => rfl
  have PsW_ypos1 : ∀ p : Nat, PsW { y with d1 := { y.d1 with ypos := p } } t₀ = PsW y t₀ := fun _ => rfl
  simp only [Mm, ApplyF, FrA6, DScW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  · simp only [Args.d, ↓reduceIte] at hyp
    dsimp only
    simp only [B.L7750_6]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7750_7]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_,
                     { y with d0 := { y.d0 with ypos := 1 - y.d0.ypos } }, ⟨Keep_ypos0 hK.1 _, hK.2⟩,
                     ApplyC_ypos0 hCy _ (by omega), ?_, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx, dA, ↓reduceIte,
          sbrA, arg1, BitVec.add_assoc, Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64,
          BitVec.setWidth_eq, Args.d, BitVec.toNat_ofNat, Nat.reduceEqDiff, BitVec.toNat_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl] at *
    all_goals try sep_mem hm
    all_goals try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try exact ypos_xor_rax _ hyp
    all_goals try (simp only [Mm, ApplyF, FrA6, DScW, c4, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd, FnW_ypos0, AcW_ypos0, ScW_ypos0, TabW_ypos0,
      OutW_ypos0, PsW_ypos0, ypos_xor _ hyp] at hm ⊢)
    all_goals try sep_close hm
    all_goals try simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero, Nat.reduceSub]
    all_goals try var_step
  · simp only [Args.d, ↓reduceIte, Nat.one_ne_zero] at hyp
    dsimp only
    simp only [B.L7750_6]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try subst_vars
    all_goals try (refine ⟨?_, ?_⟩; rw [T.L7750_7]
                   refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_,
                     { y with d1 := { y.d1 with ypos := 1 - y.d1.ypos } }, ⟨Keep_ypos1 hK.1 _, hK.2⟩,
                     ApplyC_ypos1 hCy _ (by omega), ?_, ?_⟩)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
          AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
          BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.reduceMul, BitVec.add_zero, Width.bytes,
          Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx, dA, ↓reduceIte,
          sbrA, arg1, BitVec.add_assoc, Nat.zero_ne_one, Nat.one_ne_zero, lex_var, slot64,
          BitVec.setWidth_eq, Args.d, BitVec.toNat_ofNat, Nat.reduceEqDiff, BitVec.toNat_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl] at *
    all_goals try sep_mem hm
    all_goals try simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
    all_goals try exact ypos_xor_rax _ hyp
    all_goals try (simp only [Mm, ApplyF, FrA6, DScW, c4, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
      BitVec.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Nat.reduceMul, Nat.reduceAdd, FnW_ypos1, AcW_ypos1, ScW_ypos1, TabW_ypos1,
      OutW_ypos1, PsW_ypos1, ypos_xor _ hyp] at hm ⊢)
    all_goals try sep_close hm
    all_goals try simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, Nat.sub_zero, Nat.reduceSub]
    all_goals try var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7750_7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_7" ⟨"ff_aac_sbr_apply.L7750_7", B.L7750_7, some "ff_aac_sbr_apply.L7750_8"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, hhie, hHI, -⟩ := hc
  have hHI' := PLift.up hHI
  clear hHI
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h14, h15, hbx, y, hK, hCy, hrax, hm⟩ := T.L7750_7.mp hs
  clear hs
  have hfd := hK.1.2.2.1
  have hk0 : y.k0 ≤ 32 := hCy.1.2.2.2.2.2.1
  have hpm := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hst := hC.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, DScW, c4, ScW, FnW, Blocks, sbrA, arg0, arg1, arg3, arg4,
    BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [hfd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hsp : PLift (∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64) := ⟨by
    intro a; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  have hX := carve_at (t₀.regs.get64 .rsi + 478304#64) 10240 0 (320 * y.k0) (by omega) (by decide)
  have hA0 := carve_at (t₀.regs.get64 .rsi + 547936#64) 512 0 (8 * y.k0) (by omega) (by decide)
  have hA1 := carve_at (t₀.regs.get64 .rsi + 548448#64) 512 0 (8 * y.k0) (by omega) (by decide)
  simp only [BitVec.add_zero, BitVec.ofNat_eq_ofNat, Nat.sub_zero] at hX hA0 hA1
  rw [hX, hA0, hA1, call_res_n k 0xa8 hSt (by omega)] at hm
  have hC' := PLift.up (⟨hX, hA0, hA1⟩ : _ ∧ _ ∧ _)
  clear hX hA0 hA1
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  simp only [dA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
    Nat.one_ne_zero] at hm hrax
  simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
  have hR := PLift.up (⟨hrsp, hrbp, h14, h15, hbx, hsl, hrax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7750_7]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
      BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl,
    BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc3 =>
    obtain ⟨hrsp, hrbp, h14, h15, hbx, hsl, hrax⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9934") ?_
    refine ⟨isSome_at L.L9934, ?_, ?_⟩
    · rw [T.L9934]
      refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, ?_, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero]; done)
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
                     first | exact hrax | (simp only [Nat.reducePow] at hrax ⊢; exact hrax))
      simp only [Mm, ApplyF, FrC, FrCs, ArrW, DspW, CstW, DArrW, DScW, c4, ScW, FnW, FnCell, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
      rw [hC'.down.1, hC'.down.2.1, hC'.down.2.2, call_res_n k 0xa8 hSt (by omega)]
      try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] at hm ⊢
      sep_close hm
    · first
        | (left; var_step)
        | (left
           simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
             BitVec.sub_sub_ofNat, Nat.reduceAdd]
           sep_mem hm
           simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat]
           try simp -implicitDefEqProofs only [BitVec.toNat_ofNat] at hn
           var_step)
        | (simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
             BitVec.sub_sub_ofNat, Nat.reduceAdd]
           sep_mem hm
           simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat]
           try simp -implicitDefEqProofs only [BitVec.toNat_ofNat] at hn
           var_step)
  case vc11 =>
    obtain ⟨hrsp, hrbp, h14, h15, hbx, hsl, hrax⟩ := hR.down
    rename_i hzf hfi
    simp only [CondCode.interp_z, StatusFlags.zf_from_result] at hzf
    have hs0 := start_ne _ hzf
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0xa8 (t₀.regs.get64 .rsp - 464#64),
        (320 * y.k0) ?@ (t₀.regs.get64 .rsi + 478304#64), (8 * y.k0) ?@ (t₀.regs.get64 .rsi + 547936#64),
        (8 * y.k0) ?@ (t₀.regs.get64 .rsi + 548448#64), 4 ?@ lab "LCPI19_0", 4 ?@ lab "LCPI19_1",
        16 ?@ lab "LCPI19_2", 16 ?@ lab "ps_mask3",
        Int.toBytes 8 e.fs.autocorr.toBitVec.toInt =@ (t₀.regs.get64 .rsi + 559928#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    rw [hhie]
    refine MachineWP.CallsTo.of_procSpec Rc hHI'.down
      (fun ra' => ⟨⟨?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero, HfInvF, hfInvN, FnCell, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, k0_n _ hk0, k0_n2 _ hk0]
      sep_mem hm
      sep_close hm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero, hfInvN, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, k0_n _ hk0, k0_n2 _ hk0]
      first
        | exact hk0
    · exact hpm
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero]
      first
        | exact al16_rsp456 _ hst
        | (rw [hsp.down]; exact al16_rsp456 _ hst)
    · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14, h15, hbx,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Args.d,
        ↓reduceIte, Nat.one_ne_zero, HfInvF, hfInvN, FnCell, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, k0_n _ hk0, k0_n2 _ hk0] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [hsp.down] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7750_8]
        refine ⟨_, c0, hC, ⟨hrsp', hrbp'⟩, hch, hc0, y, hK, hCy, hs0, ?_⟩
        simp only [Mm, ApplyF, FrA6, ArrW, DspW, CstW, DArrW, DScW, c4, ScW, FnW, FnCell, Blocks, dA, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, hfd]
        rw [hC'.down.1, hC'.down.2.1, hC'.down.2.2, call_res_n k 0xa8 hSt (by omega)]
        try simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] at hm' ⊢
        sep_close hm'
      · first
          | var_step
          | (simp only [lex_var, slot64, hrbp', hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
             sep_mem hm'
             simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat]
             try simp -implicitDefEqProofs only [BitVec.toNat_ofNat] at hn
             var_step)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7750_8 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7750_8" ⟨"ff_aac_sbr_apply.L7750_8", B.L7750_8, some "ff_aac_sbr_apply.L7866"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, y, hK, hCy, hst, hm⟩ := T.L7750_8.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  · have hD := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨-, hlen, -, -, -, -, -, hinv3, -⟩ := hD
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hl⟩ := list10 _ hlen
    have hb0 : b0.toNat ≤ 3 := by simpa [u8, hl] using hinv3 0 (by omega)
    have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
    rw [hl, split10] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have hv0 : (BitVec.ofInt 8 (Int.ofBytes [b0])).toNat ≤ 3 := by rw [byte_toNat]; exact hb0
    simp only [dA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
      Nat.one_ne_zero] at hm
    simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
    have hR := PLift.up (⟨hrsp, hrbp, hsl, hn⟩ : _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_8]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      Int64.ofBitVec_toBitVec] at *
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (simp only [CondCode.interp_nc, StatusFlags.cf_from_result, cf_lt4 _ hv0, Bool.not_true,
      Bool.false_eq_true] at *; done)
    all_goals try exact bw_off _ _ hb0
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc8 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7866") ?_
      refine ⟨isSome_at L.L7866, ?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc11 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
  · have hD := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨-, hlen, -, -, -, -, -, hinv3, -⟩ := hD
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, hl⟩ := list10 _ hlen
    have hb0 : b0.toNat ≤ 3 := by simpa [u8, hl] using hinv3 0 (by omega)
    have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
    rw [hl, split10] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have hv0 : (BitVec.ofInt 8 (Int.ofBytes [b0])).toNat ≤ 3 := by rw [byte_toNat]; exact hb0
    simp only [dA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
      Nat.one_ne_zero] at hm
    simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
    have hR := PLift.up (⟨hrsp, hrbp, hsl, hn⟩ : _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7750_8]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      Int64.ofBitVec_toBitVec] at *
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (simp only [CondCode.interp_nc, StatusFlags.cf_from_result, cf_lt4 _ hv0, Bool.not_true,
      Bool.false_eq_true] at *; done)
    all_goals try exact bw_off _ _ hb0
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc8 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7866") ?_
      refine ⟨isSome_at L.L7866, ?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _
    case vc11 =>
      obtain ⟨hrsp, hrbp, hsl, hn⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7866]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
            BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
            nq_rax _ hnq, hrsp, hrbp]; done)
        simp only [Mm, ApplyF, FrA6, TabW, DScW, c4, CstW, Blocks, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, hl, split10]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7866 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7866" ⟨"ff_aac_sbr_apply.L7866", B.L7866, some "ff_aac_sbr_apply.L7884"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7866.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7866]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc3 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7884") ?_
      refine ⟨isSome_at L.L7884, ?_, ?_⟩
      · rw [T.L7884]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc5 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7884]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7884 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7884" ⟨"ff_aac_sbr_apply.L7884", B.L7884, some "ff_aac_sbr_apply.L7884_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7884.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7884]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq]
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc5 =>
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc6 =>
      refine ⟨?_, ?_⟩
      · rw [T.L7884_1]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7884_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7884_1" ⟨"ff_aac_sbr_apply.L7884_1", B.L7884_1, some "ff_aac_sbr_apply.L78f2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7884_1.mp hs
  clear hs
  have hd0 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 : y.d0.invf.length = 10 := hd0.2.1
  have hl1 : y.d1.invf.length = 10 := hd1.2.1
  have hb0 : u8 y.d0.invf 1 ≤ 3 := hd0.2.2.2.2.2.2.2.1 1 (by omega)
  have hb1 : u8 y.d1.invf 1 ≤ 3 := hd1.2.2.2.2.2.2.2.1 1 (by omega)
  have e0 : (y.d0.invf.take 6).getD 1 0 = y.d0.invf.getD 1 0 := take_getD' _ _ _ (by decide)
  have e1 : (y.d1.invf.take 6).getD 1 0 = y.d1.invf.getD 1 0 := take_getD' _ _ _ (by decide)
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [byte_split y.d0.invf _ 6 (by omega) (by omega), byte_split y.d1.invf _ 6 (by omega) (by omega),
    byte_split (y.d0.invf.take 6) _ 1 (by simp only [List.length_take, hl0]; omega)
      (by simp only [List.length_take, hl0]; omega),
    byte_split (y.d1.invf.take 6) _ 1 (by simp only [List.length_take, hl1]; omega)
      (by simp only [List.length_take, hl1]; omega), e0, e1] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR2 := PLift.up (⟨hl0, hl1, e0, e1⟩ : _ ∧ _ ∧ _ ∧ _)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7884_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4, zx_byte,
        add_sub_self']
      first | exact bw_off8 _ hb0 | exact bw_off8 _ hb1
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4]
      first | exact bw_off _ _ hb0 | exact bw_off _ _ hb1
    case vc5 =>
      rename_i h1 h2 h3 h4
      exfalso
      simp only [sw8b, sw8_3, CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
        cf_sub8 _ 3 (UInt8.toNat_lt _) (by decide), zf_sub8 _ 3 (UInt8.toNat_lt _) (by decide),
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2 h3 h4
      try simp only [u8] at hb0 hb1
      omega
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L78f2") ?_
      refine ⟨isSome_at L.L78f2, ?_, ?_⟩
      · rw [T.L78f2]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 6 (by omega) (by omega), byte_split y.d1.invf _ 6 (by omega) (by omega),
          byte_split (y.d0.invf.take 6) _ 1 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 6) _ 1 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc7 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L78f2]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 6 (by omega) (by omega), byte_split y.d1.invf _ 6 (by omega) (by omega),
          byte_split (y.d0.invf.take 6) _ 1 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 6) _ 1 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L78f2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L78f2" ⟨"ff_aac_sbr_apply.L78f2", B.L78f2, some "ff_aac_sbr_apply.L7910"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L78f2.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L78f2]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc3 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7910") ?_
      refine ⟨isSome_at L.L7910, ?_, ?_⟩
      · rw [T.L7910]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc5 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7910]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7910 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7910" ⟨"ff_aac_sbr_apply.L7910", B.L7910, some "ff_aac_sbr_apply.L7910_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7910.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7910]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq]
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc5 =>
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc6 =>
      refine ⟨?_, ?_⟩
      · rw [T.L7910_1]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7910_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7910_1" ⟨"ff_aac_sbr_apply.L7910_1", B.L7910_1, some "ff_aac_sbr_apply.L797e"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7910_1.mp hs
  clear hs
  have hd0 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 : y.d0.invf.length = 10 := hd0.2.1
  have hl1 : y.d1.invf.length = 10 := hd1.2.1
  have hb0 : u8 y.d0.invf 2 ≤ 3 := hd0.2.2.2.2.2.2.2.1 2 (by omega)
  have hb1 : u8 y.d1.invf 2 ≤ 3 := hd1.2.2.2.2.2.2.2.1 2 (by omega)
  have e0 : (y.d0.invf.take 7).getD 2 0 = y.d0.invf.getD 2 0 := take_getD' _ _ _ (by decide)
  have e1 : (y.d1.invf.take 7).getD 2 0 = y.d1.invf.getD 2 0 := take_getD' _ _ _ (by decide)
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [byte_split y.d0.invf _ 7 (by omega) (by omega), byte_split y.d1.invf _ 7 (by omega) (by omega),
    byte_split (y.d0.invf.take 7) _ 2 (by simp only [List.length_take, hl0]; omega)
      (by simp only [List.length_take, hl0]; omega),
    byte_split (y.d1.invf.take 7) _ 2 (by simp only [List.length_take, hl1]; omega)
      (by simp only [List.length_take, hl1]; omega), e0, e1] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR2 := PLift.up (⟨hl0, hl1, e0, e1⟩ : _ ∧ _ ∧ _ ∧ _)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7910_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4, zx_byte,
        add_sub_self']
      first | exact bw_off8 _ hb0 | exact bw_off8 _ hb1
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4]
      first | exact bw_off _ _ hb0 | exact bw_off _ _ hb1
    case vc5 =>
      rename_i h1 h2 h3 h4
      exfalso
      simp only [sw8b, sw8_3, CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
        cf_sub8 _ 3 (UInt8.toNat_lt _) (by decide), zf_sub8 _ 3 (UInt8.toNat_lt _) (by decide),
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2 h3 h4
      try simp only [u8] at hb0 hb1
      omega
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L797e") ?_
      refine ⟨isSome_at L.L797e, ?_, ?_⟩
      · rw [T.L797e]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 7 (by omega) (by omega), byte_split y.d1.invf _ 7 (by omega) (by omega),
          byte_split (y.d0.invf.take 7) _ 2 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 7) _ 2 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc7 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L797e]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 7 (by omega) (by omega), byte_split y.d1.invf _ 7 (by omega) (by omega),
          byte_split (y.d0.invf.take 7) _ 2 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 7) _ 2 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L797e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L797e" ⟨"ff_aac_sbr_apply.L797e", B.L797e, some "ff_aac_sbr_apply.L799c"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L797e.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L797e]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc3 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L799c") ?_
      refine ⟨isSome_at L.L799c, ?_, ?_⟩
      · rw [T.L799c]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc5 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L799c]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L799c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L799c" ⟨"ff_aac_sbr_apply.L799c", B.L799c, some "ff_aac_sbr_apply.L799c_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L799c.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L799c]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq]
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc5 =>
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc6 =>
      refine ⟨?_, ?_⟩
      · rw [T.L799c_1]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L799c_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L799c_1" ⟨"ff_aac_sbr_apply.L799c_1", B.L799c_1, some "ff_aac_sbr_apply.L7a0a"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L799c_1.mp hs
  clear hs
  have hd0 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 : y.d0.invf.length = 10 := hd0.2.1
  have hl1 : y.d1.invf.length = 10 := hd1.2.1
  have hb0 : u8 y.d0.invf 3 ≤ 3 := hd0.2.2.2.2.2.2.2.1 3 (by omega)
  have hb1 : u8 y.d1.invf 3 ≤ 3 := hd1.2.2.2.2.2.2.2.1 3 (by omega)
  have e0 : (y.d0.invf.take 8).getD 3 0 = y.d0.invf.getD 3 0 := take_getD' _ _ _ (by decide)
  have e1 : (y.d1.invf.take 8).getD 3 0 = y.d1.invf.getD 3 0 := take_getD' _ _ _ (by decide)
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [byte_split y.d0.invf _ 8 (by omega) (by omega), byte_split y.d1.invf _ 8 (by omega) (by omega),
    byte_split (y.d0.invf.take 8) _ 3 (by simp only [List.length_take, hl0]; omega)
      (by simp only [List.length_take, hl0]; omega),
    byte_split (y.d1.invf.take 8) _ 3 (by simp only [List.length_take, hl1]; omega)
      (by simp only [List.length_take, hl1]; omega), e0, e1] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR2 := PLift.up (⟨hl0, hl1, e0, e1⟩ : _ ∧ _ ∧ _ ∧ _)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L799c_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4, zx_byte,
        add_sub_self']
      first | exact bw_off8 _ hb0 | exact bw_off8 _ hb1
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4]
      first | exact bw_off _ _ hb0 | exact bw_off _ _ hb1
    case vc5 =>
      rename_i h1 h2 h3 h4
      exfalso
      simp only [sw8b, sw8_3, CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
        cf_sub8 _ 3 (UInt8.toNat_lt _) (by decide), zf_sub8 _ 3 (UInt8.toNat_lt _) (by decide),
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2 h3 h4
      try simp only [u8] at hb0 hb1
      omega
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7a0a") ?_
      refine ⟨isSome_at L.L7a0a, ?_, ?_⟩
      · rw [T.L7a0a]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 8 (by omega) (by omega), byte_split y.d1.invf _ 8 (by omega) (by omega),
          byte_split (y.d0.invf.take 8) _ 3 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 8) _ 3 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc7 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7a0a]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 8 (by omega) (by omega), byte_split y.d1.invf _ 8 (by omega) (by omega),
          byte_split (y.d0.invf.take 8) _ 3 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 8) _ 3 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7a0a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7a0a" ⟨"ff_aac_sbr_apply.L7a0a", B.L7a0a, some "ff_aac_sbr_apply.L7a28"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7a0a.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7a0a]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc3 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7a28") ?_
      refine ⟨isSome_at L.L7a28, ?_, ?_⟩
      · rw [T.L7a28]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc5 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7a28]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7a28 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7a28" ⟨"ff_aac_sbr_apply.L7a28", B.L7a28, some "ff_aac_sbr_apply.L7a28_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, hm⟩ := T.L7a28.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7a28]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq]
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc5 =>
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b00") ?_
      refine ⟨isSome_at L.L7b00, ?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc6 =>
      rename_i hcc
      have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, sw32, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod,
        BitVec.reduceSetWidth, CondCode.interp_c, CondCode.interp_nz, StatusFlags.cf_from_result,
        StatusFlags.zf_from_result, cf_sub32 y.nq 5 (by omega) (by omega), zf_sub32 y.nq 5 (by omega) (by omega),
        decide_eq_true_eq, decide_eq_false_iff_not] at hcc
      refine ⟨?_, ?_⟩
      · rw [T.L7a28_1]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, by omega, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000 in
theorem blk_L7a28_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7a28_1" ⟨"ff_aac_sbr_apply.L7a28_1", B.L7a28_1, some "ff_aac_sbr_apply.L7a96"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, h5, hm⟩ := T.L7a28_1.mp hs
  clear hs
  have hd0 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hd1 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl0 : y.d0.invf.length = 10 := hd0.2.1
  have hl1 : y.d1.invf.length = 10 := hd1.2.1
  have hb0 : u8 y.d0.invf 4 ≤ 3 := hd0.2.2.2.2.2.2.2.1 4 (by omega)
  have hb1 : u8 y.d1.invf 4 ≤ 3 := hd1.2.2.2.2.2.2.2.1 4 (by omega)
  have e0 : (y.d0.invf.take 9).getD 4 0 = y.d0.invf.getD 4 0 := take_getD' _ _ _ (by decide)
  have e1 : (y.d1.invf.take 9).getD 4 0 = y.d1.invf.getD 4 0 := take_getD' _ _ _ (by decide)
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [byte_split y.d0.invf _ 9 (by omega) (by omega), byte_split y.d1.invf _ 9 (by omega) (by omega),
    byte_split (y.d0.invf.take 9) _ 4 (by simp only [List.length_take, hl0]; omega)
      (by simp only [List.length_take, hl0]; omega),
    byte_split (y.d1.invf.take 9) _ 4 (by simp only [List.length_take, hl1]; omega)
      (by simp only [List.length_take, hl1]; omega), e0, e1] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR2 := PLift.up (⟨hl0, hl1, e0, e1⟩ : _ ∧ _ ∧ _ ∧ _)
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7a28_1]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4, zx_byte,
        add_sub_self']
      first | exact bw_off8 _ hb0 | exact bw_off8 _ hb1
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_scale4]
      first | exact bw_off _ _ hb0 | exact bw_off _ _ hb1
    case vc5 =>
      rename_i h1 h2 h3 h4
      exfalso
      simp only [sw8b, sw8_3, CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.zf_from_result,
        cf_sub8 _ 3 (UInt8.toNat_lt _) (by decide), zf_sub8 _ 3 (UInt8.toNat_lt _) (by decide),
        Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h1 h2 h3 h4
      try simp only [u8] at hb0 hb1
      omega
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7a96") ?_
      refine ⟨isSome_at L.L7a96, ?_, ?_⟩
      · rw [T.L7a96]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, h5, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 9 (by omega) (by omega), byte_split y.d1.invf _ 9 (by omega) (by omega),
          byte_split (y.d0.invf.take 9) _ 4 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 9) _ 4 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc7 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7a96]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, h5, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, DScW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        obtain ⟨hl0, hl1, e0, e1⟩ := hR2.down
        rw [byte_split y.d0.invf _ 9 (by omega) (by omega), byte_split y.d1.invf _ 9 (by omega) (by omega),
          byte_split (y.d0.invf.take 9) _ 4 (by simp only [List.length_take, hl0]; omega)
            (by simp only [List.length_take, hl0]; omega),
          byte_split (y.d1.invf.take 9) _ 4 (by simp only [List.length_take, hl1]; omega)
            (by simp only [List.length_take, hl1]; omega), e0, e1]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7a96 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7a96" ⟨"ff_aac_sbr_apply.L7a96", B.L7a96, some "ff_aac_sbr_apply.L7ab4"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, h5, hm⟩ := T.L7a96.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7a96]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq] at *
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc3 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      left
      refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7ab4") ?_
      refine ⟨isSome_at L.L7ab4, ?_, ?_⟩
      · rw [T.L7ab4]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, h5, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · right
        refine ⟨?_, by simp only [lex_var]; decide⟩
        simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        exact hn
    case vc5 =>
      obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7ab4]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_, h5, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7ab4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7ab4" ⟨"ff_aac_sbr_apply.L7ab4", B.L7ab4, some "ff_aac_sbr_apply.L7b00"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hax, h5, hm⟩ := T.L7ab4.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hbx
    dsimp only
    simp only [B.L7ab4]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, dA,
        BitVec.add_assoc, BitVec.setWidth_eq]
    all_goals try sep_mem hm
    all_goals try (show (_ : Nat) + 4 ≤ 20
                   simp -implicitDefEqProofs only [Mem.sub_base_add, BitVec.toNat_ofNat, Nat.reducePow]; omega)
    all_goals try (simp only [sub_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceLeDiff]; done)
    case vc5 =>
      rename_i hcc
      have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, sw32, BitVec.setWidth_eq,
        BitVec.ofNat_eq_ofNat, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod,
        BitVec.reduceSetWidth, CondCode.interp_c, CondCode.interp_nz, StatusFlags.cf_from_result,
        StatusFlags.zf_from_result, cf_sub32 y.nq 5 (by omega) (by omega), zf_sub32 y.nq 5 (by omega) (by omega),
        decide_eq_true_eq, decide_eq_false_iff_not] at hcc
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hcc
      exfalso
      omega
    case vc6 =>
      refine ⟨?_, ?_⟩
      · rw [T.L7b00]
        refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
        all_goals try
          simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
            Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
            hbx, h8, hax]
          done
        dsimp only
        simp only [Mm, ApplyF, FrA6, CstW, DArrW, Blocks, c4, dA, sbrA, arg0, arg1, arg3, arg4, lab, BitVec.add_assoc,
            BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ↓reduceIte, Nat.reduceEqDiff, Nat.one_ne_zero, ite_true, ite_false] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7b00 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b00" ⟨"ff_aac_sbr_apply.L7b00", B.L7b00, some "ff_aac_sbr_apply.L7b00_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hm⟩ := T.L7b00.mp hs
  clear hs
  simp only [Mm, ApplyF, FrA6, DScW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hD : DWF True (y.d ch) := by
    rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
    · exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => hst
    · exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => ⟨hst, hK.2.live hst Nat.one_ne_zero⟩
  obtain ⟨-, -, -, -, hne8, -, -, -, -, -, -, -, -, -, -, hlv⟩ := hD
  have hne := (hlv trivial).1
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  all_goals
    simp only [dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Args.d, ↓reduceIte,
      Nat.one_ne_zero] at hm hbx hne8 hne
    simp -implicitDefEqProofs only [BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, Nat.reduceSub] at hn
    have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    dsimp only
    simp only [B.L7b00]
    have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
    all_goals try (subst s₀)
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8,
        BitVec.add_assoc, BitVec.setWidth_eq, Args.d, ↓reduceIte, Nat.one_ne_zero] at *
    all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
    all_goals try sep_vals hm
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
      Int64.ofBitVec_toBitVec] at *
    all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
    all_goals try sep_vals hm
    all_goals try sep_mem hm
    all_goals try (simp only [CondCode.interp_z, StatusFlags.zf_from_result, sext_n _ hne8, flag_ne _ hne8 hne,
      Bool.false_eq_true] at *; done)
    case vc4 =>
      obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx⟩ := hR.down
      refine ⟨?_, ?_⟩
      · rw [T.L7b00_1]
        refine ⟨_, c0, _, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, rfl, ?_⟩
        all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul, Nat.reduceAdd,
          BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx]; done)
        simp only [Mm, ApplyF, FrH, DScW, c4, dA, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
          BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, ↓reduceIte, Nat.one_ne_zero, Args.d, sext_n _ hne8]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm ⊢
        try simp only [sext_n _ hne8] at hm ⊢
        sep_close hm
      · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
          BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
        rw [← hn]
        try simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reduceMod, Nat.sub_zero, BitVec.toNat_zero]
        all_goals first | rfl | exact Nat.le_refl _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7b00_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b00_1" ⟨"ff_aac_sbr_apply.L7b00_1", B.L7b00_1, some "ff_aac_sbr_apply.L7b2d"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hne, hm⟩ := T.L7b00_1.mp hs
  clear hs
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hkx1 : y.kx1 ≤ 32 := hCy.1.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hps := hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hps0 : y.kx1 + ((List.range' 0 (y.npatch - 0)).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 := by
    rw [← ps_zero]; have h5 := hps.2.2.2.2.2.2; omega   -- F5
  have hzx1 := zx32 y.kx1 (by omega)
  have hzx2 := zx32 y.npatch (by omega)
  have hzf := zf_np y.npatch hnp
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, hps0, hzx1, hzx2, hzf⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7b00_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, hps0, hzx1, hzx2, hzf⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7cb0") ?_
    refine ⟨isSome_at L.L7cb0, ?_, ?_⟩
    · rw [T.L7cb0]
      refine ⟨_, c0, _, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, hne, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          hzx1]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, hps0, hzx1, hzx2, hzf⟩ := hR.down
    rename_i hz
    simp only [CondCode.interp_z, StatusFlags.zf_from_result, hzf, decide_eq_false_iff_not] at hz
    refine ⟨?_, ?_⟩
    · rw [T.L7b2d]
      refine ⟨_, c0, _, 0, y.kx1, 0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, by omega, ?_,
        by omega, hps0, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          hzx1, hzx2, xz64]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7b2d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b2d" ⟨"ff_aac_sbr_apply.L7b2d", B.L7b2d, some "ff_aac_sbr_apply.L7b50"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h13, y, hK, hCy, hst, hne, hj, hrax,
    hg, hps, hm⟩ := T.L7b2d.mp hs
  clear hs
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hpl : y.pnum.length = 6 := hT.2.2.2.2.1
  have hps1 := ps_succ (fun i => u8 y.pnum i) j y.npatch hj
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hkk : kk ≤ 64 := by omega
  have hsx := sx_kk kk (by omega)
  try dsimp only at hps1
  have hA : (y.pnum.getD j 0).toNat = 0 → kk + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 := by
    intro h0; have h0' : u8 y.pnum j = 0 := h0; omega
  have hB : kk + (u8 y.pnum j - 0) + ((List.range' (j + 1) (y.npatch - (j + 1))).map (fun i => u8 y.pnum i)).sum ≤ y.kx1 + y.m1 := by omega
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [byte_split y.pnum _ j (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax, hsx, hA, hB⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7b2d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h13, hrax,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc2 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax, hsx, hA, hB⟩ := hR.down
    rename_i hz _
    simp only [CondCode.interp_z, StatusFlags.zf_from_result, zf_byte, decide_eq_true_eq] at hz
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7c5d") ?_
    refine ⟨isSome_at L.L7c5d, ?_, ?_⟩
    · rw [T.L7c5d]
      refine ⟨_, c0, _, j, kk, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, ?_, hg, hA hz, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hsx, xz64]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, xz64]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax, hsx, hA, hB⟩ := hR.down
    rename_i hz _
    simp only [CondCode.interp_z, StatusFlags.zf_from_result, zf_byte, decide_eq_false_iff_not] at hz
    refine ⟨?_, ?_⟩
    · rw [T.L7b50]
      refine ⟨_, c0, _, j, kk, g, 0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj,
        (show 0 < (y.pnum.getD j 0).toNat by omega), hB, hg, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hsx, xz64]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, xz64]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7b50 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b50" ⟨"ff_aac_sbr_apply.L7b50", B.L7b50, some "ff_aac_sbr_apply.L7b80"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hg, hm⟩ := T.L7b50.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hpl : y.pstart.length = 6 := hT.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [byte_split y.pstart _ j (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478298#64 (BitVec.ofNat 64 j)] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hzq := zx32 y.nq (by omega)
  have hzg := zx_ofNat g (by omega)
  have hzg' := zx32n g (by omega)
  have hz13 := zx_ofNat (y.nq + 1) (by omega)
  have hs1 := ofNat_succ64 y.nq
  have hsg := sw32 g
  have hsq := sw32 y.nq
  have hcf := cf_sub32 g y.nq (by omega) (by omega)
  have hzf := zf_sub32 g y.nq (by omega) (by omega)
  have hcf7 := cf_sub64 g 7 (by omega) (by omega)
  have hg7 : decide (g < 7) = true := by simp only [decide_eq_true_eq]; omega
  have h6 : BitVec.setWidth 64 (BitVec.setWidth 32 6#64) = 6#64 := rfl
  dsimp only
  simp only [B.L7b50]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, h13,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [hzq, hzg, hs1, hz13, hsg, hsq, hzg', zx_byte, h6] at *
  all_goals try simp only [CondCode.interp_nc, CondCode.interp_a, StatusFlags.cf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, StatusFlags.zf_from_result, hcf, hzf, hcf7, hg7, Bool.not_true,
    Bool.false_eq_true, ite_false] at *
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13⟩ := hR.down
    rename_i hz
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7bb3") ?_
    refine ⟨isSome_at L.L7bb3, ?_, ?_⟩
    · rw [T.L7bb3]
      refine ⟨_, c0, _, j, kk, g, xx, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx, hkk,
        ?_, hg, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, h13, hzq, hzg, hs1, hz13, hzg', zx_byte, h6, hcf7, hg7, Bool.not_true, Bool.false_eq_true]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pstart _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478298#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13⟩ := hR.down
    rename_i hz
    have hgq : g < y.nq + 1 := by
      refine (Nat.lt_or_ge g (y.nq + 1)).elim id fun hc => ?_
      exfalso
      have h1 : decide (g < y.nq) = false := by simp only [decide_eq_false_iff_not]; omega
      have h2 : decide (g = y.nq) = false := by simp only [decide_eq_false_iff_not]; omega
      simp only [h1, h2] at hz
      exact absurd hz (by decide)
    refine ⟨?_, ?_⟩
    · rw [T.L7b80]
      refine ⟨_, c0, _, j, kk, xx, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx,
        hkk, ?_, hgq, ?_, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, h13, hzq, hzg, hs1, hz13, hzg', zx_byte, h6, hcf7, hg7, Bool.not_true, Bool.false_eq_true]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pstart _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478298#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7b80 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7b80" ⟨"ff_aac_sbr_apply.L7b80", B.L7b80, some "ff_aac_sbr_apply.L7bb0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, xx, gg, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, hdx, hsi, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hax, hgg, hcx, h13, hm⟩ := T.L7b80.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hmul : BitVec.ofNat 64 gg * 2#64 = BitVec.ofNat 64 (2 * gg) := by
    apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  have hz6 := zf_sub64 6 gg (by omega) (by omega)
  have hzq := zf_sub64 (y.nq + 1) (gg + 1) (by omega) (by omega)
  have hs1 := ofNat_succ64 gg
  have hnl : y.ftNoise.length = 12 := (hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst).2.2.1
  rw [word_split y.ftNoise _ gg (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478214#64 (BitVec.ofNat 64 (2 * gg))] at hm
  dsimp only
  simp only [B.L7b80]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, hdx, hsi, hax,
      hcx, h13, BitVec.add_assoc, BitVec.setWidth_eq, AddrIndex.offset64_scale2, hmul, hs1] at *
  all_goals try simp only [CondCode.interp_z, CondCode.interp_nz, StatusFlags.zf_from_result, hz6, hzq,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc1 =>
    exfalso
    rename_i h6
    omega
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7bb0") ?_
    refine ⟨isSome_at L.L7bb0, ?_, ?_⟩
    · rw [T.L7bb0]
      refine ⟨_, c0, _, j, kk, xx, gg, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx, hkk,
        ?_, hgg, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, hdx, hsi, hax, hcx, h13, hs1]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [word_split y.ftNoise _ gg (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478214#64 (BitVec.ofNat 64 (2 * gg))]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14, hcx, hdx, hs1]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, hcx, hdx, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ := hR.down
    rename_i _ hq _ _
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b80") ?_
    refine ⟨isSome_at L.L7b80, ?_, ?_⟩
    · rw [T.L7b80]
      refine ⟨_, c0, _, j, kk, xx, gg + 1, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj,
        hxx, hkk, ?_, by omega, ?_, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, hdx, hsi, hax, hcx, h13, hs1]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [word_split y.ftNoise _ gg (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478214#64 (BitVec.ofNat 64 (2 * gg))]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14, hcx, hdx, hs1]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, hcx, hdx, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc5 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hsi, hax, hcx, h13⟩ := hR.down
    rename_i h1 hq h3 h4
    have hq' : y.nq + 1 = gg + 1 := by
      by_cases hd : y.nq + 1 = gg + 1
      · exact hd
      · simp only [hd, decide_false, Bool.not_false] at hq
        exact absurd hq (by decide)
    have hF2 : u16 y.ftNoise y.nq = y.kx1 + y.m1 :=
      (hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    exfalso
    clear hm hR hn
    have hbv : ∀ b0 b1 : UInt8, BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (Int.ofBytes [b0, b1])))
        = BitVec.ofNat 64 (b0.toNat + 256 * b1.toNat) := by
      intro b0 b1
      apply BitVec.eq_of_toNat_eq
      have ha := b0.toNat_lt
      have hb := b1.toNat_lt
      simp -implicitDefEqProofs only [Int.ofBytes, List.foldr, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
      omega
    have hu : (y.ftNoise.getD (2 * gg) 0).toNat + 256 * (y.ftNoise.getD (2 * gg + 1) 0).toNat
        = y.kx1 + y.m1 := by
      rw [show gg = y.nq by omega]; exact hF2
    rw [CondCode.interp_l_cmp, hbv, hu] at h4
    simp -implicitDefEqProofs only [BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, decide_eq_false_iff_not] at h4
    split at h4 <;> split at h4 <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7bb0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb0" ⟨"ff_aac_sbr_apply.L7bb0", B.L7bb0, some "ff_aac_sbr_apply.L7bb3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, xx, gg, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, hdx, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hax, hgg, hm⟩ := T.L7bb0.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hzx := zx_ofNat gg (by omega)
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hax⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7bb0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, hdx, hax, hzx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, hdx, hax⟩ := hR.down
  refine ⟨?_, ?_⟩
  · rw [T.L7bb3]
    refine ⟨_, c0, _, j, kk, gg, xx, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx, hkk, ?_,
      by omega, ?_⟩
    all_goals try
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
        Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
        h15, h12, h14, hdx, hax]
      done
    simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
    sep_close hm
  · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
    sep_mem hm
    simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
    rw [← hn]
    var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7bb3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb3" ⟨"ff_aac_sbr_apply.L7bb3", B.L7bb3, some "ff_aac_sbr_apply.L7bb3_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hax, hg, hm⟩ := T.L7bb3.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13, hax⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hP : u8 y.pstart j + u8 y.pnum j ≤ 32 := hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  have hle := le_test6 g (by omega)
  have hadd := add32 xx (u8 y.pstart j) (by omega)
  have hzP := zx_ofNat (u8 y.pstart j + xx) (by omega)
  have hshP := shl320 (u8 y.pstart j + xx) (by omega)
  have hshK := shl320 kk (by omega)
  have hfix : ∀ r a X : BitVec 64, 16#64 + (r + (a + X)) = r + (a + (X + 16#64)) := by
    intro r a X; rw [BitVec.add_comm 16#64, BitVec.add_assoc, BitVec.add_assoc]
  dsimp only
  simp only [B.L7bb3]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h14, h13, hax,
      BitVec.add_assoc, BitVec.setWidth_eq, AddrIndex.offset64_scale4, BitVec.toNat_ofNat, Nat.reduceEqDiff, ↓reduceIte,
      hle, hadd, hzP, hshP, hshK, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc1 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13, hax⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7c80") ?_
    refine ⟨isSome_at L.L7c80, ?_, ?_⟩
    · rw [T.L7c80]
      refine ⟨_, c0, _, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, hst, hne, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h14, h13, hax⟩ := hR.down
    rename_i hg0 _ _
    have hdec := dec32 g (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rw [T.L7bb3_1]
      refine ⟨_, c0, _, j, kk, g - 1, xx, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, hxx,
        hkk, by omega, ?_, ?_, ?_, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h14, h13, hax, hdec, hfix]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, h14]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7bb3_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb3_1" ⟨"ff_aac_sbr_apply.L7bb3_1", B.L7bb3_1, some "ff_aac_sbr_apply.L7bb3_2"⟩ := by
  info_off
  obtain ⟨-, -, -, -, hHG, -⟩ := hc
  have hHG' := PLift.up hHG
  clear hHG
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne,
    hj, hxx, hkk, hg, hax, hdi, hsi, hm⟩ := T.L7bb3_1.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  subst hne
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hTW : TabWF y := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hpj : u8 y.pstart j + u8 y.pnum j ≤ 32 := hTW.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  have hdc : DWF True (y.d ch) := by
    unfold Args.d; split
    · exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => hst
    · rename_i hc0'; exact hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.mono fun _ => ⟨hst, hK.2.live hst hc0'⟩
  have hlv := hdc.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 trivial
  have hteN : u8 (y.d ch).te (y.d ch).nenv ≤ 19 := hlv.2.1 _ (Nat.le_refl _)
  have hte0 : u8 (y.d ch).te 0 < u8 (y.d ch).te (y.d ch).nenv :=
    lt_of_mono (fun e => u8 (y.d ch).te e) _ hlv.2.2 hlv.1
  have htl : (y.d ch).te.length = 10 := hdc.2.2.1
  have hn8 : (y.d ch).nenv ≤ 8 := hdc.2.2.2.2.1
  have hn1 : 0 < (y.d ch).nenv := hlv.1
  clear hlv
  have hal1 : isAligned 32 (arg1 t₀) = true := hC.2.1
  have halps : isAligned 16 (lab "ps_mask") = true := hC.2.2.2.2.2.2.2.2.2.2.2.1.1
  simp only [Mm, ApplyF] at hm
  rw [applyF_dpair y t₀ ch hch] at hm
  simp only [DArrW, Blocks] at hm
  -- M4-F1 closed: the entry has `g < n_q ≤ 5` (TabWF F2/F5 through the HfGen loop), so `bw_array[g]`
  -- is inside its own 20-byte Block.
  simp only [DScW] at hm
  rw [te_split (y.d ch).te _ (y.d ch).nenv hn1 (by omega) (by omega)] at hm
  simp only [Mm, ApplyF, FrH, ScW, TabW, DScW, DArrW, ArrW, DspW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4,
    lab, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hXh := carve_at (t₀.regs.get64 .rsi + 488544#64) 20480 (320 * kk + 16 + 16 * u8 (y.d ch).te 0)
    (16 * (u8 (y.d ch).te (y.d ch).nenv - u8 (y.d ch).te 0)) (by omega) (by decide)
  have hXl := carve_at (t₀.regs.get64 .rsi + 478304#64) 10240 (320 * (u8 y.pstart j + xx) + 16 * u8 (y.d ch).te 0)
    (16 * (u8 (y.d ch).te (y.d ch).nenv - u8 (y.d ch).te 0) + 16) (by omega) (by decide)
  have hA0 := carve_at (t₀.regs.get64 .rsi + 547936#64) 512 (8 * (u8 y.pstart j + xx)) 8 (by omega) (by decide)
  have hA1 := carve_at (t₀.regs.get64 .rsi + 548448#64) 512 (8 * (u8 y.pstart j + xx)) 8 (by omega) (by decide)
  rw [hXh, hXl, hA0, hA1, call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  rw [res_k0 hSt] at hm
  simp only [dA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hbx
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h8, hax, h15, h12, h14, h13, hdi, hsi⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7bb3_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8, Nat.reducePow,
      Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, hax, h15, h12, h14, h13,
      hdi, hsi, BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, BitVec.add_assoc,
    BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try (guard_target =ₛ 0 + g * 4 + 4 ≤ 20; omega)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.zero_add, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  -- the call
  obtain ⟨hrsp, hrbp, hsl, hn, hbx, h8, hax, h15, h12, h14, h13, hdi, hsi⟩ := hR.down
  simp only [Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hbx hdi hsi
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve 0 (t₀.regs.get64 .rsp - 464#64),
    (16 * (((if ch = 0 then y.d0 else y.d1).te.getD (if ch = 0 then y.d0 else y.d1).nenv 0).toNat - ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat)) ?@ (t₀.regs.get64 .rsi + (488544#64 + BitVec.ofNat 64 (320 * kk + 16 + 16 * ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat))),
    (16 * (((if ch = 0 then y.d0 else y.d1).te.getD (if ch = 0 then y.d0 else y.d1).nenv 0).toNat - ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat) + 16) ?@ (t₀.regs.get64 .rsi + (478304#64 + BitVec.ofNat 64 (320 * ((y.pstart.getD j 0).toNat + xx) + 16 * ((if ch = 0 then y.d0 else y.d1).te.getD 0 0).toNat))),
    8 ?@ (t₀.regs.get64 .rsi + (547936#64 + BitVec.ofNat 64 (8 * ((y.pstart.getD j 0).toNat + xx)))),
    8 ?@ (t₀.regs.get64 .rsi + (548448#64 + BitVec.ofNat 64 (8 * ((y.pstart.getD j 0).toNat + xx)))), 16 ?@ lab "ps_mask"] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
  refine MachineWP.CallsTo.of_procSpec Rc hHG'.down
    (fun ra' => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun s' hpost => ?_⟩)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hdi, hsi, te2x, h12, h13, h14, h15,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  all_goals try simp (disch := omega) only [sx2, hg_sz, hg_xh, hg_xl]
  all_goals try simp only [hg_m8]
  · sep_mem hm
    sep_close hm
  · exact hg_lt _ _ hte0 (by omega)
  · exact hg_even _ _
  · refine hg_al _ _ _ hal1 ?_ ?_
    · simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    · omega
  · refine hg_al _ _ _ hal1 ?_ ?_
    · simp -implicitDefEqProofs only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    · omega
  · exact halps
  · try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, MachineData.pushRa, Width.bytesv, Width.bytes,
        Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
        BitVec.sub_sub_eight, BitVec.sub_sub_ofNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hdi, hsi, te2x, h12, h13, h14, h15,
        BitVec.add_assoc, BitVec.setWidth_eq, Blocks, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hpost
    try simp (disch := omega) only [sx2, hg_sz, hg_xh, hg_xl] at hpost
    try simp only [hg_m8] at hpost
    obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
    have hsp : ∀ a : BitVec 64, a - 464#64 + 8#64 = a - 456#64 := fun a => by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
    rw [hsp] at hrsp'
    have e := hRc'.down
    subst e
    refine MachineWP.nil_spec.le_wp s' ?_
    refine ⟨?_, ?_⟩
    · rw [T.L7bb3_2]
      refine ⟨_, c0, _, j, kk, g, xx, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, rfl, hj, hxx,
        hkk, hg, ?_⟩
      all_goals try (simp only [arg1, hbx', h12', h13', h14', h15', h12, h13, h14, h15]; done)
      have hn1' : 0 < (y.d ch).nenv := hn1
      have htl' : (y.d ch).te.length = 10 := htl
      have hn8' : (y.d ch).nenv ≤ 8 := hn8
      simp only [Mm, ApplyF]
      rw [applyF_dpair y t₀ ch hch]
      simp only [DArrW, Blocks]
      simp only [DScW]
      rw [te_split (y.d ch).te _ (y.d ch).nenv hn1' (by omega) (by omega)]
      simp only [Mm, ApplyF, FrH, ScW, TabW, DScW, DArrW, ArrW, DspW, CstW, Blocks, c4, sbrA, arg0, arg1, arg3,
        arg4, lab, BitVec.add_assoc, BitVec.reduceAdd]
      rw [hXh, hXl, hA0, hA1, call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      rw [res_k0 hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        dA, Args.d] at hm' ⊢
      sep_close hm'
    · simp only [lex_var, slot64, hrbp', h15', h14', h15, h14, BitVec.sub_sub_ofNat, Nat.reduceAdd] at hn ⊢
      sep_mem hm'
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      try rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7bb3_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7bb3_2" ⟨"ff_aac_sbr_apply.L7bb3_2", B.L7bb3_2, some "ff_aac_sbr_apply.L7c5d"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, xx, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, h15, h12, h14, h13, y, hK, hCy, hst, hne, hj,
    hxx, hkk, hg, hm⟩ := T.L7bb3_2.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnq : y.nq ≤ 5 := hCy.1.2.2.2.2.2.2.2.2.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  have hT := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.1 hst
  have hpl : y.pnum.length = 6 := hT.2.2.2.2.1
  have hP : u8 y.pstart j + u8 y.pnum j ≤ 32 := hT.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j hj
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [byte_split y.pnum _ j (by omega) (by omega)] at hm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
  rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at hbx
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx, h15, h12, h14, h13⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hk1 := ofNat_succ64 kk
  have hzx := zx32 y.npatch (by omega)
  have hb256 : (y.pnum.getD j 0).toNat < 256 := UInt8.toNat_lt _
  have hx1 : BitVec.ofNat 32 xx + 1#32 = BitVec.ofNat 32 (xx + 1) := BitVec.ofNat_add_ofNat _ _
  have hzx1 := zx32n (xx + 1) (by omega)
  have hzb := zx32n (y.pnum.getD j 0).toNat (by omega)
  have hcf := cf_sub32 (xx + 1) (y.pnum.getD j 0).toNat (by omega) (by omega)
  dsimp only
  simp only [B.L7bb3_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h15, h12, h14, h13,
      BitVec.add_assoc, BitVec.setWidth_eq, hk1, hzx] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [sw32, hx1, hzx1, sw_byte32, hzb, hcf, CondCode.interp_c, StatusFlags.cf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, hbx, h15, h12, h14, h13⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b50") ?_
    refine ⟨isSome_at L.L7b50, ?_, ?_⟩
    · rw [T.L7b50]
      refine ⟨_, c0, _, j, kk + 1, g, xx + 1, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj,
        (by (try simp only [u8] at *); omega), (by (try simp only [u8] at *); omega), (by (try simp only [u8] at *); omega), ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, hbx,
          h15, h12, h14, h13, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hzx1]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc5 =>
    obtain ⟨hrsp, hrbp, hsl, hn, hbx, h15, h12, h14, h13⟩ := hR.down
    have hzx := zx32 y.npatch (by omega)
    refine ⟨?_, ?_⟩
    · rw [T.L7c5d]
      refine ⟨_, c0, _, j, kk + 1, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, hj, ?_,
        (by (try simp only [u8] at *); omega), (by (try simp only [u8] at *); omega), ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, hbx,
          h15, h12, h14, h13, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      rw [byte_split y.pnum _ j (by omega) (by omega)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      rw [BitVec.add_comm 478292#64 (BitVec.ofNat 64 j)]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hzx1]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, h14, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7c5d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7c5d" ⟨"ff_aac_sbr_apply.L7c5d", B.L7c5d, some "ff_aac_sbr_apply.L7c80"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, j, kk, g, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h15, h12, h13, y, hK, hCy, hst, hne, hj, hrax,
    hg, hps, hm⟩ := T.L7c5d.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hnp : y.npatch ≤ 6 := hCy.1.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  simp only [arg1] at h8
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hj1 := ofNat_succ64 j
  have hzx := zx_ofNat y.npatch (by omega)
  have hcf := cf_sub64 (j + 1) y.npatch (by omega) (by omega)
  have hzf := zf_sub64 (j + 1) 6 (by omega) (by omega)
  have hkk : kk ≤ 64 := by omega
  dsimp only
  simp only [B.L7c5d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h8, h15, h12, h13, hrax,
      BitVec.add_assoc, BitVec.setWidth_eq, hj1, hzx] at *
  all_goals try simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
    StatusFlags.from_result.Remaining.cf_mk, StatusFlags.zf_from_result, hcf, hzf, Bool.not_eq_true',
    Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc1 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L8b4f") ?_
    refine ⟨isSome_at L.L8b4f, ?_, ?_⟩
    · rw [T.L8b4f]
      refine ⟨_, c0, _, kk, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, hst, hne, hkk, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hj1, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hj1]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc2 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h15, h12, h13, hrax⟩ := hR.down
    rename_i hz hc
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7b2d") ?_
    refine ⟨isSome_at L.L7b2d, ?_, ?_⟩
    · rw [T.L7b2d]
      refine ⟨_, c0, _, j + 1, kk, g, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, ?_, ?_, y, hK, hCy, hst, hne, by omega, ?_,
        hg, hps, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp, h8, hbx,
          h15, h12, h13, hrax, hj1, hzx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, h15, hj1]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, h15, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc3 =>
    exfalso
    rename_i hz hc
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7c80 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7c80" ⟨"ff_aac_sbr_apply.L7c80", B.L7c80, some "ff_aac_sbr_apply.L7c80_1"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, y, hK, hCy, hst, hne, hm⟩ := T.L7c80.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, FnW, AcW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hbx, hn⟩ : _ ∧ _ ∧ _ ∧ _)
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hm0 := hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  dsimp only
  simp only [B.L7c80]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm0
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, BitVec.add_assoc,
    BitVec.reduceAdd] at *
  all_goals try sep_vals hm0
  all_goals try sep_mem hm0
  case vc3 =>
    obtain ⟨hrsp, hrbp, hbx, hn⟩ := hR.down
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7c80_1]
        refine ⟨ch, c0, _, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, y, hK, hCy, hst, rfl, ?_⟩
        · rw [hsv.1, hbx]
        simp only [Mm, ApplyF, FrH, ScW, TabW, FnW, AcW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
          BitVec.reduceAdd]
        rw [call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        try rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7c80_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7c80_1" ⟨"ff_aac_sbr_apply.L7c80_1", B.L7c80_1, some "ff_aac_sbr_apply.L7cb0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, y, hK, hCy, hst, hne, hm⟩ := T.L7c80_1.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7c80_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc1 =>
    obtain ⟨hrsp, hrbp, hsl, hn, hbx⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7ce0") ?_
    refine ⟨isSome_at L.L7ce0, ?_, ?_⟩
    · rw [T.L7ce0]
      refine ⟨_, c0, _, hC, ⟨?_, ?_⟩, hch, hc0, ?_, y, hK, hCy, hst, hne, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          hbx]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7cb0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7cb0" ⟨"ff_aac_sbr_apply.L7cb0", B.L7cb0, some "ff_aac_sbr_apply.L7cbf"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, y, hK, hCy, hst, hne, h12, hm⟩ := T.L7cb0.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [arg1] at h8
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hkx : y.kx1 ≤ 32 := hCy.1.2.1
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hzk := zx32n y.kx1 (by omega)
  have had32 : BitVec.ofNat 32 y.m1 + BitVec.ofNat 32 y.kx1 = BitVec.ofNat 32 (y.m1 + y.kx1) := BitVec.ofNat_add_ofNat _ _
  have hzs := zx32n (y.m1 + y.kx1) (by omega)
  have hsub := sub32z (y.m1 + y.kx1) y.kx1 (by omega) (by omega)
  have hcf := cf_sub32 (y.m1 + y.kx1) y.kx1 (by omega) (by omega)
  have hzf := zf_sub32 (y.m1 + y.kx1) y.kx1 (by omega) (by omega)
  dsimp only
  simp only [B.L7cb0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h8, hbx, h12,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [BitVec.ofInt_natCast, sw32, hzk, hzs, had32, hsub, hcf, hzf,
    Nat.add_sub_cancel, CondCode.interp_be, StatusFlags.cf_from_result, StatusFlags.from_result.Remaining.cf_mk,
    StatusFlags.zf_from_result, Bool.or_eq_true, Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc2 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7ce4") ?_
    refine ⟨isSome_at L.L7ce4, ?_, ?_⟩
    · rw [T.L7ce4]
      refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          h8, hbx]
        done
      simp only [Mm, ApplyF, FrC, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ := hR.down
    refine ⟨?_, ?_⟩
    · rw [T.L7cbf]
      refine ⟨_, c0, _, y.kx1, y.m1, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, hst, hne, by omega, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          h8, hbx, h12]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7cbf (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7cbf" ⟨"ff_aac_sbr_apply.L7cbf", B.L7cbf, some "ff_aac_sbr_apply.L7ce0"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMs, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, kk, cnt, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, h12, hax, y, hK, hCy, hst, hne, hkc, hm⟩ :=
    T.L7cbf.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, FnW, AcW, ArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hX := carve_at (t₀.regs.get64 .rsi + 488544#64) 20480 (320 * kk) (320 * cnt) (by omega) (by decide)
  rw [hX, call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hm0 := hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
    (320 * cnt) ?@ (t₀.regs.get64 .rsi + 488544#64 + BitVec.ofNat 64 (320 * kk))] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  have hR := PLift.up (⟨hrsp, hrbp, hbx, hn⟩ : _ ∧ _ ∧ _ ∧ _)
  have hsx := sx_kk kk (by omega)
  have hs1 := shl320 kk (by omega)
  have hs2 := shl320b cnt (by omega)
  dsimp only
  simp only [B.L7cbf]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "memset" hMs]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx, h12, hax,
      BitVec.toNat_ofNat, Nat.reduceEqDiff, ↓reduceIte, AddrIndex.offset64_scale4, hsx, hs1, hs2] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm0
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, BitVec.add_assoc,
    BitVec.reduceAdd] at *
  all_goals try sep_vals hm0
  all_goals try sep_mem hm0
  case vc2 =>
    obtain ⟨hrsp, hrbp, hbx, hn⟩ := hR.down
    have hcn : (BitVec.ofNat 64 (320 * cnt)).toNat = 320 * cnt := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd, Blocks, hcn]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd, Blocks, hcn]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
        Nat.reduceAdd, BitVec.reduceAdd, Blocks, hcn] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      have e := hRc'.down
      subst e
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7ce0]
        refine ⟨ch, c0, _, hC, ⟨hrsp', hrbp'⟩, hch, hc0, ?_, y, hK, hCy, hst, rfl, ?_⟩
        · rw [hsv.1, hbx]
        simp only [Mm, ApplyF, FrH, ScW, TabW, FnW, AcW, ArrW, Blocks, c4, sbrA, arg0, arg1, arg3, arg4,
          BitVec.add_assoc, BitVec.reduceAdd]
        rw [carve_at (t₀.regs.get64 .rsi + 488544#64) 20480 (320 * kk) (320 * cnt) (by omega) (by decide),
          call_res k hSt]
        simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
        try simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm' ⊢
        sep_close hm'
      · simp only [lex_var, slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
        try rw [← hn]
        var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7ce0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7ce0" ⟨"ff_aac_sbr_apply.L7ce0", B.L7ce0, some "ff_aac_sbr_apply.L7ce4"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, hC, ⟨hrsp, hrbp⟩, hch, hc0, hbx, y, hK, hCy, hst, hne, hm⟩ := T.L7ce0.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, hbx⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _)
  dsimp only
  simp only [B.L7ce0]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, hbx,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals (
    obtain ⟨hrsp, hrbp, hsl, hn, hbx⟩ := hR.down
    refine ⟨?_, ?_⟩
    · rw [T.L7ce4]
      refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          hbx]
        done
      simp only [Mm, ApplyF, FrC, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  )

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L8b4f (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L8b4f" ⟨"ff_aac_sbr_apply.L8b4f", B.L8b4f, some "ff_aac_sbr_apply.L8b6b"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, ne, kk, hC, ⟨hrsp, hrbp⟩, hch, hc0, h8, hbx, h12, y, hK, hCy, hst, hne, hkk, hm⟩ := T.L8b4f.mp hs
  clear hs
  simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [arg1] at h8
  have hsl : slot64 s₀ 0x1a0 = BitVec.ofNat 64 ch := by
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  simp only [lex_var, hsl] at hn
  have hR := PLift.up (⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ :
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  have hkx : y.kx1 ≤ 32 := hCy.1.2.1
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hzk := zx32n y.kx1 (by omega)
  have had32 : BitVec.ofNat 32 y.m1 + BitVec.ofNat 32 y.kx1 = BitVec.ofNat 32 (y.m1 + y.kx1) := BitVec.ofNat_add_ofNat _ _
  have hzs := zx32n (y.m1 + y.kx1) (by omega)
  have hcf := cf_sub32 (y.m1 + y.kx1) kk (by omega) (by omega)
  have hzf := zf_sub32 (y.m1 + y.kx1) kk (by omega) (by omega)
  dsimp only
  simp only [B.L8b4f]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try (subst s₀)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      AddrIndex.offset64_scale1, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero, Width.bytes, BitVec.ofNat_eq_ofNat,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h8, hbx, h12,
      BitVec.add_assoc, BitVec.setWidth_eq] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    Int64.ofBitVec_toBitVec] at *
  all_goals try simp only [BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp only [BitVec.ofInt_natCast, sw32, hzk, hzs, had32, hcf, hzf,
    CondCode.interp_a, StatusFlags.cf_from_result, StatusFlags.from_result.Remaining.cf_mk,
    StatusFlags.zf_from_result, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not] at *
  case vc3 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ := hR.down
    rename_i hz
    have hgt : kk < y.m1 + y.kx1 := by omega
    have hsub := sub32z (y.m1 + y.kx1) kk (by omega) (by omega)
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7cbf") ?_
    refine ⟨isSome_at L.L7cbf, ?_, ?_⟩
    · rw [T.L7cbf]
      refine ⟨_, c0, _, kk, y.m1 + y.kx1 - kk, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, ?_, y, hK, hCy, hst, hne, by omega, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          h8, hbx, h12, hsub]
        done
      simp only [Mm, ApplyF, FrH, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step
  case vc4 =>
    obtain ⟨hrsp, hrbp, hsl, hn, h8, hbx, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7ce4") ?_
    refine ⟨isSome_at L.L7ce4, ?_, ?_⟩
    · rw [T.L7ce4]
      refine ⟨_, c0, hC, ⟨?_, ?_⟩, hch, hc0, ?_, ?_, y, hK, hCy, hst, ?_⟩
      all_goals try
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, arg1, dA, sbrA, Nat.reduceMul,
          Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, hrsp, hrbp,
          h8, hbx]
        done
      simp only [Mm, ApplyF, FrC, ScW, TabW, c4, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd]
      sep_close hm
    · left
      simp only [lex_var, slot64, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp,
        BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_mem hm
      simp -implicitDefEqProofs only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat] at hn ⊢
      rw [← hn]
      var_step

end Kraken.Examples.Sbr.Apply
