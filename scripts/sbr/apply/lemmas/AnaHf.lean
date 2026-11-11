
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
