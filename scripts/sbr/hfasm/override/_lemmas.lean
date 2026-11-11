/-! ## hfasm-2: lemmas for the `Lb426`/`y1..y14` copy blocks (direct `vmovups` row copies) -/


omit [CodeEnv] in
theorem off_toNat3 (a : BitVec 64) (b c o d : Nat) (hb : b ≤ c) (hc : c < 2 ^ 32) (ho : o < 2 ^ 32)
    (hd : d < 2 ^ 32) :
    (a + BitVec.ofNat 64 c + BitVec.ofNat 64 o + BitVec.ofNat 64 d - (a + BitVec.ofNat 64 b)).toNat
      = c - b + o + d := by
  have : a + BitVec.ofNat 64 c + BitVec.ofNat 64 o + BitVec.ofNat 64 d - (a + BitVec.ofNat 64 b)
      = BitVec.ofNat 64 (c - b + o + d) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.toNat_ofNat]; omega

/-- `T` with `DataW` in front of the rest (behind the name `TR`). -/
def TR (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData)
    (IC : Mem 64 → Prop) (FR : (Mem 64 → Prop) → Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x290#64) ⋆ (Reserve k (r - 0x290#64) ⋆ (ScW x t₀ ⋆ (FnW fs t₀
    ⋆ (TeW x t₀ ⋆ (EaW x t₀ ⋆ (IC ⋆ FR (Rest x.R ra t₀)))))))

theorem T_eq_TR (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData)
    (IC : Mem 64 → Prop) (FR : (Mem 64 → Prop) → Mem 64 → Prop) :
    T k fs x ra t₀ IC FR = DataW x t₀ ⋆ TR k fs x ra t₀ IC FR := by
  simp only [T, TR]
  ac_rfl

/-- Two disjoint 192-byte pieces of `g_temp`/`q_temp` (in either order). -/
theorem DataW_carve_y2 (x : HfArgs) (t : MachineData) (b₁ b₂ : BitVec 64)
    (h₁ : (b₁ - (arg3 t + 0x11130#64)).toNat + 192 ≤ 16128)
    (h₂ : (b₂ - (arg3 t + 0x11130#64)).toNat + 192 ≤ 16128)
    (hd : (b₁ - (arg3 t + 0x11130#64)).toNat + 192 ≤ (b₂ - (arg3 t + 0x11130#64)).toNat
      ∨ (b₂ - (arg3 t + 0x11130#64)).toNat + 192 ≤ (b₁ - (arg3 t + 0x11130#64)).toNat) :
    ∃ H, DataW x t = Blocks [(b₁, 192), (b₂, 192)] ⋆ H := by
  have e : ∃ H1, (Block (arg3 t + 0x11130#64) 16128 : Mem 64 → Prop)
      = 192 ?@ b₁ ⋆ (192 ?@ b₂ ⋆ H1) := by
    rcases hd with hd | hd
    · exact Block.carve2_ex hd h₂ (by omega)
    · obtain ⟨H1, e1⟩ := Block.carve2_ex hd h₁ (by omega)
      exact ⟨H1, by rw [show (Block (arg3 t + 0x11130#64) 16128 : Mem 64 → Prop)
        = 16128 ?@ (arg3 t + 0x11130#64) from rfl, e1]; ac_rfl⟩
  obtain ⟨H1, e1⟩ := e
  refine ⟨H1 ⋆ DataWG x t, ?_⟩
  rw [DataW_G, e1]
  simp only [Blocks, Std.ExtHashMap.sep_assoc]

/-- One 192-byte piece of `g_temp`/`q_temp`. -/
theorem DataW_carve_y1 (x : HfArgs) (t : MachineData) (b : BitVec 64)
    (h : (b - (arg3 t + 0x11130#64)).toNat + 192 ≤ 16128) :
    ∃ H, DataW x t = Blocks [(b, 192)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex (a := arg3 t + 0x11130#64) (b := b) (len := 16128) (n := 192) h (by omega)
  refine ⟨H1 ⋆ DataWG x t, ?_⟩
  rw [DataW_G, e1]
  simp only [Blocks, Std.ExtHashMap.sep_assoc]

/-- closer for the y blocks (no `congr`). -/
macro "y_close" : tactic =>
  `(tactic| first | omega | with_reducible assumption | grind_cells' | (refine hf_xb ?_ ?_ <;> first | with_reducible assumption | with_reducible rfl))

-- from hfasm-2 (E region)
/-! ## hfasm-2: lemmas for the E k=4..7 blocks -/



/-! row address of the E-loop heads s_k (`r12 = C + 0x130b0 + 192*(hSL + 2 te_k)`) -/

omit [CodeEnv] in
theorem hf_zext8 (t : Nat) (ht : t < 128) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t))) = BitVec.ofNat 64 t := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem hf_r14_two (t : Nat) (ht : t < 128) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t))
      + BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t)))).toNat = 2 * t := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem hf_add2 (t : Nat) (ht : t < 2 ^ 32) :
    BitVec.ofNat 64 t + BitVec.ofNat 64 t * 2#64 = BitVec.ofNat 64 (3 * t) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_mul]
  omega

omit [CodeEnv] in
theorem hf_shl_k (n k : Nat) (hn : n * 2 ^ k < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) <<< k) = BitVec.ofNat 64 (n * 2 ^ k) := by
  have h1 : n < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)) hn
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (Nat.lt_trans h1 (by decide)),
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn]

omit [CodeEnv] in
theorem hf_shl7 (t : Nat) (ht : t < 128) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 t + BitVec.ofNat 64 t * 2#64) <<< 7)
      = BitVec.ofNat 64 (384 * t) := by
  rw [hf_add2 t (by omega), hf_shl_k _ _ (by rw [show (2:Nat) ^ 7 = 128 from rfl]; omega)]
  congr 1; rw [show (2:Nat) ^ 7 = 128 from rfl]; omega

omit [CodeEnv] in
theorem hf_shl6 (h : Nat) (hh : h < 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 h + BitVec.ofNat 64 h * 2#64) <<< 6)
      = BitVec.ofNat 64 (192 * h) := by
  rw [hf_add2 h (by omega), hf_shl_k _ _ (by rw [show (2:Nat) ^ 6 = 64 from rfl]; omega)]
  congr 1; rw [show (2:Nat) ^ 6 = 64 from rfl]; omega

omit [CodeEnv] in
theorem hf_s_row (C : BitVec 64) (t h : Nat) (ht : t < 128) (hh : h < 16) :
    BitVec.setWidth 64 78000#64 + (C + (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t)))
        + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t))) * 2#64) <<< 7)
      + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 h + BitVec.ofNat 64 h * 2#64) <<< 6)) * 1#64)
    = C + 78000#64 + BitVec.ofNat 64 (192 * (h + (BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t))
          + BitVec.setWidth 32 (BitVec.setWidth 8 (BitVec.ofNat 64 t)))).toNat)) := by
  rw [hf_r14_two t ht, hf_zext8 t ht, hf_shl7 t ht, hf_shl6 h hh, BitVec.mul_one,
    show BitVec.setWidth 64 78000#64 = 78000#64 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## hfasm-2: filter loop lemmas (Lb248 Lb280 v1 Lb340 w1) -/

/-- `DataW` with the `g_temp`/`q_temp` block in front. -/
theorem hf2_DataW_G (x : HfArgs) (t : MachineData) :
    DataW x t = Block (arg3 t + 0x11130#64) 16128 ⋆ (Blocks [(arg0 t, 19456), (arg1 t, 20480),
      (arg2 t + 0x5eac0#64, 4608), (lab "ff_sbr_noise_table", 4160), (lab "ps_noise0", 16),
      (lab "ps_noise13", 48), (lab "ps_noise2", 16), (arg0 t + 19456#64, 24 - 24 * x.ypos)]
      ⋆ (4 ?@ lab "LCPI17_6" ⋆ (4 ?@ lab "LCPI17_7" ⋆ (4 ?@ lab "LCPI17_8" ⋆ (4 ?@ lab "LCPI17_9"
      ⋆ (4 ?@ lab "LCPI17_10" ⋆ (4 ?@ lab "LCPI17_12"
      ⋆ Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11"))))))) := by
  simp only [DataW, Blocks]
  ac_rfl

omit [CodeEnv] in
theorem hf2_inG (A R D : BitVec 64) (o c n : Nat) (hD : D + BitVec.ofNat 64 c = 0#64)
    (hc : c ≤ 0x1f80 + o) (hc' : c < 2 ^ 32) (ho : o < 2 ^ 32) (hR : R.toNat < 2 ^ 32)
    (hn : 0x1f80 + o - c + R.toNat + n ≤ 16128) :
    (A + 0x130b0#64 + BitVec.ofNat 64 o + R + D - (A + 0x11130#64)).toNat + n ≤ 16128 := by
  have eD : D = 0#64 - BitVec.ofNat 64 c := by
    rw [← hD, BitVec.add_sub_cancel]
  have e1 : A + 0x130b0#64 + BitVec.ofNat 64 o + R + D - (A + 0x11130#64)
      = 0x1f80#64 + BitVec.ofNat 64 o + R - BitVec.ofNat 64 c := by
    rw [eD]; grind
  have e : 0x1f80#64 + BitVec.ofNat 64 o + R - BitVec.ofNat 64 c
      = BitVec.ofNat 64 (0x1f80 + o - c + R.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e1, e, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem hf2_inG0 (A R : BitVec 64) (o n : Nat) (ho : o < 2 ^ 32) (hR : R.toNat < 2 ^ 32)
    (hn : 0x1f80 + o + R.toNat + n ≤ 16128) :
    (A + 0x130b0#64 + BitVec.ofNat 64 o + R - (A + 0x11130#64)).toNat + n ≤ 16128 := by
  have e1 : A + 0x130b0#64 + BitVec.ofNat 64 o + R - (A + 0x11130#64)
      = 0x1f80#64 + BitVec.ofNat 64 o + R := by grind
  have e : 0x1f80#64 + BitVec.ofNat 64 o + R = BitVec.ofNat 64 (0x1f80 + o + R.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e1, e, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- A stack-buffer access `rbp + X - c` (`rbp = rsp - 8`) in the cell at `rsp - (c + 8)`. -/
theorem hf2_inS' (r X D Cb : BitVec 64) (c n len : Nat) (hC : BitVec.ofNat 64 (c + 8) = Cb)
    (hD : D + BitVec.ofNat 64 c = 0#64) (hX : X.toNat + n ≤ len) :
    (r - 8#64 + X + D - (r - Cb)).toNat + n ≤ len := by
  subst hC
  have e : r - 8#64 + X + D - (r - BitVec.ofNat 64 (c + 8)) = X := by
    rw [BitVec.ofNat_add]
    have eD : D = 0#64 - BitVec.ofNat 64 c := by
      rw [← hD, BitVec.add_sub_cancel]
    rw [eD]; grind
  rw [e]; exact hX

omit [CodeEnv] in
theorem hf2_mul1 (r : BitVec 64) : (r * 1#64).toNat = r.toNat := by
  rw [BitVec.mul_one]

omit [CodeEnv] in
theorem hf2_mul4 (r : BitVec 64) (h : r.toNat < 2 ^ 32) : (r * 4#64).toNat = r.toNat * 4 := by
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega



omit [CodeEnv] in
theorem hf2_c8_split (a : BitVec 64) (v : Int) :
    (Int.toBytes 8 v =@ a) = (Int.toBytes 4 v =@ a ⋆ Int.toBytes 4 (v / 256 ^ 4) =@ (a + 4#64)) := by
  show Eq ((Int.toBytes 8 v).At a) = _
  rw [show (8:Nat) = 4 + 4 from rfl, Int.toBytes_add, At_append_sep _ _ _ (by simp [Int.toBytes_length]),
    Int.toBytes_length]
  rfl

omit [CodeEnv] in
theorem hf2_ld_lo (m : Mem 64) (a : BitVec 64) (k : Nat) (hk : k < 2 ^ 31) (R : Mem 64 → Prop)
    (h : m =⋆ (Int.toBytes 8 (BitVec.ofNat 64 k).toInt =@ a) ⋆ R) : m.loadInt a 4 = some (k : Int) := by
  rw [hf2_c8_split, Std.ExtHashMap.sep_assoc] at h
  rw [Mem.Val.loadInt h (Mem.Split.here_val _ _ _) (Int.toBytes_length _ _) (by decide), ofBytes_toBytes]
  have e : (BitVec.ofNat 64 k).toInt = (k : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofNat]; split <;> omega
  rw [e, Int.take]
  congr 1
  omega

-- index-register byte offset: `rax*1` or `rax*4`.
set_option hygiene false in
macro "hf2_idx" : tactic => `(tactic| first
  | (rw [hf2_mul1]; omega)
  | (rw [hf2_mul4 _ (by omega)]; omega)
  | omega)

set_option hygiene false in
macro "hf2_ldGc " c:term : tactic => `(tactic|
  ((with_reducible refine hf2_inG _ _ _ _ $c _ ?_ ?_ ?_ ?_ ?_ ?_) <;> first | decide | hf2_idx))

-- G/Q row read in the filter loops (needs `hG`, `h8`, `hh4`, `hteB`, `hm48`).
set_option hygiene false in
macro "hf2_ldG" : tactic => `(tactic| (
  (with_reducible refine Block.loadInt_isSome hG ?_); rw [h8, hh4]
  first
  | ((with_reducible refine hf2_inG0 _ _ _ _ ?_ ?_ ?_) <;> hf2_idx)
  | hf2_ldGc 0xc0 | hf2_ldGc 0x180 | hf2_ldGc 0x240 | hf2_ldGc 0x300
  | hf2_ldGc 0x1f80 | hf2_ldGc 0x2040 | hf2_ldGc 0x2100 | hf2_ldGc 0x21c0 | hf2_ldGc 0x2280))

set_option hygiene false in
macro "hf2_inStc " c:term : tactic => `(tactic|
  ((with_reducible refine hf2_inS' _ _ _ _ $c _ _ ?_ ?_ ?_) <;> first | decide | hf2_idx))

set_option hygiene false in
macro "hf2_inSt" : tactic => `(tactic| first | hf2_inStc 0x280 | hf2_inStc 0x1c0)

-- spill row buffers at `rsp-0x288`, `rsp-0x1c8` (2nd/3rd cells of the frame)
set_option hygiene false in
macro "hf2_st" : tactic => `(tactic| first
  | ((with_reducible refine Block.loadInt_isSome_split hm (Split.right (Split.here_block _ _ _) _) ?_); hf2_inSt)
  | ((with_reducible refine Block.loadInt_isSome_split (Block.storeInt_split hm (Split.right (Split.here_block _ _ _) _) ?_ _) (Split.right (Split.right (Split.here_block _ _ _) _) _) ?_) <;> hf2_inSt)
  | ((with_reducible refine Block.storeInt_split (Block.storeInt_split hm (Split.right (Split.here_block _ _ _) _) ?_ _) (Split.right (Split.right (Split.here_block _ _ _) _) _) ?_ _) <;> hf2_inSt))
/-! ## hfasm-2: main-region lemmas (m1 m2 m3 Laf40 Lafd9 Lb400 r0) -/


omit [CodeEnv] in
theorem hf2_m4_and (m : Nat) (h : m ≤ 48) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m) &&& BitVec.setWidth 32 2147483644#64)
      = BitVec.ofNat 64 (m / 4 * 4) := by
  have : ∀ m, m < 49 → BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 m) &&& BitVec.setWidth 32 2147483644#64)
      = BitVec.ofNat 64 (m / 4 * 4) := by decide
  exact this m (by omega)

omit [CodeEnv] in
theorem hf2_m4_shl (m : Nat) (h : m ≤ 48) :
    BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.ofNat 64 m)).ushiftRight 2 &&& BitVec.setWidth 32 536870911#64) <<< (4 : Nat)
      = BitVec.ofNat 64 (16 * (m / 4)) := by
  have : ∀ m, m < 49 → BitVec.setWidth 64 ((BitVec.setWidth 32 (BitVec.ofNat 64 m)).ushiftRight 2 &&& BitVec.setWidth 32 536870911#64) <<< (4 : Nat)
      = BitVec.ofNat 64 (16 * (m / 4)) := by decide
  exact this m (by omega)

omit [CodeEnv] in
theorem hf2_r9mul (x : HfArgs) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (hSL x)) <<< (6 : Nat))
      + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (hSL x)) <<< (6 : Nat)) * 2#64
      = BitVec.ofNat 64 (192 * hSL x) := by
  unfold hSL; split <;> rfl

omit [CodeEnv] in
theorem hf2_m2_e0 (a r : BitVec 64) :
    BitVec.setWidth 64 78000#64 + (a + r) = a + 78000#64 + r := by
  simp only [BitVec.setWidth_eq]; ac_rfl

omit [CodeEnv] in
theorem hf2_m2_d8 (a : BitVec 64) (kx : Nat) :
    BitVec.setWidth 64 8#64 + (a + BitVec.ofNat 64 kx * 8#64) = a + BitVec.ofNat 64 (8 * kx + 8) := by
  simp only [BitVec.setWidth_eq]
  rw [BitVec.ofNat_add, BitVec.ofNat_mul, BitVec.mul_comm]; ac_rfl

omit [CodeEnv] in
theorem hf2_sub1 (m : Nat) (h : 1 ≤ m) (h2 : m ≤ 48) : BitVec.ofNat 64 m - 1#64 = BitVec.ofNat 64 (m - 1) := by
  have : ∀ m, m < 49 → BitVec.ofNat 64 m - 1#64 = BitVec.ofNat 64 (m - 1) ∨ m = 0 := by decide
  exact (this m (by omega)).resolve_right (by omega)

omit [CodeEnv] in
theorem hf2_addm1 (m : Nat) (h : 1 ≤ m) (h2 : m ≤ 48) :
    BitVec.ofNat 64 m + 18446744073709551615#64 = BitVec.ofNat 64 (m - 1) := by
  have : ∀ m, m < 49 → BitVec.ofNat 64 m + 18446744073709551615#64 = BitVec.ofNat 64 (m - 1) ∨ m = 0 := by decide
  exact (this m (by omega)).resolve_right (by omega)

omit [CodeEnv] in
theorem hf2_m1addm1 (m : Nat) (h : 1 ≤ m) (h2 : m ≤ 48) :
    18446744073709551615#64 + BitVec.ofNat 64 m = BitVec.ofNat 64 (m - 1) := by
  rw [BitVec.add_comm]; exact hf2_addm1 m h h2

omit [CodeEnv] in
theorem hf2_r10b (r : BitVec 64) (x : HfArgs) (h : r.toNat % 256 = if x.smooth = 0 then 1 else 0)
    (h7 : x.smooth = 0) : (BitVec.setWidth 8 r).toInt = 1 := by
  simp only [h7, ite_true] at h
  have : BitVec.setWidth 8 r = 1#8 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; omega
  rw [this]; rfl



omit [CodeEnv] in
/-- m2's four stores into the four free 8-byte cells at the head of its frame. -/
theorem hf2_m2_frame {m : Mem 64} {R : Mem 64 → Prop} {r v1 v2 v3 v4 : BitVec 64}
    (h : m =⋆ 8 ?@ (r - 232#64) ⋆ (8 ?@ (r - 224#64) ⋆ (8 ?@ (r - 216#64) ⋆ (8 ?@ (r - 208#64) ⋆ R)))) :
    (((m.storeInt (r - 216#64) 8 v3.toInt).storeInt (r - 208#64) 8 v4.toInt).storeInt (r - 232#64) 8 v1.toInt).storeInt (r - 224#64) 8 v2.toInt
      =⋆ c8 (r - 232#64) v1 ⋆ (c8 (r - 224#64) v2 ⋆ (c8 (r - 216#64) v3 ⋆ (c8 (r - 208#64) v4 ⋆ R))) := by
  grind_cells'


-- from hfasm-1
/-- hfasm-1: normalize `c + (A + ofNat n)` (lea+add $imm row address) to `A + ofNat (n + c)`. -/
theorem hf_lit_add_row (A : BitVec 64) (n c : Nat) :
    (no_index (OfNat.ofNat c : BitVec 64)) + (A + BitVec.ofNat 64 n) = A + BitVec.ofNat 64 (n + c) := by
  rw [BitVec.ofNat_add]
  show BitVec.ofNat 64 c + _ = _
  ac_rfl

/-- hfasm-1: same as hf_lit_add_row for `c#64` literals (`BitVec.ofNat 64 c`). -/
theorem hf_lit_add_row' (A : BitVec 64) (n c : Nat) :
    BitVec.ofNat 64 c + (A + BitVec.ofNat 64 n) = A + BitVec.ofNat 64 (n + c) := by
  rw [BitVec.ofNat_add]
  ac_rfl

omit [CodeEnv] in
/-- hfasm-1 (La8f6): `mov %r10b,%r9b; shl $2,%r9d` with r9 = 0 and the low byte of r10 = b ≤ 1. -/
theorem hf1_r9_slot (old r10 : BitVec 64) (b : Nat) (hold : old = 0#64) (hb : r10.toNat % 256 = b)
    (hb1 : b ≤ 1) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (old.replaceLow (BitVec.setWidth 8 r10)) <<< 2)
      = BitVec.ofNat 64 (4 * b) := by
  have h1 := BitVec.toNat_replaceLow8_mod old (BitVec.setWidth 8 r10)
  have h2 := BitVec.toNat_replaceLow8_div old (BitVec.setWidth 8 r10)
  subst hold
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h1 h2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have : (BitVec.replaceLow 0#64 (BitVec.setWidth 8 r10)).toNat = b := by omega
  rw [this]
  omega

omit [CodeEnv] in
/-- hfasm-1 (La8f6): the slot value r9 = rsi = hSL x. -/
theorem hf1_r9_hSL (x : HfArgs) (old r10 : BitVec 64) (hold : old = 0#64)
    (h : r10.toNat % 256 = if x.smooth = 0 then 1 else 0) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (old.replaceLow (BitVec.setWidth 8 r10)) <<< 2)
      = BitVec.ofNat 64 (hSL x) := by
  rw [hf1_r9_slot old r10 _ hold h (by split <;> omega)]
  unfold hSL; split <;> rfl

omit [CodeEnv] in
theorem hf1_add2 (t : Nat) (ht : t < 2 ^ 32) :
    BitVec.ofNat 64 t + BitVec.ofNat 64 t * 2#64 = BitVec.ofNat 64 (3 * t) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_mul]
  omega

omit [CodeEnv] in
theorem hf1_shl_k (n k : Nat) (hn : n * 2 ^ k < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) <<< k) = BitVec.ofNat 64 (n * 2 ^ k) := by
  have h1 : n < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)) hn
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (Nat.lt_trans h1 (by decide)),
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn]

omit [CodeEnv] in
/-- hfasm-1: row address of s0 (`r12 = C + 0x130b0 + 192*(hSL + r14)`), te0 already zero-extended in rcx. -/
theorem hf1_s0_row (C R : BitVec 64) (t h : Nat) (ht : t < 128) (hh : h < 16) (hR : R.toNat = 2 * t) :
    BitVec.setWidth 64 78000#64 + (C + (BitVec.setWidth 64 (BitVec.setWidth 32
        (BitVec.ofNat 64 t + BitVec.ofNat 64 t * 2#64) <<< 7)
      + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 h + BitVec.ofNat 64 h * 2#64) <<< 6)) * 1#64)
    = C + 78000#64 + BitVec.ofNat 64 (192 * (h + R.toNat)) := by
  rw [hf1_add2 t (by omega), hf1_add2 h (by omega), hf1_shl_k _ _ (by rw [show (2:Nat) ^ 7 = 128 from rfl]; omega),
    hf1_shl_k _ _ (by rw [show (2:Nat) ^ 6 = 64 from rfl]; omega), BitVec.mul_one, hR,
    show BitVec.setWidth 64 78000#64 = 78000#64 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- hfasm-1 (La8f6): a 32-bit store of edx holding a small count n. -/
theorem hf1_toInt32 (r : BitVec 64) (n : Nat) (h : r.toNat % 2 ^ 32 = n) (hn : n < 2 ^ 31) :
    (BitVec.setWidth 32 r).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth]
  rw [h]
  split <;> omega


-- from hfasm-3
/-! ## hfasm-3: lemmas for the sine loop (Lb08f, n2, Lb140, Lb16c) -/


omit [CodeEnv] in
theorem hf_lea4 (a r : BitVec 64) (c : Nat) :
    a + BitVec.ofNat 64 c + r * 4#64 = a + BitVec.ofNat 64 (c + 4 * r.toNat) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega



omit [CodeEnv] in
theorem hf_and1_lt2 (y : BitVec 32) : (BitVec.setWidth 64 (y &&& BitVec.setWidth 32 1#64)).toNat < 2 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
  have := Nat.and_le_right (n := y.toNat) (m := 1 % 2 ^ 64 % 2 ^ 32)
  omega


omit [CodeEnv] in
theorem hf_toInt_sw32 (m : Nat) (h : m < 2 ^ 31) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 m)).toInt = (m : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split <;> omega

omit [CodeEnv] in
theorem hf_z32_ne (n c : Nat) (hn : n < c) (hc : c < 2 ^ 31) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.ofInt 32 (n : Int) - BitVec.setWidth 32 (BitVec.ofNat 64 c)) f) = false := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_eq_false_iff_ne, ne_eq]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt] at this
  simp at this
  omega


/-- Copy of hfasm's `FL2_read_i` (dev build only). -/
theorem hf3_read_i {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ : MachineData} {e i : Nat}
    {v : BitVec 128} {m : Mem 64} (h : m =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v))
    (hi : i < 2 ^ 64) :
    (BitVec.ofInt 64 ((m.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i := by
  rw [FL2_s38] at h
  rw [Mem.Val.loadInt h (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)]
  simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- Copy of hfasm's `FL2_read_v` (dev build only). -/
theorem hf3_read_v {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ : MachineData} {e i : Nat}
    {v : BitVec 128} {m : Mem 64} (h : m =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)) :
    BitVec.ofInt 128 ((m.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v := by
  rw [FL2_xv] at h
  rw [Mem.Val.loadInt h (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)]
  simp only [Option.getD_some]
  exact BitVec.ofInt_ofBytes_toBytes 128 16 rfl v


/-- `Lb140` entry from facts in the frame parameters `e i v` (no `IM`/`XV` terms). -/
theorem Lb140_rb {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ s : MachineData} {e i : Nat} {v : BitVec 128}
    (hE : (s.regs.get64 .r10).toNat = e) (h0 : HfC x t₀) (h1 : Base t₀ s) (h2 : e < x.nenv)
    (h3 : v.toNat % 2 ^ 32 ≤ 515) (h4 : v.toNat / 2 ^ 32 % 2 ^ 32 < 4)
    (h5 : x.te e * 2 ≤ i) (h6 : i < x.te (e + 1) * 2)
    (h7 : s.regs.get64 .rbx = arg0 t₀ + BitVec.ofNat 64 x.kx * 8#64 + BitVec.ofNat 64 (512 * i))
    (h8 : s.regs.get64 .r12 = arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * (hSL x + i)))
    (h9 : s.regs.get64 .r13 = arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * i) ∨ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x1c8#64)
    (h10 : s.regs.get64 .r14 = arg2 t₀ + 0x5f0c4#64 + BitVec.ofNat 64 (192 * e))
    (h11 : s.regs.get64 .r8 = arg3 t₀) (h12 : s.regs.get64 .r9 = BitVec.ofNat 64 (x.m - 1))
    (h13 : s.regs.get64 .rcx = BitVec.ofNat 64 x.m)
    (h14 : s.regs.get64 .r11 = arg0 t₀ + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i))
    (h15 : s.regs.get64 .r15 = BitVec.ofNat 64 i) (h16 : (s.regs.get64 .rdx).toNat < 2)
    (h17 : s.regs.get64 .rsi = arg0 t₀ + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i + 4 * (s.regs.get64 .rdx).toNat))
    (h18 : (s.regs.get64 .rdi).toNat % 2 = 0) (h19 : (s.regs.get64 .rdi).toNat + 1 < x.m)
    (hm : s.dmem =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)) :
    table k fs x ra t₀ "sbr_hf_assemble.Lb140" s := by
  have hte := h0.2.2.2.2.2.2.2.2.2.2.1 (e + 1) (by omega)
  have hI := hf3_read_i hm (by omega)
  have hV := hf3_read_v hm
  subst hE
  apply Lb140_tbl_Lb140
  rw [hI, hV]
  rw [Lb140_post_Lb140] at hm
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, hm⟩

/-- `Lb16c` entry from facts in `e i v`. -/
theorem Lb16c_rb {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ s : MachineData} {e i : Nat} {v : BitVec 128}
    (hE : (s.regs.get64 .r10).toNat = e) (h0 : HfC x t₀) (h1 : Base t₀ s) (h2 : e < x.nenv)
    (h3 : v.toNat % 2 ^ 32 ≤ 515) (h4 : v.toNat / 2 ^ 32 % 2 ^ 32 < 4)
    (h5 : x.te e * 2 ≤ i) (h6 : i < x.te (e + 1) * 2)
    (h7 : s.regs.get64 .rbx = arg0 t₀ + BitVec.ofNat 64 x.kx * 8#64 + BitVec.ofNat 64 (512 * i))
    (h8 : s.regs.get64 .r12 = arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * (hSL x + i)))
    (h9 : s.regs.get64 .r13 = arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * i) ∨ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x1c8#64)
    (h10 : s.regs.get64 .r14 = arg2 t₀ + 0x5f0c4#64 + BitVec.ofNat 64 (192 * e))
    (h11 : s.regs.get64 .r8 = arg3 t₀) (h12 : s.regs.get64 .r9 = BitVec.ofNat 64 (x.m - 1))
    (h13 : s.regs.get64 .rcx = BitVec.ofNat 64 x.m)
    (h14 : s.regs.get64 .r11 = arg0 t₀ + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i))
    (h15 : s.regs.get64 .r15 = BitVec.ofNat 64 i) (h16 : (s.regs.get64 .rdx).toNat < 2)
    (h18 : (s.regs.get64 .rdi).toNat % 2 = 0) (h19 : (s.regs.get64 .rdi).toNat ≤ x.m)
    (hm : s.dmem =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)) :
    table k fs x ra t₀ "sbr_hf_assemble.Lb16c" s := by
  have hte := h0.2.2.2.2.2.2.2.2.2.2.1 (e + 1) (by omega)
  have hI := hf3_read_i hm (by omega)
  have hV := hf3_read_v hm
  subst hE
  apply Lb16c_tbl_Lb140
  rw [hI, hV]
  rw [Lb140_post_Lb16c] at hm
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h18, h19, hm⟩

/-- `Lafa0` entry (frame `FL e`) from `Lb16c`-style facts in `e i`. -/
theorem Lafa0_rb {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ s : MachineData} {e i : Nat} {v : BitVec 128}
    (hE : (s.regs.get64 .r10).toNat = e) (h0 : HfC x t₀) (h1 : Base t₀ s) (h2 : e < x.nenv)
    (h5 : x.te e * 2 ≤ i) (h6 : i < x.te (e + 1) * 2)
    (h8 : s.regs.get64 .r12 = arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * (hSL x + i)))
    (h10 : s.regs.get64 .r14 = arg2 t₀ + 0x5f0c4#64 + BitVec.ofNat 64 (192 * e))
    (h11 : s.regs.get64 .r8 = arg3 t₀) (h13 : s.regs.get64 .rcx = BitVec.ofNat 64 x.m)
    (h14 : s.regs.get64 .r11 = arg0 t₀ + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i))
    (h15 : s.regs.get64 .r15 = BitVec.ofNat 64 i)
    (hm : s.dmem =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)) :
    table k fs x ra t₀ "sbr_hf_assemble.Lafa0" s := by
  have hte := h0.2.2.2.2.2.2.2.2.2.2.1 (e + 1) (by omega)
  have hI := hf3_read_i hm (by omega)
  have hV := hf3_read_v hm
  subst hE
  have h15' : (s.regs.get64 .r15).toNat = i := by rw [h15, BitVec.toNat_ofNat]; omega
  rw [← hI, ← hV] at hm
  rw [Lb16c_post_Lafa0] at hm
  apply Lafa0_tbl_Lb16c
  rw [h15']
  exact ⟨h0, h1, h11, h13, h2, h5, h6, h8, h14, h10, hm⟩


theorem hf_tn_add (a b : BitVec 64) (A B : Nat) (ha : a.toNat = A) (hb : b.toNat = B) (h : A + B < 2 ^ 64) :
    (a + b).toNat = A + B := by
  rw [BitVec.toNat_add, ha, hb, Nat.mod_eq_of_lt h]

theorem hf_tn_mul (a : BitVec 64) (A c : Nat) (ha : a.toNat = A) (h : A * c < 2 ^ 64) (hc : c < 2 ^ 64) :
    (a * BitVec.ofNat 64 c).toNat = A * c := by
  rw [BitVec.toNat_mul, ha, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt h]

theorem hf_tn_ofNat (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

omit [CodeEnv] in
/-- `test $1, %cl` not zero: `m` is odd (the tail element of the sine loop exists). -/
theorem hf_test1_odd (m : Nat) (r : BitVec 64) (af : Bool) (hm : m < 256) (hr : r = BitVec.ofNat 64 m)
    (h : CondCode.z.interp (StatusFlags.from_result (BitVec.setWidth 8 r &&& BitVec.setWidth 8 1#64)
      { cf := false, af := af, of := false }) = false) : m % 2 = 1 := by
  subst hr
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_eq_false_iff_ne, ne_eq] at h
  apply Classical.byContradiction
  intro hne
  apply h
  apply BitVec.eq_of_toNat_eq
  have e1 : m % 2 ^ 64 % 2 ^ 8 = m := by omega
  have e2 : (1 : Nat) % 2 ^ 64 % 2 ^ 8 = 1 := by decide
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat, e1, e2, Nat.and_one_is_mod]
  show m % 2 = 0
  omega

theorem hf_inY (a rbx rdx rdi : BitVec 64) (kx i : Nat)
    (hrbx : rbx = a + BitVec.ofNat 64 kx * 8#64 + BitVec.ofNat 64 (512 * i))
    (hkx : kx + rdi.toNat + 1 ≤ 64) (hi : i < 38) (hdx : rdx.toNat < 2) (hdi : rdi.toNat ≤ 48) :
    ((rbx + rdx * 4#64 + (rdi + rdi) * 4#64) - a).toNat + 4 ≤ 19456 := by
  subst hrbx
  have e : a + BitVec.ofNat 64 kx * 8#64 + BitVec.ofNat 64 (512 * i) + rdx * 4#64 + (rdi + rdi) * 4#64 - a
      = BitVec.ofNat 64 kx * 8#64 + BitVec.ofNat 64 (512 * i) + rdx * 4#64 + (rdi + rdi) * 4#64 := by
    rw [eq_comm, BitVec.eq_sub_iff_add_eq]; ac_rfl
  rw [e]
  have h1 := hf_tn_mul (BitVec.ofNat 64 kx) kx 8 (hf_tn_ofNat kx (by omega)) (by omega) (by omega)
  have h2 := hf_tn_ofNat (512 * i) (by omega)
  have h3 := hf_tn_mul rdx rdx.toNat 4 rfl (by omega) (by omega)
  have h4 := hf_tn_add rdi rdi rdi.toNat rdi.toNat rfl rfl (by omega)
  have h5 := hf_tn_mul (rdi + rdi) _ 4 h4 (by omega) (by omega)
  have h12 := hf_tn_add _ _ _ _ h1 h2 (by omega)
  have h123 := hf_tn_add _ _ _ _ h12 h3 (by omega)
  have h := hf_tn_add _ _ _ _ h123 h5 (by omega)
  rw [h]
  omega

theorem hf_inS (a rdi : BitVec 64) (e : Nat) (he : e < 8) (hdi : rdi.toNat ≤ 48) :
    ((a + 389312#64 + BitVec.ofNat 64 (192 * e) + rdi * 4#64) - (a + 0x5eac0#64)).toNat + 4 ≤ 4608 := by
  have q : a + 389312#64 + BitVec.ofNat 64 (192 * e) + rdi * 4#64 - (a + 0x5eac0#64)
      = 1536#64 + BitVec.ofNat 64 (192 * e) + rdi * 4#64 := by
    rw [show (389312#64 : BitVec 64) = 0x5eac0#64 + 1536#64 by decide]
    rw [eq_comm, BitVec.eq_sub_iff_add_eq]; ac_rfl
  rw [q]
  have h1 := hf_tn_ofNat 1536 (by omega)
  have h2 := hf_tn_ofNat (192 * e) (by omega)
  have h3 := hf_tn_mul rdi rdi.toNat 4 rfl (by omega) (by omega)
  have h12 := hf_tn_add _ _ _ _ h1 h2 (by omega)
  have h := hf_tn_add _ _ _ _ h12 h3 (by omega)
  rw [h]
  omega

theorem hf_dw_ld0 {x : HfArgs} {t : MachineData} {P : Mem 64 → Prop} {m : Mem 64} {addr : BitVec 64} {n : Nat}
    (h : m =⋆ DataW x t ⋆ P) (hin : (addr - arg0 t).toNat + n ≤ 19456) : (m.loadInt addr n).isSome = true := by
  simp only [DataW, Std.ExtHashMap.sep_assoc] at h
  exact Mem.Blocks.loadInt_isSome h (Or.inl hin)

theorem hf_dw_ld2 {x : HfArgs} {t : MachineData} {P : Mem 64 → Prop} {m : Mem 64} {addr : BitVec 64} {n : Nat}
    (h : m =⋆ DataW x t ⋆ P) (hin : (addr - (arg2 t + 0x5eac0#64)).toNat + n ≤ 4608) : (m.loadInt addr n).isSome = true := by
  simp only [DataW, Std.ExtHashMap.sep_assoc] at h
  exact Mem.Blocks.loadInt_isSome h (Or.inr (Or.inr (Or.inl hin)))

theorem hf_dw_st0 {x : HfArgs} {t : MachineData} {P : Mem 64 → Prop} {m : Mem 64} {addr : BitVec 64} {n : Nat}
    (h : m =⋆ DataW x t ⋆ P) (hin : (addr - arg0 t).toNat + n ≤ 19456) (v : Int) : m.storeInt addr n v =⋆ DataW x t ⋆ P := by
  simp only [DataW, Std.ExtHashMap.sep_assoc] at h ⊢
  exact Mem.Blocks.storeInt h (Or.inl hin) v

omit [CodeEnv] in
theorem hf_l_false_ge (m c : Nat) (hm : m < 2 ^ 31) (hc : c < 2 ^ 31) (f : StatusFlags.from_result.Remaining)
    (h : CondCode.l.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 m).toInt))) - BitVec.setWidth 32 (BitVec.ofNat 64 c)) f) = false)
    (hf : f.of = ((BitVec.setWidth 32 (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 m).toInt))) - BitVec.setWidth 32 (BitVec.ofNat 64 c)).signed
      != (BitVec.setWidth 32 (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 m).toInt)))).signed - (BitVec.setWidth 32 (BitVec.ofNat 64 c)).signed)) :
    c ≤ m := by
  rw [CondCode.interp_l_sub32 _ _ _ hf, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt,
    hf_toInt_sw32 m hm, hf_toInt_sw32 c hc] at h
  simp only [decide_eq_false_iff_not, Int.not_lt] at h
  omega


-- START
theorem hf_inR14m (a r14 rdi : BitVec 64) (e : Nat)
    (hr : r14 = a + 0x5f0c4#64 + BitVec.ofNat 64 (192 * e)) (he : e < 8) (hdi : rdi.toNat ≤ 48) :
    ((r14 + rdi * 4#64 + (-4 : Int64).toBitVec) - (a + 0x5eac0#64)).toNat + 4 ≤ 4608 := by
  subst hr
  have q : ∀ X R : BitVec 64, a + 0x5f0c4#64 + X + R + (-4 : Int64).toBitVec - (a + 0x5eac0#64) = 1536#64 + X + R := by
    intro X R
    rw [show (-4 : Int64).toBitVec = 0xFFFFFFFFFFFFFFFC#64 by decide]
    bv_omega
  rw [q]
  have h1 := hf_tn_ofNat 1536 (by omega)
  have h2 := hf_tn_ofNat (192 * e) (by omega)
  have h3 := hf_tn_mul rdi rdi.toNat 4 rfl (by omega) (by omega)
  have h12 := hf_tn_add _ _ _ _ h1 h2 (by omega)
  have h := hf_tn_add _ _ _ _ h12 h3 (by omega)
  rw [h]
  omega

theorem hf_inR14 (a r14 rdi : BitVec 64) (e : Nat)
    (hr : r14 = a + 0x5f0c4#64 + BitVec.ofNat 64 (192 * e)) (he : e < 8) (hdi : rdi.toNat ≤ 48) :
    ((r14 + rdi * 4#64) - (a + 0x5eac0#64)).toNat + 4 ≤ 4608 := by
  subst hr
  have q : ∀ X R : BitVec 64, a + 0x5f0c4#64 + X + R - (a + 0x5eac0#64) = 1540#64 + X + R := by
    intro X R
    bv_omega
  rw [q]
  have h1 := hf_tn_ofNat 1540 (by omega)
  have h2 := hf_tn_ofNat (192 * e) (by omega)
  have h3 := hf_tn_mul rdi rdi.toNat 4 rfl (by omega) (by omega)
  have h12 := hf_tn_add _ _ _ _ h1 h2 (by omega)
  have h := hf_tn_add _ _ _ _ h12 h3 (by omega)
  rw [h]
  omega

theorem hf_inYm (a rsi rdx rdi : BitVec 64) (kx i : Nat)
    (hr : rsi = a + BitVec.ofNat 64 (8 * kx + 8 + 512 * i + 4 * rdx.toNat))
    (hkx : kx + rdi.toNat + 2 ≤ 64) (hi : i < 38) (hdx : rdx.toNat < 2) (hdi : rdi.toNat ≤ 48) :
    ((rsi + rdi * 8#64 + (-8 : Int64).toBitVec) - a).toNat + 4 ≤ 19456 := by
  have hr' : rsi = a + BitVec.ofNat 64 (8 * kx + 512 * i + 4 * rdx.toNat) + 8#64 := by
    rw [hr, BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  subst hr'
  have q : ∀ X R : BitVec 64, a + X + 8#64 + R + (-8 : Int64).toBitVec - a = X + R := by
    intro X R
    rw [show (-8 : Int64).toBitVec = 0xFFFFFFFFFFFFFFF8#64 by decide]
    bv_omega
  rw [q]
  have h1 := hf_tn_ofNat (8 * kx + 512 * i + 4 * rdx.toNat) (by omega)
  have h3 := hf_tn_mul rdi rdi.toNat 8 rfl (by omega) (by omega)
  have h := hf_tn_add _ _ _ _ h1 h3 (by omega)
  rw [h]
  omega

theorem hf_inY2 (a rsi rdx rdi : BitVec 64) (kx i : Nat)
    (hr : rsi = a + BitVec.ofNat 64 (8 * kx + 8 + 512 * i + 4 * rdx.toNat))
    (hkx : kx + rdi.toNat + 2 ≤ 64) (hi : i < 38) (hdx : rdx.toNat < 2) (hdi : rdi.toNat ≤ 48) :
    ((rsi + rdi * 8#64) - a).toNat + 4 ≤ 19456 := by
  subst hr
  have q : ∀ X R : BitVec 64, a + X + R - a = X + R := by
    intro X R
    bv_omega
  rw [q]
  have h1 := hf_tn_ofNat (8 * kx + 8 + 512 * i + 4 * rdx.toNat) (by omega)
  have h3 := hf_tn_mul rdi rdi.toNat 8 rfl (by omega) (by omega)
  have h := hf_tn_add _ _ _ _ h1 h3 (by omega)
  rw [h]
  omega


omit [CodeEnv] in
theorem hf_l_true_lt64 (a b : BitVec 64) (ha : a.toNat < 2 ^ 63) (hb : b.toNat < 2 ^ 63)
    (f : StatusFlags.from_result.Remaining)
    (h : CondCode.l.interp (StatusFlags.from_result (a - b) f) = true)
    (hf : f.of = ((a - b).signed != a.signed - b.signed)) : a.toNat < b.toNat := by
  rw [CondCode.interp_l_sub64 _ _ _ hf] at h
  simp only [decide_eq_true_eq] at h
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond] at h
  split at h <;> split at h <;> omega

theorem hf_T_st2 {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ : MachineData} {e i : Nat} {v : BitVec 128}
    {P : Mem 64 → Prop} {m : Mem 64} {A1 A2 : BitVec 64} {v1 v2 : Int}
    (hT : T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v) = DataW x t₀ ⋆ P) (h : m =⋆ DataW x t₀ ⋆ P)
    (h1 : (A1 - arg0 t₀).toNat + 4 ≤ 19456) (h2 : (A2 - arg0 t₀).toNat + 4 ≤ 19456) :
    (m.storeInt A1 4 v1).storeInt A2 4 v2 =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v) := by
  rw [hT]
  exact hf_dw_st0 (hf_dw_st0 h h1 v1) h2 v2

/-! ## hfasm-3: Lafa0 -/


omit [CodeEnv] in
theorem hf4_and_lo (X : BitVec 128) : (X &&& BitVec.ofInt 128 0x3000001ff).toNat % 2 ^ 32 ≤ 515 := by
  rw [BitVec.toNat_and]
  have hc : (BitVec.ofInt 128 0x3000001ff).toNat = 0x3000001ff := by decide
  rw [hc]
  have : (X.toNat &&& 0x3000001ff) % 2 ^ 32 = (X.toNat % 2 ^ 32) &&& (0x3000001ff % 2 ^ 32) := by
    rw [Nat.and_mod_two_pow]
  rw [this]
  have := Nat.and_le_right (n := X.toNat % 2 ^ 32) (m := 0x3000001ff % 2 ^ 32)
  omega

omit [CodeEnv] in
theorem hf4_and_hi (X : BitVec 128) : (X &&& BitVec.ofInt 128 0x3000001ff).toNat / 2 ^ 32 % 2 ^ 32 < 4 := by
  rw [BitVec.toNat_and]
  have hc : (BitVec.ofInt 128 0x3000001ff).toNat = 0x3000001ff := by decide
  rw [hc, Nat.and_div_two_pow, Nat.and_mod_two_pow]
  have := Nat.and_le_right (n := X.toNat / 2 ^ 32 % 2 ^ 32) (m := 0x3000001ff / 2 ^ 32 % 2 ^ 32)
  omega

theorem hf4_l11 {x : HfArgs} {t : MachineData} {P : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ DataW x t ⋆ P) :
    m.loadInt (lab "LCPI17_11") 16 = some (Int.ofBytes (Int.toBytes 16 0x3000001ff)) := by
  simp only [DataW, Std.ExtHashMap.sep_assoc] at h
  exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)

theorem hf4_te_ld {t : MachineData} {x : HfArgs} {X R : Mem 64 → Prop} {m : Mem 64} (j : Nat) (hj : j ≤ 9)
    (h : m =⋆ X ⋆ (Int.toBytes 4 (x.nenv : Int) =@ (arg3 t + 0x8#64) ⋆ (Int.toBytes 1 (x.te 0 : Int) =@ (arg3 t + 0x15a9c#64) ⋆ (Int.toBytes 1 (x.te 1 : Int) =@ (arg3 t + 0x15a9d#64) ⋆ (Int.toBytes 1 (x.te 2 : Int) =@ (arg3 t + 0x15a9e#64) ⋆ (Int.toBytes 1 (x.te 3 : Int) =@ (arg3 t + 0x15a9f#64) ⋆ (Int.toBytes 1 (x.te 4 : Int) =@ (arg3 t + 0x15aa0#64) ⋆ (Int.toBytes 1 (x.te 5 : Int) =@ (arg3 t + 0x15aa1#64) ⋆ (Int.toBytes 1 (x.te 6 : Int) =@ (arg3 t + 0x15aa2#64) ⋆ (Int.toBytes 1 (x.te 7 : Int) =@ (arg3 t + 0x15aa3#64) ⋆ (Int.toBytes 1 (x.te 8 : Int) =@ (arg3 t + 0x15aa4#64) ⋆ (Int.toBytes 1 (x.te 9 : Int) =@ (arg3 t + 0x15aa5#64) ⋆ R)))))))))))) :
    m.loadInt (arg3 t + 0x15a9c#64 + BitVec.ofNat 64 j) 1 = some (Int.ofBytes (Int.toBytes 1 (x.te j : Int))) := by
  obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 := by omega
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
  · rw [BitVec.add_assoc]
    exact Mem.Val.loadInt h (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)


omit [CodeEnv] in
theorem hf4_xb (X : BitVec 128) :
    (X &&& BitVec.ofInt 128 (Int.ofBytes (Int.toBytes 16 12884902399))).toNat % 4294967296 ≤ 515 ∧
    (X &&& BitVec.ofInt 128 (Int.ofBytes (Int.toBytes 16 12884902399))).toNat / 4294967296 % 4294967296 < 4 := by
  rw [BitVec.ofInt128_ofBytes_toBytes16, BitVec.toNat_and]
  have hc : (BitVec.ofInt 128 12884902399).toNat = 0x3000001ff := by decide
  rw [hc]
  constructor
  · have : (X.toNat &&& 0x3000001ff) % 2 ^ 32 = (X.toNat % 2 ^ 32) &&& (0x3000001ff % 2 ^ 32) := by
      rw [Nat.and_mod_two_pow]
    have h2 := Nat.and_le_right (n := X.toNat % 2 ^ 32) (m := 0x3000001ff % 2 ^ 32)
    have : (4294967296 : Nat) = 2 ^ 32 := rfl
    omega
  · have : (4294967296 : Nat) = 2 ^ 32 := rfl
    rw [this, Nat.and_div_two_pow, Nat.and_mod_two_pow]
    have := Nat.and_le_right (n := X.toNat / 2 ^ 32 % 2 ^ 32) (m := 0x3000001ff / 2 ^ 32 % 2 ^ 32)
    omega

omit [CodeEnv] in
theorem hf4_te2 (n : Nat) (h : n < 128) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 (n : Int))))
      + BitVec.setWidth 32 (BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 (n : Int)))))).toNat = 2 * n := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
theorem hf4_tn_succ (a : BitVec 64) (h : a.toNat < 2 ^ 63) : (a + 1).toNat = a.toNat + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, h1]
  omega


omit [CodeEnv] in
theorem hf4_step (r C : BitVec 64) (N M c : Nat) (hr : r = C + BitVec.ofNat 64 N)
    (hb : N + c < 2 ^ 64) (hM : M = N + c) :
    BitVec.setWidth 64 (BitVec.ofNat 64 c) + r = C + BitVec.ofNat 64 M := by
  subst hr hM
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

-- hfasm-3 Laf40: general variable-index cell-array load



omit [CodeEnv] in
/-- Ten byte cells at `a + 88732 …` as an array. -/
theorem hf4_te_arr (a : BitVec 64) (g : Nat → Nat) (R : Mem 64 → Prop) :
    (Int.toBytes 1 (g 0 : Int) =@ (a + 0x15a9c#64) ⋆ (Int.toBytes 1 (g 1 : Int) =@ (a + 0x15a9d#64) ⋆ (Int.toBytes 1 (g 2 : Int) =@ (a + 0x15a9e#64) ⋆ (Int.toBytes 1 (g 3 : Int) =@ (a + 0x15a9f#64) ⋆ (Int.toBytes 1 (g 4 : Int) =@ (a + 0x15aa0#64) ⋆ (Int.toBytes 1 (g 5 : Int) =@ (a + 0x15aa1#64) ⋆ (Int.toBytes 1 (g 6 : Int) =@ (a + 0x15aa2#64) ⋆ (Int.toBytes 1 (g 7 : Int) =@ (a + 0x15aa3#64) ⋆ (Int.toBytes 1 (g 8 : Int) =@ (a + 0x15aa4#64) ⋆ (Int.toBytes 1 (g 9 : Int) =@ (a + 0x15aa5#64) ⋆ R))))))))))
    = Mem.CellArr 1 (a + 0x15a9c#64) (fun k => (g k : Int)) 10 R := by
  simp only [Mem.CellArr, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, Nat.zero_add]

omit [CodeEnv] in
/-- Laf40: the two variable-index te loads `te[r]`, `te[r+1]` in vcgen address form. -/
theorem hf4_te_ld2 {m : Mem 64} {X R : Mem 64 → Prop} {a r8 r : BitVec 64} {g : Nat → Nat}
    (h : m =⋆ X ⋆ Mem.CellArr 1 (a + 0x15a9c#64) (fun k => (g k : Int)) 10 R) (h8 : r8 = a) (hr : r.toNat < 9) :
    m.loadInt (r8 + r * 1#64 + 88732#64) 1 = some (Int.ofBytes (Int.toBytes 1 (g r.toNat : Int))) ∧
    m.loadInt (r8 + r * 1#64 + 88733#64) 1 = some (Int.ofBytes (Int.toBytes 1 (g (r.toNat + 1) : Int))) := by
  subst r8
  have h0 := Mem.CellArr.loadInt h (by decide) r.toNat (by omega)
  have h1 := Mem.CellArr.loadInt h (by decide) (r.toNat + 1) (by omega)
  refine ⟨?_, ?_⟩
  · rw [show a + r * 1#64 + 88732#64 = a + 0x15a9c#64 + BitVec.ofNat 64 (1 * r.toNat) by
      rw [Nat.one_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.mul_one]; ac_rfl]
    exact h0
  · rw [show a + r * 1#64 + 88733#64 = a + 0x15a9c#64 + BitVec.ofNat 64 (1 * (r.toNat + 1)) by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega]
    exact h1


-- hfasm-3 Laf40: stack store/load and store-into-view





omit [CodeEnv] in
theorem hf4_b8 (n : Nat) :
    BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 (n : Int))) = BitVec.ofNat 8 n := by
  rw [BitVec.ofInt_ofBytes_toBytes_eq 8 1 rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega


-- hfasm-3 Laf40: te-derived register values

omit [CodeEnv] in
theorem hf4_r12 (C : BitVec 64) (t h : Nat) (ht : t ≤ 19) :
    C + BitVec.ofNat 64 (192 * h) +
    BitVec.setWidth 64
      (BitVec.setWidth 32
          (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) +
            BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) * 2#64) <<< 7) =
    C + BitVec.ofNat 64 (192 * (h + (BitVec.setWidth 64 (BitVec.setWidth 32
                (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) +
                  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) * 1#64))).toNat)) := by
  have e1 : BitVec.setWidth 64
      (BitVec.setWidth 32
          (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) +
            BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) * 2#64) <<< 7) = BitVec.ofNat 64 (384 * t) := by
    have s0 : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) = BitVec.ofNat 64 t := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega
    have s1 : BitVec.ofNat 64 t + BitVec.ofNat 64 t * 2#64 = BitVec.ofNat 64 (3 * t) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
    have s2 : BitVec.setWidth 32 (BitVec.ofNat 64 (3 * t)) = BitVec.ofNat 32 (3 * t) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow]; omega
    have s3 : BitVec.ofNat 32 (3 * t) <<< 7 = BitVec.ofNat 32 (384 * t) := by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega
    have s4 : BitVec.setWidth 64 (BitVec.ofNat 32 (384 * t)) = BitVec.ofNat 64 (384 * t) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
        Nat.mod_eq_of_lt (show 384 * t < 4294967296 by omega), Nat.mod_eq_of_lt (show 384 * t < 18446744073709551616 by omega)]
    rw [s0, s1, s2, s3, s4]
  have e2 : (BitVec.setWidth 64 (BitVec.setWidth 32
                (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) +
                  BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 t)) * 1#64))).toNat = 2 * t := by
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [e1, e2, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

omit [CodeEnv] in
theorem hf4_r192 (r : BitVec 64) (hr : r.toNat < 2 ^ 32) :
    (r + r * 2#64) <<< 6 = BitVec.ofNat 64 (192 * r.toNat) := by
  have s1 : r + r * 2#64 = BitVec.ofNat 64 (3 * r.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.mod_eq_of_lt (show r.toNat * 2 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show r.toNat + r.toNat * 2 < 18446744073709551616 by omega),
      Nat.mod_eq_of_lt (show 3 * r.toNat < 18446744073709551616 by omega)]
    omega
  rw [s1]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow,
    Nat.mod_eq_of_lt (show 3 * r.toNat < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show 3 * r.toNat * 64 < 18446744073709551616 by omega),
    Nat.mod_eq_of_lt (show 192 * r.toNat < 18446744073709551616 by omega)]
  omega

omit [CodeEnv] in
theorem hf4_inc (r : BitVec 64) (hr : r.toNat < 2 ^ 32) :
    r + 1#64 = BitVec.ofNat 64 (r.toNat + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.mod_eq_of_lt (show r.toNat + 1 < 18446744073709551616 by omega)]

omit [CodeEnv] in
theorem hf4_tn_inc (a : BitVec 64) (h : a.toNat < 2 ^ 63) : (a + 1#64).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## G1: the `f_indexnoise`/`f_indexsine` cell comes back bounded (`HfIdxOut`) -/

/-- `xmm4 = idx` (zero-extended) is within the `HfC` bounds. -/
theorem hf_xb {x : HfArgs} {t : MachineData} {v : BitVec 128} (hC : HfC x t)
    (h : v = x.idx.setWidth 128) :
    v.toNat % 2 ^ 32 ≤ 515 ∧ v.toNat / 2 ^ 32 % 2 ^ 32 < 4 := by
  subst h
  have h1 := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2 := hC.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hl := x.idx.isLt
  have e : x.idx.toNat % 2 ^ 128 = x.idx.toNat := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_setWidth, e]
  omega

/-- The stored pair, in range, read as `HfIdxOut` (the `IC` slot of `T`). -/
theorem T_idxout (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (v : BitVec 64) (hb1 : v.toNat % 2 ^ 32 ≤ 515)
    (hb2 : v.toNat / 2 ^ 32 < 4) :
    Mem.Entails (T k fs x ra t₀ (Int.toBytes 8 v.toInt =@ (arg3 t₀ + 0x15aac#64)) FR)
      (T k fs x ra t₀ (HfIdxOut t₀) FR) := by
  have e : Mem.Entails ((Int.toBytes 8 v.toInt =@ (arg3 t₀ + 0x15aac#64)) ⋆ FR (Rest x.R ra t₀))
      (HfIdxOut t₀ ⋆ FR (Rest x.R ra t₀)) := by
    intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
    exact ⟨m₁, m₂, hd, hm, ⟨v, hb1, hb2, h₁⟩, h₂⟩
  simp only [T]
  exact Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left e))))))

omit [CodeEnv] in
/-- The low 64 bits of an in-range `xmm4`, as the stored pair. -/
theorem hf_xb64 {v : BitVec 128} (h : v.toNat % 2 ^ 32 ≤ 515 ∧ v.toNat / 2 ^ 32 % 2 ^ 32 < 4) :
    (v.setWidth 64).toNat % 2 ^ 32 ≤ 515 ∧ (v.setWidth 64).toNat / 2 ^ 32 < 4 := by
  rw [BitVec.toNat_setWidth]
  omega

omit [CodeEnv] in
/-- The stored pair, in range, as `HfIdxOut` behind the seven groups in front of the index cell
(`T` unfolded: return slot, reservation, `DataW`, `ScW`, `FnW`, `TeW`, `EaW`). -/
theorem hf_idx_intro {t : MachineData} {A1 A2 A3 A4 A5 A6 A7 R : Mem 64 → Prop} {m : Mem 64}
    (v : BitVec 64) (hb1 : v.toNat % 2 ^ 32 ≤ 515) (hb2 : v.toNat / 2 ^ 32 < 4)
    (h : (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7
      ⋆ ((Int.toBytes 8 v.toInt =@ (arg3 t + 0x15aac#64)) ⋆ R)))))))) m) :
    (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ (A6 ⋆ (A7 ⋆ (HfIdxOut t ⋆ R)))))))) m := by
  have e : Mem.Entails ((Int.toBytes 8 v.toInt =@ (arg3 t + 0x15aac#64)) ⋆ R) (HfIdxOut t ⋆ R) := by
    intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
    exact ⟨m₁, m₂, hd, hm, ⟨v, hb1, hb2, h₁⟩, h₂⟩
  exact (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left e))))))) m h

omit [CodeEnv] in
/-- A `t_env` byte (`movzbl`, then zero-extended) as a 64-bit value (`La8f6`). -/
theorem hf_te_sw (n : Nat) (h : n < 256) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 (n : Int))) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega
