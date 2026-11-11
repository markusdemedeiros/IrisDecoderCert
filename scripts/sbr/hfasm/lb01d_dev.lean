/-! ### Reading `i` and `v` back from the frame (FL2), and the `hf_g_filt` call -/

theorem FL2_read_i {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ : MachineData} {e i : Nat}
    {v : BitVec 128} {m : Mem 64} (h : m =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v))
    (hi : i < 2 ^ 64) :
    (BitVec.ofInt 64 ((m.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i := by
  rw [FL2_s38] at h
  rw [Mem.Val.loadInt h (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)]
  simp only [Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem FL2_read_v {k : Nat} {fs : HfFns} {x : HfArgs} {ra : Int64} {t₀ : MachineData} {e i : Nat}
    {v : BitVec 128} {m : Mem 64} (h : m =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)) :
    BitVec.ofInt 128 ((m.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v := by
  rw [FL2_xv] at h
  rw [Mem.Val.loadInt h (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)]
  simp only [Option.getD_some]
  exact BitVec.ofInt_ofBytes_toBytes 128 16 rfl v

/-- The memory across the `hf_g_filt` call: `g_filt_tab` joins the data. -/
theorem T_FL2_call (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData) (e i : Nat)
    (v : BitVec 128) :
    T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)
      = 8 ?@ (t₀.regs.get64 .rsp - 0x290#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x290#64)
        ⋆ ((DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x288#64)) ⋆ (ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀
        ⋆ (EaW x t₀ ⋆ (IdxC x t₀ ⋆ FL2g x t₀ e i v (Rest x.R ra t₀)))))))) := by
  simp only [T, FL2, FL2g, Std.ExtHashMap.sep_assoc]
  ac_rfl

omit [CodeEnv] in
theorem hf_off (p : BitVec 64) (c : Nat) (hc : c < 2 ^ 64) : (p + BitVec.ofNat 64 c - p).toNat = c := by
  have : p + BitVec.ofNat 64 c - p = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]

/-- `hf_g_filt`'s footprint inside the data and `g_filt_tab`: the `Y1` row, the
`X_high` rows, and `g_filt` (a `g_temp` row or the local table). -/
theorem Lb01d_carve (x : HfArgs) (t₀ : MachineData) (kx m i : Nat) (D : BitVec 64)
    (hkm : kx + m ≤ 64) (hi : i ≤ 37)
    (hD : (∃ c, c ≤ 41 ∧ D = arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (192 * c))
      ∨ (D = t₀.regs.get64 .rsp - 0x288#64 ∧ m ≤ 48)) :
    ∃ H, DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x288#64)
      = Blocks [(arg0 t₀ + BitVec.ofNat 64 (8 * kx + 512 * i), 8 * m),
          (arg1 t₀ + BitVec.ofNat 64 (320 * kx), 320 * m), (D, 4 * m)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Mem.Block.carve_ex (a := arg0 t₀) (b := arg0 t₀ + BitVec.ofNat 64 (8 * kx + 512 * i))
    (len := 19456) (n := 8 * m) (by rw [hf_off _ _ (by omega)]; omega) (by omega)
  obtain ⟨H2, e2⟩ := Mem.Block.carve_ex (a := arg1 t₀) (b := arg1 t₀ + BitVec.ofNat 64 (320 * kx))
    (len := 20480) (n := 320 * m) (by rw [hf_off _ _ (by omega)]; omega) (by omega)
  simp only [DataW, Blocks]
  rw [show (Block (arg0 t₀) 19456 : Mem 64 → Prop) = 19456 ?@ arg0 t₀ from rfl, e1,
    show (Block (arg1 t₀) 20480 : Mem 64 → Prop) = 20480 ?@ arg1 t₀ from rfl, e2]
  rcases hD with ⟨c, hc, rfl⟩ | ⟨rfl, hm⟩
  · obtain ⟨H3, e3⟩ := Mem.Block.carve_ex (a := arg3 t₀ + 0x11130#64)
      (b := arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (192 * c))
      (len := 16128) (n := 4 * m) (by rw [hf_off _ _ (by omega)]; omega) (by omega)
    rw [show (Block (arg3 t₀ + 0x11130#64) 16128 : Mem 64 → Prop) = 16128 ?@ (arg3 t₀ + 0x11130#64) from rfl, e3]
    refine ⟨H1 ⋆ (H2 ⋆ (H3 ⋆ (4608 ?@ (arg2 t₀ + 0x5eac0#64) ⋆ (Blocks [(lab "ff_sbr_noise_table", 4160),
      (lab "ps_noise0", 16), (lab "ps_noise13", 48), (lab "ps_noise2", 16), (arg0 t₀ + 19456#64, 24 - 24 * x.ypos)]
      ⋆ (4 ?@ lab "LCPI17_6" ⋆ (4 ?@ lab "LCPI17_7" ⋆ (4 ?@ lab "LCPI17_8" ⋆ (4 ?@ lab "LCPI17_9"
      ⋆ (4 ?@ lab "LCPI17_10" ⋆ (4 ?@ lab "LCPI17_12" ⋆ (Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11"
      ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x288#64)))))))))))), ?_⟩
    simp only [Blocks, Std.ExtHashMap.sep_assoc]
    ac_rfl
  · obtain ⟨H3, e3⟩ := Mem.Block.carve_ex (a := t₀.regs.get64 .rsp - 0x288#64)
      (b := t₀.regs.get64 .rsp - 0x288#64)
      (len := 192) (n := 4 * m) (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega) (by omega)
    rw [e3]
    refine ⟨H1 ⋆ (H2 ⋆ (H3 ⋆ (4608 ?@ (arg2 t₀ + 0x5eac0#64) ⋆ (16128 ?@ (arg3 t₀ + 0x11130#64)
      ⋆ (Blocks [(lab "ff_sbr_noise_table", 4160),
      (lab "ps_noise0", 16), (lab "ps_noise13", 48), (lab "ps_noise2", 16), (arg0 t₀ + 19456#64, 24 - 24 * x.ypos)]
      ⋆ (4 ?@ lab "LCPI17_6" ⋆ (4 ?@ lab "LCPI17_7" ⋆ (4 ?@ lab "LCPI17_8" ⋆ (4 ?@ lab "LCPI17_9"
      ⋆ (4 ?@ lab "LCPI17_10" ⋆ (4 ?@ lab "LCPI17_12"
      ⋆ Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11"))))))))))), ?_⟩
    simp only [Blocks, Std.ExtHashMap.sep_assoc]
    ac_rfl

omit [CodeEnv] in
theorem hf_y_row (A r : BitVec 64) (kx : Nat) (hkx : kx ≤ 64) (hr : r.toNat < 64) :
    A + BitVec.ofNat 64 kx * 8#64 + r <<< 9 = A + BitVec.ofNat 64 (8 * kx + 512 * r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
theorem hf_x_row (X : BitVec 64) (kx : Nat) (hkx : kx ≤ 64) :
    (BitVec.ofNat 64 kx + BitVec.ofNat 64 kx * 4#64) <<< 6 + X = X + BitVec.ofNat 64 (320 * kx) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  omega

/-- `Lb01d_carve` in the form the call site computes the addresses. -/
theorem Lb01d_carve' (x : HfArgs) (t₀ : MachineData) (kx m : Nat) (r D a0 a1 : BitVec 64) (M : Nat)
    (hkm : kx + m ≤ 64) (hi : r.toNat ≤ 37)
    (hD : (∃ c, c ≤ 41 ∧ D = arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (192 * c))
      ∨ (D = t₀.regs.get64 .rsp - 0x288#64 ∧ m ≤ 48))
    (e0 : a0 = arg0 t₀ + BitVec.ofNat 64 kx * 8#64 + r <<< 9)
    (e1 : a1 = (BitVec.ofNat 64 kx + BitVec.ofNat 64 kx * 4#64) <<< 6 + arg1 t₀) (eM : M = m) :
    ∃ H, DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x288#64)
      = Blocks [(a0, 8 * M), (a1, 320 * M), (D, 4 * M)] ⋆ H := by
  subst e0 e1 eM
  rw [hf_y_row _ _ _ (by omega) (by omega), hf_x_row _ _ (by omega)]
  exact Lb01d_carve x t₀ kx M r.toNat D hkm hi hD

omit [CodeEnv] in
theorem hf_y_row' (A : BitVec 64) (kx i : Nat) (hkx : kx ≤ 64) (hi : i ≤ 64) :
    A + BitVec.ofNat 64 kx * 8#64 + BitVec.ofNat 64 (512 * i) = A + BitVec.ofNat 64 (8 * kx + 512 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- An offset between two `base + c + o` addresses. -/
theorem hf_off2 (a : BitVec 64) (b d c o : Nat) (h : b + d ≤ c + o) (hc : c < 2 ^ 32) (ho : o < 2 ^ 32)
    (hb : b < 2 ^ 32) (hd : d < 2 ^ 32) :
    (a + BitVec.ofNat 64 c + BitVec.ofNat 64 o - (a + BitVec.ofNat 64 b + BitVec.ofNat 64 d)).toNat
      = c + o - b - d := by
  have : a + BitVec.ofNat 64 c + BitVec.ofNat 64 o - (a + BitVec.ofNat 64 b + BitVec.ofNat 64 d)
      = BitVec.ofNat 64 (c + o - b - d) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
/-- `Y1` and the 24 bytes after it as one block. -/
theorem hf_merge24 (a : BitVec 64) (K : Mem 64 → Prop) :
    Block a 19456 ⋆ (Block (a + 19456#64) 24 ⋆ K) = Block a 19480 ⋆ K := by
  rw [show (Block a 19480 : Mem 64 → Prop) = (19456 + 24) ?@ a from rfl, Block.split a 19456 24 (by decide)]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The entry's noise constant inside the three `ps_noise*` blocks. -/
theorem hf_noise_carve (c1 : BitVec 64) (c2 : Nat)
    (hc : (c1, c2) = HfApplyNoiseK0 ∨ (c1, c2) = HfApplyNoiseK1 ∨ (c1, c2) = HfApplyNoiseK2
      ∨ (c1, c2) = HfApplyNoiseK3) :
    ∃ H, ∀ K : Mem 64 → Prop, Block (lab "ps_noise0") 16 ⋆ (Block (lab "ps_noise13") 48
      ⋆ (Block (lab "ps_noise2") 16 ⋆ K)) = Block c1 c2 ⋆ (H ⋆ K) := by
  rcases hc with h | h | h | h <;>
    simp only [HfApplyNoiseK0, HfApplyNoiseK1, HfApplyNoiseK2, HfApplyNoiseK3, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨Block (lab "ps_noise13") 48 ⋆ Block (lab "ps_noise2") 16, fun K => by
      simp only [Std.ExtHashMap.sep_assoc]⟩
  · obtain ⟨H4, e4⟩ := Mem.Block.carve_ex (a := lab "ps_noise13") (b := lab "ps_noise13")
      (len := 48) (n := 32) (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega) (by omega)
    exact ⟨Block (lab "ps_noise0") 16 ⋆ (H4 ⋆ Block (lab "ps_noise2") 16), fun K => by
      rw [show (Block (lab "ps_noise13") 48 : Mem 64 → Prop) = 48 ?@ lab "ps_noise13" from rfl, e4]
      simp only [Std.ExtHashMap.sep_assoc]; ac_rfl⟩
  · exact ⟨Block (lab "ps_noise0") 16 ⋆ Block (lab "ps_noise13") 48, fun K => by
      simp only [Std.ExtHashMap.sep_assoc]; ac_rfl⟩
  · obtain ⟨H4, e4⟩ := Mem.Block.carve_ex (a := lab "ps_noise13") (b := lab "ps_noise13" + 16#64)
      (len := 48) (n := 32) (by rw [show lab "ps_noise13" + 16#64 - lab "ps_noise13" = 16#64 by bv_omega]; decide) (by omega)
    exact ⟨Block (lab "ps_noise0") 16 ⋆ (H4 ⋆ Block (lab "ps_noise2") 16), fun K => by
      rw [show (Block (lab "ps_noise13") 48 : Mem 64 → Prop) = 48 ?@ lab "ps_noise13" from rfl, e4]
      simp only [Std.ExtHashMap.sep_assoc]; ac_rfl⟩

/-- `hf_apply_noise`'s footprint inside the data and `q_filt_tab`: the window of `Y1` row `i`
(`32⌈m/4⌉` bytes from column `kx`; by `a2_row_spill`, for `i ≤ 37` inside `Y1` and the
24 bytes after it), the `s_m` row, the `q_filt` row (a `q_temp`
row or the local table), the noise table and the entry's constant. -/
theorem Lb1a0_carve (x : HfArgs) (t₀ : MachineData) (kx m i e It : Nat) (a0 a1 a2 r9 : BitVec 64)
    (c : BitVec 64 × Nat) (hy : x.ypos ≤ 1)
    (hY : arg0 t₀ = arg3 t₀ + 0x7930#64 + BitVec.ofNat 64 (19456 * x.ypos))
    (hkm : kx + m ≤ 64) (hm : m ≤ 48) (hi : i ≤ 37) (he : e < 8) (hr9 : r9 = BitVec.ofNat 64 m)
    (hIt : It = (r9.toNat % 2 ^ 32 + 3) / 4)
    (e0 : a0 = arg0 t₀ + BitVec.ofNat 64 kx * 8#64 + BitVec.ofNat 64 (512 * i))
    (e1 : a1 = arg2 t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (192 * e))
    (hQ : a2 = arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * i) ∨ a2 = t₀.regs.get64 .rsp - 0x1c8#64)
    (hc : c = HfApplyNoiseK0 ∨ c = HfApplyNoiseK1 ∨ c = HfApplyNoiseK2 ∨ c = HfApplyNoiseK3) :
    ∃ H, DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x1c8#64)
      = Blocks [(a0, 32 * It), (a1, 16 * It), (a2, 16 * It), (lab "ff_sbr_noise_table", 4160), c] ⋆ H := by
  obtain ⟨c1, c2⟩ := c
  subst e0 e1 hIt hr9
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega)]
  rw [hf_y_row' _ _ _ (by omega) (by omega)]
  -- `a2_row_spill`: the window ends at most 24 bytes after row `i`
  have hsp := (a2_row_spill kx m hkm).1
  rw [← DataW_eq x t₀ hy hY]
  simp only [HfData, Blocks]
  rw [← hY, hf_merge24]
  obtain ⟨H1, e1⟩ := Mem.Block.carve_ex (a := arg0 t₀) (b := arg0 t₀ + BitVec.ofNat 64 (8 * kx + 512 * i))
    (len := 19480) (n := 32 * ((m + 3) / 4)) (by rw [hf_off _ _ (by omega)]; omega) (by omega)
  obtain ⟨H2, e2⟩ := Mem.Block.carve_ex (a := arg2 t₀ + 0x5f0c0#64)
    (b := arg2 t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (192 * e))
    (len := 1536) (n := 16 * ((m + 3) / 4)) (by rw [hf_off _ _ (by omega)]; omega) (by omega)
  obtain ⟨H4, e4⟩ := hf_noise_carve c1 c2 hc
  simp only [Std.ExtHashMap.sep_assoc]
  rw [e1, e2, e4]
  rcases hQ with rfl | rfl
  · obtain ⟨H3, e3⟩ := Mem.Block.carve_ex (a := arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (24 * x.ypos))
      (b := arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (192 * i))
      (len := 16128 - 24 * x.ypos) (n := 16 * ((m + 3) / 4))
      (by rw [hf_off2 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)]; omega) (by omega)
    rw [e3]
    refine ⟨H1 ⋆ (H3 ⋆ (Block (arg1 t₀) 20480 ⋆ (Block (arg2 t₀ + 0x5eac0#64) 1536 ⋆ (H2
      ⋆ (Block (arg2 t₀ + 0x5f6c0#64) 1536 ⋆ (H4
      ⋆ (4 ?@ lab "LCPI17_6" ⋆ (4 ?@ lab "LCPI17_7" ⋆ (4 ?@ lab "LCPI17_8" ⋆ (4 ?@ lab "LCPI17_9"
      ⋆ (4 ?@ lab "LCPI17_10" ⋆ (4 ?@ lab "LCPI17_12" ⋆ (Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11"
      ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x1c8#64)))))))))))))), ?_⟩
    simp only [Std.ExtHashMap.sep_assoc]
    ac_rfl
  · obtain ⟨H3, e3⟩ := Mem.Block.carve_ex (a := t₀.regs.get64 .rsp - 0x1c8#64) (b := t₀.regs.get64 .rsp - 0x1c8#64)
      (len := 192) (n := 16 * ((m + 3) / 4)) (by rw [BitVec.sub_self, BitVec.toNat_zero]; omega) (by omega)
    rw [e3]
    refine ⟨H1 ⋆ (Block (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (24 * x.ypos)) (16128 - 24 * x.ypos)
      ⋆ (Block (arg1 t₀) 20480 ⋆ (Block (arg2 t₀ + 0x5eac0#64) 1536 ⋆ (H2
      ⋆ (Block (arg2 t₀ + 0x5f6c0#64) 1536 ⋆ (H4
      ⋆ (4 ?@ lab "LCPI17_6" ⋆ (4 ?@ lab "LCPI17_7" ⋆ (4 ?@ lab "LCPI17_8" ⋆ (4 ?@ lab "LCPI17_9"
      ⋆ (4 ?@ lab "LCPI17_10" ⋆ (4 ?@ lab "LCPI17_12" ⋆ (Int.toBytes 16 0x3000001ff =@ lab "LCPI17_11"
      ⋆ H3))))))))))))), ?_⟩
    simp only [Std.ExtHashMap.sep_assoc]
    ac_rfl


/-- The memory across the `hf_apply_noise` call: `q_filt_tab` joins the data. -/
theorem T_FL2_callq (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData) (e i : Nat)
    (v : BitVec 128) :
    T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)
      = 8 ?@ (t₀.regs.get64 .rsp - 0x290#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x290#64)
        ⋆ ((DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x1c8#64)) ⋆ (ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀
        ⋆ (EaW x t₀ ⋆ (IdxC x t₀ ⋆ FL2q x t₀ e i v (Rest x.R ra t₀)))))))) := by
  simp only [T, FL2, FL2q, Std.ExtHashMap.sep_assoc]
  ac_rfl

omit [CodeEnv] in
theorem hf_align_row (a : BitVec 64) (o c : Nat) (ha : isAligned 16 a = true) (ho : o % 16 = 0)
    (ho' : o < 2 ^ 32) (hc : c < 2 ^ 32) :
    isAligned 16 (a + BitVec.ofNat 64 o + BitVec.ofNat 64 (192 * c)) = true := by
  refine isAligned_add (by decide) (isAligned_add (by decide) ha ?_) ?_
  · rw [BitVec.toNat_ofNat]; omega
  · rw [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem hf_align_qtab (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) :
    isAligned 16 (r - 0x1c8#64) = true :=
  isAligned_of_sub (by decide) h (by
    rw [show r - 0x1c8#64 - (r + 8#64) = 0xfffffffffffffe30#64 by bv_omega]; rfl)

omit [CodeEnv] in
theorem hf_align_16 (a : BitVec 64) (h : isAligned 16 a = true) : isAligned 16 (a + 16#64) = true :=
  isAligned_add (by decide) h rfl

omit [CodeEnv] in
theorem hf_shl9 (r : BitVec 64) (hr : r.toNat < 2 ^ 32) : r <<< 9 = BitVec.ofNat 64 (512 * r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
theorem hf_fn_load (f : Int64) :
    Int64.ofBitVec (BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 f.toBitVec.toInt))) = f := by
  simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]

omit [CodeEnv] in
theorem hf_take4 (v : Int) : (Int.toBytes 8 v).take 4 = Int.toBytes 4 v := rfl

omit [CodeEnv] in
/-- The low dword of a known qword cell. -/
theorem hfc_load_lo4 {H R : Mem 64 → Prop} {m : Mem 64} {a : BitVec 64} {v : BitVec 64}
    (h : m =⋆ H) (hs : Mem.Split (Int.toBytes 8 v.toInt =@ a) R H) :
    m.loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 v.toInt)) := by
  rw [hs] at h
  have := Mem.loadInt_slice (addr := a) (n := 4) h (by simp [Int.toBytes_length]) (by simp [Int.toBytes_length])
  rw [BitVec.sub_self, BitVec.toNat_zero, List.drop_zero, hf_take4] at this
  exact this

omit [CodeEnv] in
theorem hf_kx32 (kx : Nat) (h : kx < 2 ^ 32) :
    BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (BitVec.ofNat 64 kx).toInt)) = BitVec.ofNat 32 kx := by
  rw [BitVec.ofInt32_ofBytes_toBytes4]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega

omit [CodeEnv] in
theorem hf_add2_lt (r : BitVec 64) (h : r.toNat < 38) : (r + 2#64).toNat < 40 := by bv_omega

omit [CodeEnv] in
theorem hf_align_xv (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) :
    isAligned 16 (r - 120#64) = true :=
  isAligned_of_sub (by decide) h (by
    rw [show r - 120#64 - (r + 8#64) = 0xffffffffffffff80#64 by bv_omega]; rfl)

omit [CodeEnv] in
/-- The carry flag of a 32-bit `cmp` as the unsigned order (as in `XGen`). -/
theorem hf_sub_cf32 (a b : BitVec 32) :
    ((((a - b).toNat : Int)) != ((a.toNat : Int) - (b.toNat : Int))) = decide (a.toNat < b.toNat) := by
  have ha := a.isLt; have hb := b.isLt
  rw [BitVec.toNat_sub]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    omega

omit [CodeEnv] in
theorem hf_align_eq {a b : BitVec 64} (e : a = b) (h : isAligned 16 b = true) : isAligned 16 a = true := e ▸ h

omit [CodeEnv] in
theorem hf_rsp_656_8 (r : BitVec 64) : r - 656#64 + 8#64 = r - 648#64 := by bv_omega
omit [CodeEnv] in
theorem hf_rsp_656_8_584 (r : BitVec 64) : r - 656#64 + 8#64 + 584#64 = r - 64#64 := by bv_omega
omit [CodeEnv] in
theorem hf_rsp_648_584 (r : BitVec 64) : r - 648#64 + 584#64 = r - 64#64 := by bv_omega
omit [CodeEnv] in
theorem hf_rsp_648_8 (r : BitVec 64) : r - 648#64 - 8#64 = r - 656#64 := by bv_omega
omit [CodeEnv] in
theorem hf_rsp_656_648 (r : BitVec 64) : r - 656#64 = r - 648#64 - 8#64 := by bv_omega
