import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`: lemmas for the border blocks (`0x1fa`–`0x714`)

The flag tests of the border code, the `num_env_tab` load, and `toHdr`: the facts at the border
code's exits give `AtHdr` (`0x715`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

omit [CodeEnv] in
/-- `test %r8b,%r8b; jle` on a small positive register: not taken. -/
theorem hn_le_test8 (d : BitVec 64) (h1 : 1 ≤ d.toNat) (h2 : d.toNat < 128) (a : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 8 d &&& BitVec.setWidth 8 d)
      { cf := false, af := a, of := false }) = false := by
  have e1 : (BitVec.setWidth 8 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]; omega
  have e2 : ((BitVec.setWidth 8 d) == BitVec.zero 8) = false := by
    have : ¬ (BitVec.setWidth 8 d = BitVec.zero 8) := by
      have z : (BitVec.zero 8).toNat = 0 := rfl
      rw [← BitVec.toNat_inj, z, BitVec.toNat_setWidth]; omega
    simpa using this
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self, e1, e2]
  rfl

omit [CodeEnv] in
/-- `num_env_tab[frame_class][bits]`'s address (`rsi = frame_class ≤ 1`, `r9 = bits < 4`). -/
theorem hn_nenv_addr (L r9 rsi : BitVec 64) (h1 : rsi.toNat ≤ 1) (h2 : r9.toNat < 4) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r9) + (L + BitVec.setWidth 64 (BitVec.setWidth 32 rsi) * 4#64)
      = L + BitVec.ofNat 64 (4 * rsi.toNat + r9.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- The entries of `num_env_tab`, sign-extended as loaded. -/
theorem hn_nenv_val (j : Nat) (hj : j < 8) :
    (BitVec.setWidth 64 (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1)))).toNat ≤ 4
    ∧ BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 8
        (BitVec.setWidth 64 (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1))))))
      = BitVec.setWidth 64 (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1)))
    ∧ (j < 4 → (BitVec.setWidth 64 (BitVec.signExtend 32
        (BitVec.ofInt 8 (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1)))).toNat ≠ 3)
    ∧ (4 ≤ j → 1 ≤ (BitVec.setWidth 64 (BitVec.signExtend 32
        (BitVec.ofInt 8 (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1)))).toNat) := by
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide

/-! ## `*ps` past the header fields, and the header fields without a header -/

omit [CodeEnv] in
theorem hn_getD_Kp {x : PArgs} {c : List UInt8} (hK : Kp x c) (j : Nat) (hj : 0x4c ≤ j) :
    c.getD j 0 = x.c.getD j 0 := by
  have h := congrArg (fun l : List UInt8 => l[j - 0x4c]?) hK.2
  simp only [List.getElem?_drop] at h
  rw [show 0x4c + (j - 0x4c) = j by omega] at h
  simp only [List.getD_eq_getElem?_getD, h]

omit [CodeEnv] in
theorem hn_i8_Kp {x : PArgs} {c : List UInt8} (hK : Kp x c) (j : Nat) (hj : 0x4c ≤ j) :
    i8 c j = i8 x.c j := by
  simp only [i8, hn_getD_Kp hK j hj]

omit [CodeEnv] in
theorem hn_i32_Kp0 {x : PArgs} {c : List UInt8} (hK : Kp x c) : i32 c 0 = i32 x.c 0 := by
  simp only [i32, List.drop_zero, hK.1]

omit [CodeEnv] in
theorem hn_i32_K24 {x : PArgs} {c : List UInt8} (hK : K24 x c) (o : Nat) (h1 : 4 ≤ o)
    (h2 : o + 4 ≤ 0x24) : i32 c o = i32 x.c o := by
  have e : ∀ l : List UInt8, (l.drop o).take 4 = (((l.drop 4).take 0x20).drop (o - 4)).take 4 := by
    intro l
    rw [List.drop_take, List.drop_drop, List.take_take, show 4 + (o - 4) = o by omega,
      Nat.min_eq_left (by omega)]
  have hK' : (x.c.drop 4).take 0x20 = (c.drop 4).take 0x20 := hK.symm
  simp only [i32, e c, e x.c]
  unfold K24 at hK
  rw [hK]

omit [CodeEnv] in
/-- `Rng` from the input (`*ps` past the header fields, `PsInv`). -/
theorem hn_Rng {x : PArgs} {c : List UInt8} (hP : PsInv c) (hK : Kp x c) (hw : PsWFb x.c) :
    Rng c := by
  obtain ⟨h756, h8⟩ := Rng0_of_Kp hP hK hw
  refine ⟨h756, h8, ?_, ?_⟩
  · intro e he b hb
    rw [hn_i8_Kp hK _ (by omega)]
    exact hw.2.2.2.2.2.1 e he b hb
  · intro e he b hb
    rw [hn_i8_Kp hK _ (by omega), hn_i8_Kp hK (586 + 34 * e + b) (by omega)]
    exact hw.2.2.2.2.2.2.1 e he b hb

omit [CodeEnv] in
/-- `IidS` from the header bit's facts. -/
theorem hn_IidS {x : PArgs} {c f : List UInt8} (hH : HdrOk x c f) (hK : Kp x c)
    (hw : PsWFb x.c) : IidS c (rd f 0x18 4) := by
  intro h0 h4
  by_cases hb : rd f 0x18 4 = 0
  · have k24 := hH.1 hb
    have hs : i32 x.c 0 ≠ 0 := by
      rcases h0 with h | h
      · rw [← hn_i32_Kp0 hK]; exact h
      · exact absurd hb h
    rw [hn_i32_K24 k24 4 (by omega) (by omega)] at h4
    rw [hn_i32_K24 k24 12 (by omega) (by omega)]
    exact (hw.2.2.2.2.2.2.2 hs).2.2.2.2.1 h4
  · exact hH.2 hb h4

/-- The border code's exits: the borders `0..v` read, `num_env = v`, give `AtHdr`. -/
theorem toHdr {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {v : Nat} (hB : BS k Ext x ra t₀ s c f v) (hb : BordTo c v) :
    AtHdr k Ext x ra t₀ s := by
  obtain ⟨⟨hCm, hR, hbx, hK⟩, hH, h38, hv4, hne, h58, h10, -, hix⟩ := hB
  refine ⟨c, f, hCm, hR, hbx, hix, ⟨by omega, by omega, by rw [h58, hne], h38⟩, by omega,
    fun hw => ⟨hn_Rng hCm.2.1.2.2.2.1 hK hw, ⟨by omega, by omega, hb.1, ?_, ?_⟩, hn_IidS hH hK hw⟩⟩
  · intro e he; exact hb.2.1 e (by omega)
  · intro e he; exact hb.2.2 e (by omega)

omit [CodeEnv] in
theorem hn_BordTo0 {c : List UInt8} {n : Nat} (h : bord c 0 = -1) (hn : n = 0) : BordTo c n := by
  subst hn
  refine ⟨h, fun e he => absurd he (by omega), fun e he => ?_⟩
  have : e = 0 := by omega
  subst this; rw [h]; decide

/-- `num_env = 0`: straight to the header exit. -/
theorem toHdr0 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {v : Nat} (hB : BS k Ext x ra t₀ s c f v) (hv : v = 0) :
    AtHdr k Ext x ra t₀ s :=
  toHdr hB (hn_BordTo0 hB.2.2.2.2.2.2.2.1 hv)

/-! ## The flag tests -/

omit [CodeEnv] in
/-- `test %r8b,%r8b; jle` on a small register: taken iff it is `0`. -/
theorem hn_le8 (d : BitVec 64) (h2 : d.toNat < 128) (a : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 8 d &&& BitVec.setWidth 8 d)
      { cf := false, af := a, of := false }) = decide (d.toNat = 0) := by
  have e1 : (BitVec.setWidth 8 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]; omega
  have e2 : ((BitVec.setWidth 8 d) == BitVec.zero 8) = decide (d.toNat = 0) := by
    have : (BitVec.setWidth 8 d = BitVec.zero 8) ↔ d.toNat = 0 := by
      have z : (BitVec.zero 8).toNat = 0 := rfl
      rw [← BitVec.toNat_inj, z, BitVec.toNat_setWidth]; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, this]
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self, e1, e2]
  cases decide (d.toNat = 0) <;> rfl

omit [CodeEnv] in
/-- `test %esi,%esi; jne` on a small register: taken iff it is not `0`. -/
theorem hn_nz32 (d : BitVec 64) (h2 : d.toNat < 2 ^ 31) (a : Bool) :
    CondCode.nz.interp (StatusFlags.from_result (BitVec.setWidth 32 d &&& BitVec.setWidth 32 d)
      { cf := false, af := a, of := false }) = decide (d.toNat ≠ 0) := by
  have e2 : ((BitVec.setWidth 32 d) == BitVec.zero 32) = decide (d.toNat = 0) := by
    have : (BitVec.setWidth 32 d = BitVec.zero 32) ↔ d.toNat = 0 := by
      have z : (BitVec.zero 32).toNat = 0 := rfl
      rw [← BitVec.toNat_inj, z, BitVec.toNat_setWidth]; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, this]
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self, e2]
  by_cases h : d.toNat = 0 <;> simp [h]

/-! ## Writes of `num_env` and the borders (offsets `44..0x4c`) -/

/-- A write at `[o, o+4) ⊆ [44, 0x4c)` keeps the header facts. -/
theorem hn_hdr_wr {x : PArgs} {c f : List UInt8} (hl : c.length = 764) (o : Nat) (v : Int)
    (h1 : 44 ≤ o) (h2 : o + 4 ≤ 0x4c) (hH : HdrOk x c f) (h38 : S38 c f) (hK : Kp x c) :
    HdrOk x (wr c o 4 v) f ∧ S38 (wr c o 4 v) f ∧ Kp x (wr c o 4 v) := by
  have hi : ∀ o', o' + 4 ≤ 44 → i32 (wr c o 4 v) o' = i32 c o' :=
    fun o' h => i32_wr c o 4 o' v (by omega) (by omega)
  have hk24 : ((wr c o 4 v).drop 4).take 0x20 = (c.drop 4).take 0x20 :=
    wr_drop_take_disj c o 4 4 0x20 v (by omega) (Or.inl (by omega))
  refine ⟨⟨fun h => ?_, fun h hi4 => ?_⟩, ?_, Kp_wr hK o 4 v (by omega) h2 (by omega)⟩
  · unfold K24; rw [hk24]; exact hH.1 h
  · rw [hi 4 (by omega)] at hi4; rw [hi 12 (by omega)]; exact hH.2 h hi4
  · unfold S38; rw [hi 40 (by omega)]; exact h38

/-- `num_env` (offset 44) written with a value in `[0, 5]` keeps `PsInv`. -/
theorem hn_PsInv_wr44 {c : List UInt8} (h : PsInv c) (W : BitVec 32) (h0 : 0 ≤ W.toInt)
    (h5 : W.toInt ≤ 5) : PsInv (wr c 44 4 W.toInt) := by
  obtain ⟨hl, e12, e16, e28, e40, e44, e8⟩ := h
  have hw : ∀ o', o' + 4 ≤ 44 → i32 (wr c 44 4 W.toInt) o' = i32 c o' := fun o' h1 =>
    i32_wr c 44 4 o' _ (by omega) (by omega)
  refine ⟨by rw [wr_length _ _ _ _ (by omega), hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 12 (by omega)]; exact e12
  · rw [hw 16 (by omega)]; exact e16
  · rw [hw 28 (by omega)]; exact e28
  · rw [hw 40 (by omega)]; exact e40
  · rw [i32_wr_same c 44 W (by omega)]; exact ⟨h0, h5⟩
  · rw [hw 8 (by omega)]; exact e8

omit [CodeEnv] in
/-- A write at offset `≥ 48` keeps `PsInv`. -/
theorem hn_PsInv_wr_hi {c : List UInt8} (h : PsInv c) (o n : Nat) (v : Int) (h1 : 48 ≤ o)
    (h2 : o + n ≤ 764) : PsInv (wr c o n v) := by
  obtain ⟨hl, e12, e16, e28, e40, e44, e8⟩ := h
  have hw : ∀ o', o' + 4 ≤ 48 → i32 (wr c o n v) o' = i32 c o' := fun o' h3 =>
    i32_wr c o n o' _ (by omega) (by omega)
  refine ⟨by rw [wr_length _ _ _ _ (by omega), hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 12 (by omega)]; exact e12
  · rw [hw 16 (by omega)]; exact e16
  · rw [hw 28 (by omega)]; exact e28
  · rw [hw 40 (by omega)]; exact e40
  · rw [hw 44 (by omega)]; exact e44
  · rw [hw 8 (by omega)]; exact e8

omit [CodeEnv] in
theorem hn_sw32_toInt (r : BitVec 64) (h : r.toNat < 2 ^ 31) :
    (BitVec.setWidth 32 r).toInt = r.toNat := by
  rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_setWidth]; omega), BitVec.toNat_setWidth]
  omega

/-- After `0x216`'s two stores (`num_env = eax`, `border[0] = -1`): `BS` at `v = eax`. -/
theorem hn_BS216 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (hHB : HB k Ext x ra t₀ s c f) (hH : HdrOk x c f) (h38 : S38 c f)
    (hix : Ix x (s.regs.get64 .r8)) (hax : (s.regs.get64 .rax).toNat ≤ 4)
    (h10 : s.regs.get64 .r10 = s.regs.get64 .rax) (h58 : rd f 0x58 8 = (s.regs.get64 .rax).toNat)
    (hr : s'.regs = s.regs)
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ f (wr (wr c 44 4 (BitVec.setWidth 32 (s.regs.get64 .rax)).toInt)
      52 4 (BitVec.setWidth 32 4294967295#64).toInt) x.idx) :
    BS k Ext x ra t₀ s' (wr (wr c 44 4 (BitVec.setWidth 32 (s.regs.get64 .rax)).toInt)
      52 4 (BitVec.setWidth 32 4294967295#64).toInt) f (s.regs.get64 .rax).toNat := by
  obtain ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, -⟩, ⟨h13, h12⟩, hbx, hK⟩ := hHB
  have hcl : c.length = 764 := hP.1
  have hw := hn_sw32_toInt (s.regs.get64 .rax) (by omega)
  have hP1 := hn_PsInv_wr44 hP (BitVec.setWidth 32 (s.regs.get64 .rax)) (by omega) (by omega)
  have hl1 : (wr c 44 4 (BitVec.setWidth 32 (s.regs.get64 .rax)).toInt).length = 764 := hP1.1
  obtain ⟨hH1, h381, hK1⟩ := hn_hdr_wr hcl 44 (BitVec.setWidth 32 (s.regs.get64 .rax)).toInt
    (by omega) (by omega) hH h38 hK
  obtain ⟨hH2, h382, hK2⟩ := hn_hdr_wr hl1 52 (BitVec.setWidth 32 4294967295#64).toInt
    (by omega) (by omega) hH1 h381 hK1
  refine ⟨⟨⟨hC, ⟨by rw [hr]; exact hsp, by rw [hr]; exact hbp, hf,
      hn_PsInv_wr_hi hP1 52 4 _ (by omega) (by omega), hbl, h08, hid⟩, hm⟩,
    ⟨by rw [hr]; exact h13, by rw [hr]; exact h12⟩, by rw [hr]; exact hbx, hK2⟩,
    hH2, h382, hax, ?_, h58, by rw [hr, h10], ?_, by rw [hr]; exact hix⟩
  · show i32 _ 44 = _
    rw [i32_wr _ 52 4 44 _ (by omega) (by omega), i32_wr_same _ _ _ (by omega), hw]
  · show i32 _ (52 + 4 * 0) = _
    rw [i32_wr_same _ _ _ (by omega)]; decide

/-! ## Signed compares of the 5-bit borders -/

omit [CodeEnv] in
theorem hn_ge32 (a b : BitVec 32) (cf af : Bool) :
    CondCode.ge.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := ((a - b).signed != a.signed - b.signed) })
      = decide (b.toInt ≤ a.toInt) := by
  rw [CondCode.interp_ge, StatusFlags.sf_from_result, StatusFlags.of_from_result]
  grind [BitVec.signed_eq]

omit [CodeEnv] in
theorem hn_l32 (a b : BitVec 32) (cf af : Bool) :
    CondCode.l.interp (StatusFlags.from_result (a - b)
      { cf := cf, af := af, of := ((a - b).signed != a.signed - b.signed) })
      = decide (a.toInt < b.toInt) := by
  rw [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result]
  grind [BitVec.signed_eq]

omit [CodeEnv] in
theorem hn_z32 (A : BitVec 32) (k : Nat) (hk : k < 2 ^ 32) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (A - BitVec.setWidth 32 (BitVec.ofNat 64 k)) f)
      = decide (A.toNat = k) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result]
  have : (A - BitVec.setWidth 32 (BitVec.ofNat 64 k) == 0#32) = decide (A.toNat = k) := by
    have e : ∀ a b : BitVec 32, a - b = 0#32 ↔ a = b := fun a b =>
      ⟨fun h => by have := congrArg (· + b) h; simpa [BitVec.sub_add_cancel] using this, fun h => by subst h; simp⟩
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, e,
      ← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  simpa using this

omit [CodeEnv] in
theorem hn_shr27 (v : BitVec 32) : (v.ushiftRight 27).toNat < 32 := by
  show (v >>> 27).toNat < 32
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega

omit [CodeEnv] in
theorem hn_shr27_toInt (v : BitVec 32) : (v.ushiftRight 27).toInt = (v.ushiftRight 27).toNat := by
  have : (v.ushiftRight 27).toNat < 32 := by
    show (v >>> 27).toNat < 32
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := v.isLt; omega
  rw [BitVec.toInt_eq_toNat_of_lt (by omega)]



omit [CodeEnv] in
theorem hn_shr27_le (v : BitVec 32) : (v.ushiftRight 27).toInt ≤ 31 := by
  rw [hn_shr27_toInt]; have := hn_shr27 v; omega

omit [CodeEnv] in
theorem hn_shr27_ge (v : BitVec 32) (b : Int) (hb : b = -1) : b ≤ (v.ushiftRight 27).toInt := by
  rw [hn_shr27_toInt]; omega

omit [CodeEnv] in
theorem hn_shr27_nat (v : BitVec 32) :
    (BitVec.setWidth 64 (v.ushiftRight 27)).toNat = (v.ushiftRight 27).toInt.toNat := by
  rw [hn_shr27_toInt, Int.toNat_natCast, BitVec.toNat_setWidth]; have := hn_shr27 v; omega

/-! ## `incl %r` (as `Apply.inc_reg_w32_spec`, which this file does not import) -/

theorem hn_inc32_spec {p : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let v := a + 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r (v.setWidth 64),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                    of := v.signed != a.signed + 1 } } ⦄
      (Directive.instr (.regular asz .W32 (.inc (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All]
    (try simp only [Reg64s.get_low32, Reg64s.set_low32])
    exact hP)

/-- `BS` after register moves that keep the frame registers, `r10`, and a reader index in `r8`. -/
theorem hn_BS_mv {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {v : Nat} (hB : BS k Ext x ra t₀ s c f v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12)
    (hbx : s'.regs.get64 .rbx = s.regs.get64 .rbx) (h10 : s'.regs.get64 .r10 = s.regs.get64 .r10)
    (h8 : Ix x (s'.regs.get64 .r8)) (hm : s'.dmem = s.dmem) :
    BS k Ext x ra t₀ s' c f v := by
  obtain ⟨⟨⟨hC, ⟨hsp0, hbp0, hf, hP, hbl, h08, hid⟩, hm0⟩, ⟨h130, h120⟩, hbx0, hK⟩, hH, h38, hv4, hne,
    h58, h100, hb0, -⟩ := hB
  exact ⟨⟨⟨hC, ⟨by rw [hsp]; exact hsp0, by rw [hbp]; exact hbp0, hf, hP, hbl, h08, hid⟩,
    by rw [hm]; exact hm0⟩, ⟨by rw [h13]; exact h130, by rw [h12]; exact h120⟩, by rw [hbx]; exact hbx0,
    hK⟩, hH, h38, hv4, hne, h58, by rw [h10]; exact h100, hb0, h8⟩

omit [CodeEnv] in
/-- `mov -0x48(%rbp),%rax; inc %eax` with `num_env = v ≤ 4` in the slot. -/
theorem hn_inc_v (v : Nat) (hv : v ≤ 4) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 64 (v : Int)) + 1#32)).toNat = v + 1 := by
  have h1 : (BitVec.ofInt 64 (v : Int)).toNat = v := by
    rw [BitVec.toNat_ofInt]; omega
  have h2 : (1#32).toNat = 1 := rfl
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, h1, h2]
  omega

omit [CodeEnv] in
theorem hn_inc_v32 (v : Nat) (hv : v ≤ 4) :
    (BitVec.setWidth 32 (BitVec.ofInt 64 (v : Int)) + 1#32).toNat = v + 1 := by
  have h := hn_inc_v v hv
  rw [BitVec.toNat_setWidth] at h
  have := (BitVec.setWidth 32 (BitVec.ofInt 64 (v : Int)) + 1#32).isLt
  omega

/-! ## The border writes (`border[e]` at `52 + 4 e`, `e ≥ 1`) -/

/-- A border write (offset in `[56, 0x4c)`) keeps `BS` (the registers it reads unchanged). -/
theorem hn_BS_wr {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {v : Nat} (hB : BS k Ext x ra t₀ s c f v) (o : Nat) (w : Int)
    (h1 : 56 ≤ o) (h2 : o + 4 ≤ 0x4c)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12)
    (hbx : s'.regs.get64 .rbx = s.regs.get64 .rbx) (h10 : s'.regs.get64 .r10 = s.regs.get64 .r10)
    (h8 : Ix x (s'.regs.get64 .r8))
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ f (wr c o 4 w) x.idx) :
    BS k Ext x ra t₀ s' (wr c o 4 w) f v := by
  obtain ⟨⟨⟨hC, ⟨hsp0, hbp0, hf, hP, hbl, h08, hid⟩, -⟩, ⟨h130, h120⟩, hbx0, hK⟩, hH, h38, hv4, hne,
    h58, h100, hb0, -⟩ := hB
  have hcl : c.length = 764 := hP.1
  obtain ⟨hH1, h381, hK1⟩ := hn_hdr_wr hcl o w (by omega) h2 hH h38 hK
  refine ⟨⟨⟨hC, ⟨by rw [hsp]; exact hsp0, by rw [hbp]; exact hbp0, hf,
      hn_PsInv_wr_hi hP o 4 _ (by omega) (by omega), hbl, h08, hid⟩, hm⟩,
    ⟨by rw [h13]; exact h130, by rw [h12]; exact h120⟩, by rw [hbx]; exact hbx0, hK1⟩,
    hH1, h381, hv4, ?_, h58, by rw [h10]; exact h100, ?_, h8⟩
  · show i32 _ 44 = _
    rw [i32_wr _ o 4 44 _ (by omega) (by omega)]; exact hne
  · show i32 _ (52 + 4 * 0) = _
    rw [i32_wr _ o 4 _ _ (by omega) (by omega)]; exact hb0

/-- A border decreases: the error path. -/
theorem hn_err_wr {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {v : Nat} (hB : BS k Ext x ra t₀ s c f v) (o : Nat) (w : Int)
    (h1 : 56 ≤ o) (h2 : o + 4 ≤ 0x4c)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (hbx : s'.regs.get64 .rbx = s.regs.get64 .rbx)
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ f (wr c o 4 w) x.idx) :
    AtErr k Ext x ra t₀ s' := by
  obtain ⟨⟨⟨hC, ⟨hsp0, hbp0, hf, hP, hbl, h08, hid⟩, -⟩, -, hbx0, hK⟩, -⟩ := hB
  have hcl : c.length = 764 := hP.1
  have hP1 := hn_PsInv_wr_hi hP o 4 w (by omega) (by omega)
  have hK1 := Kp_wr hK o 4 w (by omega) h2 (by omega)
  exact ⟨_, f, ⟨hC, ⟨by rw [hsp]; exact hsp0, by rw [hbp]; exact hbp0, hf, hP1, hbl, h08, hid⟩, hm⟩,
    by rw [hbx]; exact hbx0, fun hw => Rng0_of_Kp hP1 hK1 hw⟩

/-- `border[j+1]` read, not below `border[j]`, at most `31`. -/
theorem hn_BordTo_wr {c : List UInt8} {j : Nat} (hl : c.length = 764) (hb : BordTo c j) (hj : j < 5)
    (w : BitVec 32) (hw : bord c j ≤ w.toInt) (h31 : w.toInt ≤ 31) :
    BordTo (wr c (52 + 4 * (j + 1)) 4 w.toInt) (j + 1) := by
  have hs : bord (wr c (52 + 4 * (j + 1)) 4 w.toInt) (j + 1) = w.toInt :=
    i32_wr_same c _ w (by omega)
  have ho : ∀ e, e ≤ j → bord (wr c (52 + 4 * (j + 1)) 4 w.toInt) e = bord c e := fun e he =>
    i32_wr c _ 4 _ _ (by omega) (by omega)
  obtain ⟨h0, hm, h3⟩ := hb
  refine ⟨by rw [ho 0 (by omega)]; exact h0, fun e he => ?_, fun e he => ?_⟩
  · by_cases h : e = j
    · subst h; rw [hs, ho e (by omega)]; exact hw
    · rw [ho e (by omega), ho (e + 1) (by omega)]; exact hm e (by omega)
  · by_cases h : e = j + 1
    · subst h; rw [hs]; exact h31
    · rw [ho e (by omega)]; exact h3 e (by omega)

theorem hn_bord_wr_same (c : List UInt8) (j : Nat) (hl : c.length = 764) (hj : j < 5) (w : BitVec 32) :
    bord (wr c (52 + 4 * (j + 1)) 4 w.toInt) (j + 1) = w.toInt :=
  i32_wr_same c _ w (by omega)

/-- A border read (`border[j+1]`, 5 bits) not below the previous one (in `r`, as a register):
the borders `0..j+1`, and the register holding the new one. -/
theorem hn_rd_bord {c : List UInt8} {j : Nat} (hl : c.length = 764) (hbt : BordTo c j) (hj : j < 5)
    (o : Nat) (ho : o = 52 + 4 * (j + 1)) (r : BitVec 64) (hr : r.toNat = (bord c j).toNat)
    (v : BitVec 32) (hge : ¬ (v.ushiftRight 27).toInt < (BitVec.setWidth 32 r).toInt) :
    BordTo (wr c o 4 (v.ushiftRight 27).toInt) (j + 1)
    ∧ (BitVec.setWidth 64 (v.ushiftRight 27)).toNat = (bord (wr c o 4 (v.ushiftRight 27).toInt) (j + 1)).toNat := by
  subst ho
  have h31 := hbt.2.2 j (by omega)
  have hlo : -1 ≤ bord c j := by
    have h0 := hbt.1
    have : ∀ e, e ≤ j → -1 ≤ bord c e := by
      intro e; induction e with
      | zero => intro _; omega
      | succ e ih => intro he; have := hbt.2.1 e (by omega); have := ih (by omega); omega
    exact this j (by omega)
  have hr32 : (BitVec.setWidth 32 r).toInt = r.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_setWidth]; omega), BitVec.toNat_setWidth]
    omega
  refine ⟨hn_BordTo_wr hl hbt hj _ ?_ (hn_shr27_le v), ?_⟩
  · rw [hr32] at hge; omega
  · rw [hn_shr27_nat, hn_bord_wr_same c j hl hj]

omit [CodeEnv] in
theorem hn_eax (r : BitVec 64) (n : Nat) (h : r.toNat = n) (hn : n < 2 ^ 32) :
    (BitVec.setWidth 32 r).toNat = n := by
  rw [BitVec.toNat_setWidth]; omega

/-! ## `av_log` from the border code (`0x297`) -/

/-- `Fr` with `av_log`'s frame at the head: the return slot, the callee's reservation, `Ext`. -/
theorem hn_Fr_ext (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f c : List UInt8) (i : BitVec 32) :
    ∃ F, Fr k Ext x ra t₀ f c i = 8 ?@ (t₀.regs.get64 .rsp - 0xb0#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0xb0#64) ⋆ (Ext ⋆ F)) := by
  refine ⟨f =@ (rsp0 t₀ - 0xa8#64) ⋆ (Sv t₀ ⋆ ((c =@ arg2 t₀ ⋆ (GbW (arg1 t₀) x i
    ⋆ (Blocks [(x.buf, x.L)] ⋆ PsTabs x.v))) ⋆ (RetCell ra (rsp0 t₀) ⋆ x.R))), ?_⟩
  simp only [Fr, PF]; ac_rfl

/-! ## `movq sym(%rip), %r` (the `ff_log2_tab` GOT slot) -/

section RipLoad
open Lean.Order
variable {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

theorem hn_mov_load_rip_spec (r : Reg64) (l : Label) :
    ⦃ fun s =>
        let a := ((_root_.Executable.labels cenv).label l).toBitVec
        ((Mem.loadInt s.dmem a 8).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 8 = some v →
            WP.wp p Q E { s with regs := s.regs.set64 r (BitVec.ofInt 64 v) }) ⦄
      (Directive.instr (.regular .W64 .W64
          (.mov (.reg (.low r .W64))
            (.regOrMem (.mem ⟨some .rip, none, .sub (.label l) .after_current_instruction⟩)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or]
    simp only [MachineData.load, AddrExpr.zeroExtend_interp_rip_label,
      Width.bytes, hv, Effects.All]
    exact hk v hv _ hpl'

end RipLoad

end Kraken.Examples.Sbr.Ps
