import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

/-!
# `ff_ps_read_data`, the `iid`/`icc` parameters: lemmas for the blocks of `PsBlkL*`

* Stores into `*ps` inside `iid_par` (`[76, 246)`) and `icc_par` (`[246, 416)`) keep `PsInv`,
  `Hdr`, `IidS`, `Rng0`, and the clauses about the other array (`*_wr` lemmas).
* The stored value read back (`i8_wr_self`), the zeroed ranges of the `memset`s (`Zr`).
* The loaded 32-bit fields (`rd` is unsigned, `i32` signed: equal as bit vectors).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-! ## Loads -/

theorem int_ofBytes_nat (bs : List UInt8) : Int.ofBytes bs = ((Nat.ofBytes bs : Nat) : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Int.ofBytes bs * 256 + ((b.toNat : Nat) : Int) = ((Nat.ofBytes bs * 256 + b.toNat : Nat) : Int)
    rw [ih]; omega

/-- A 4-byte field as loaded is the signed field as a bit vector. -/
theorem rd_i32 (c : List UInt8) (o : Nat) :
    BitVec.ofInt 32 (rd c o 4) = BitVec.ofInt 32 (i32 c o) := by
  simp only [rd, i32, BitVec.ofInt_toInt, int_ofBytes_nat]
  rfl

/-! ## Stores into `*ps` -/

theorem wr_len (c : List UInt8) (o n : Nat) (v : Int) (h : o + n ≤ c.length) :
    (wr c o n v).length = c.length := wr_length c o n v h

/-- A store at `[o, o + n)` with `48 ≤ o` keeps `PsInv`. -/
theorem PsInv_wr {c : List UInt8} {o n : Nat} (v : Int) (h : PsInv c) (ho : 48 ≤ o)
    (hn : o + n ≤ 764) : PsInv (wr c o n v) := by
  obtain ⟨hl, h12, h16, h28, h40, h44, h8⟩ := h
  have e : ∀ o', o' + 4 ≤ 48 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' hd => i32_wr c o n o' v (by omega) (Or.inl (by omega))
  refine ⟨by rw [wr_len _ _ _ _ (by omega)]; exact hl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [e 12 (by omega), e 16 (by omega), e 28 (by omega), e 40 (by omega),
    e 44 (by omega), e 8 (by omega)]
  all_goals assumption

theorem Hdr_wr {c : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) (h : Hdr c)
    (ho : 76 ≤ o) (hn : o + n ≤ 764) : Hdr (wr c o n v) := by
  have e : ∀ o', o' + 4 ≤ 76 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' hd => i32_wr c o n o' v (by omega) (Or.inl (by omega))
  obtain ⟨d0, d4, db0, dmono, d31⟩ := h
  have hne : ne (wr c o n v) = ne c := e 44 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hne]; exact d0
  · rw [hne]; exact d4
  · simp only [bord]; rw [e 52 (by omega)]; exact db0
  · intro e' he'
    rw [hne] at he'
    simp only [bord]
    rw [e _ (by omega), e _ (by omega)]; exact dmono e' he'
  · intro e' he'
    rw [hne] at he'
    simp only [bord]
    rw [e _ (by omega)]; exact d31 e' he'

theorem IidS_wr {c : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) {hdr : Int}
    (h : IidS c hdr) (ho : 16 ≤ o) (hn : o + n ≤ 764) : IidS (wr c o n v) hdr := by
  have e : ∀ o', o' + 4 ≤ 16 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' hd => i32_wr c o n o' v (by omega) (Or.inl (by omega))
  simp only [IidS] at h ⊢
  rw [e 0 (by omega), e 4 (by omega), e 12 (by omega)]
  exact h

theorem Rng0_wr {c : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) (h : Rng0 c)
    (ho : 12 ≤ o) (hn : o + n ≤ 756) : Rng0 (wr c o n v) := by
  have e1 : i32 (wr c o n v) 756 = i32 c 756 := i32_wr c o n 756 v (by omega) (Or.inr hn)
  have e2 : i32 (wr c o n v) 8 = i32 c 8 := i32_wr c o n 8 v (by omega) (Or.inl (by omega))
  simp only [Rng0] at h ⊢
  rw [e1, e2]; exact h

theorem RngPO_wr {c : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) (h : RngPO c)
    (hn : o + n ≤ 416) : RngPO (wr c o n v) := by
  intro e he b hb
  rw [i8_wr c o n _ v (by omega) (Or.inr (by omega)),
    i8_wr c o n _ v (by omega) (Or.inr (by omega))]
  exact h e he b hb

/-- A store into `iid_par` keeps `Rng`. -/
theorem Rng_wr_iid {c : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) (h : Rng c)
    (ho : 12 ≤ o) (hn : o + n ≤ 246) : Rng (wr c o n v) := by
  obtain ⟨r756, r8, ricc, rpar⟩ := h
  have e1 : i32 (wr c o n v) 756 = i32 c 756 := i32_wr c o n 756 v (by omega) (Or.inr (by omega))
  have e2 : i32 (wr c o n v) 8 = i32 c 8 := i32_wr c o n 8 v (by omega) (Or.inl (by omega))
  refine ⟨by rw [e1]; exact r756, by rw [e2]; exact r8, ?_, ?_⟩
  · intro e he b hb
    rw [i8_wr c o n _ v (by omega) (Or.inr (by omega))]; exact ricc e he b hb
  · intro e he b hb
    rw [i8_wr c o n _ v (by omega) (Or.inr (by omega)),
      i8_wr c o n _ v (by omega) (Or.inr (by omega))]
    exact rpar e he b hb

/-- A store into `icc_par` keeps `IidB`. -/
theorem IidB_wr_icc {c : List UInt8} {o n : Nat} (v : Int) (hl : c.length = 764) {m : Int}
    (h : IidB c m) (hm : m ≤ 5) (ho : 246 ≤ o) (hn : o + n ≤ 764) : IidB (wr c o n v) m := by
  have e : ∀ o', o' + 4 ≤ 246 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' hd => i32_wr c o n o' v (by omega) (Or.inl (by omega))
  intro e' he' b hb hc
  rw [e 4 (by omega), e 12 (by omega)] at hc
  have := h e' he' b hb hc
  rw [e 8 (by omega), i8_wr c o n _ v (by omega) (Or.inl (by omega))]
  exact this

/-! ## Frame slot addresses -/

/-- `rbp - d` (`rbp = rsp0 - 8`) is offset `0xa0 - d` of the frame cell at `rsp0 - 0xa8`. -/
theorem slot_addr {r b : BitVec 64} (h : r = b - 8#64) (d o : Nat) (hd : o + d = 0xa0) :
    r + (-(no_index (OfNat.ofNat d : Int64))).toBitVec = b - 0xa8#64 + BitVec.ofNat 64 o := by
  rw [Int64.toBitVec_neg_ofNat_norm, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := b.isLt
  omega

/-- `rbp - d` as a `slot64` address. -/
theorem slot_addr_sub {r b : BitVec 64} (h : r = b - 8#64) (d o : Nat) (hd : o + d = 0xa0) :
    r - BitVec.ofNat 64 d = b - 0xa8#64 + BitVec.ofNat 64 o := by
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := b.isLt
  omega

theorem ofNat64_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The measure of a counted loop: `n - e` for `e ≤ n < 2 ^ 63`. -/
theorem meas_sub (n : Int) (e : Nat) (h0 : (e : Int) ≤ n) (h1 : n < 2 ^ 63) :
    (BitVec.ofInt 64 n - BitVec.ofNat 64 e).toNat = n.toNat - e := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- `inc` and `cmp` against the loop bound `n` of a counted loop at `e < n`: equal iff `e + 1 = n`. -/
theorem cnt_beq (n : Int) (e : Nat) (he : (e : Int) < n) (h1 : n ≤ 4) :
    (BitVec.ofNat 64 e + 1 - BitVec.ofInt 64 n == BitVec.zero 64) = decide ((e : Int) + 1 = n) := by
  have key : (BitVec.ofNat 64 e + 1 - BitVec.ofInt 64 n = BitVec.zero 64) ↔ ((e : Int) + 1 = n) := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    have h1' : (1 : BitVec 64).toNat = 1 := rfl
    show _ = 0 ↔ _
    omega
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact key

/-- The next row of a 34-byte-row array. -/
theorem row_step (a : BitVec 64) (b e : Nat) :
    BitVec.setWidth 64 (Int64.toBitVec 34) + (a + BitVec.ofNat 64 (b + 34 * e))
      = a + BitVec.ofNat 64 (b + 34 * (e + 1)) := by
  have h : BitVec.setWidth 64 (Int64.toBitVec 34) = BitVec.ofNat 64 34 := rfl
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toNat_ofInt64_small (n : Int) (h0 : 0 ≤ n) (h1 : n < 2 ^ 63) :
    (BitVec.ofInt 64 n).toNat = n.toNat := by
  simp only [BitVec.toNat_ofInt]
  omega

/-! ## Extensions -/

/-- Zero-extending a nonnegative 32-bit value is sign-extending it. -/
theorem zx_ofInt32 (v : Int) (h0 : 0 ≤ v) (h1 : v < 2 ^ 31) :
    (BitVec.ofInt 32 v).setWidth 64 = BitVec.ofInt 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

/-! ## Flags -/

/-- `test %al, %al; jle` on a loaded `0 ≤ n ≤ 4`: taken iff `n = 0`. -/
theorem le_and8_small (n : Int) (h0 : 0 ≤ n) (h4 : n ≤ 4) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result
      (BitVec.setWidth 8 (BitVec.ofInt 64 n) &&& BitVec.setWidth 8 (BitVec.ofInt 64 n))
      { cf := false, af := af, of := false }) = decide (n = 0) := by
  have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## Read after write -/

theorem rd_wr_self (l : List UInt8) (o n w : Nat) (v : Int) (h : o + n ≤ l.length)
    (hw : w = 8 * n) : BitVec.ofInt w (rd (wr l o n v) o n) = BitVec.ofInt w v := by
  rw [rd_wr_same l o n v h, BitVec.ofInt_ofBytes_toBytes_eq w n hw]

theorem i32_wr_disj (c : List UInt8) (o n o' : Nat) (v : Int) (h : o + n ≤ c.length)
    (hd : o' + 4 ≤ o ∨ o + n ≤ o') : i32 (wr c o n v) o' = i32 c o' := i32_wr c o n o' v h hd

theorem i8_wr_disj (c : List UInt8) (o n j : Nat) (v : Int) (h : o + n ≤ c.length)
    (hd : j + 1 ≤ o ∨ o + n ≤ j) : i8 (wr c o n v) j = i8 c j := i8_wr c o n j v h hd

/-- The byte stored by `mov %r8b, (…)` read back as `int8_t`. -/
theorem i8_wr_self (c : List UInt8) (o : Nat) (b : BitVec 8) (h : o + 1 ≤ c.length) :
    i8 (wr c o 1 b.toInt) o = b.toInt := by
  simp only [i8, getD_win _ o, wr_drop_take_same c o 1 _ h]
  have key : BitVec.ofInt 8 (Int.ofBytes (Int.toBytes 1 b.toInt)) = b :=
    BitVec.ofInt_ofBytes_toBytes 8 1 rfl b
  have hl : (Int.toBytes 1 b.toInt).length = 1 := Int.toBytes_length 1 _
  generalize Int.toBytes 1 b.toInt = l at key hl
  match l, hl with
  | [u], _ =>
    have e : Int.ofBytes [u] = ((u.toNat : Nat) : Int) := by
      show Int.ofBytes [] * 256 + ((u.toNat : Nat) : Int) = _
      simp [Int.ofBytes]
    rw [e] at key
    simp only [List.getD_cons_zero]
    rw [← key]
    rfl

end Kraken.Examples.Sbr.Ps

/-- The side conditions of `fsimp`: `omega`, which sees the length facts in the context, after
`wr_length` for nested stores. -/
macro "fdisch" : tactic =>
  `(tactic| (first | omega | (simp (disch := omega) only [Kraken.Examples.Sbr.Ps.wr_length]; omega)))

/-- Read-after-write on the byte-list cells `f`, `*ps`. -/
macro "fsimp" : tactic => `(tactic| simp (disch := fdisch) only
  [Kraken.Examples.Sbr.Ps.rd_wr_disj, Kraken.Examples.Sbr.Ps.rd_wr_self,
   Kraken.Examples.Sbr.Ps.i32_wr_disj, Kraken.Examples.Sbr.Ps.i8_wr_disj,
   Kraken.Examples.Sbr.Ps.wr_length])

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-! ## Stores into the free slots of the frame -/

/-- A store into a slot that no frame invariant mentions keeps `LB`. -/
theorem LB_wrf {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {o n : Nat} {v : Int} (h : LB k Ext x ra t₀ s c f)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (hR : Rdr x s') (hI : Ix x (s'.regs.get64 .r8))
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ (wr f o n v) c x.idx)
    (hd : o + n ≤ 0x08 ∨ (0x1c ≤ o ∧ o + n ≤ 0x34) ∨ (0x48 ≤ o ∧ o + n ≤ 0x58)
      ∨ (0x60 ≤ o ∧ o + n ≤ 0x68)) :
    LB k Ext x ra t₀ s' c (wr f o n v) := by
  obtain ⟨⟨hC, ⟨hsp0, hbp0, hfl, hP, hb⟩, _⟩, _, _, ⟨⟨h0, h4, h58, h38⟩, h34, h68, h40⟩⟩ := h
  refine ⟨⟨hC, ⟨by rw [hsp, hsp0], by rw [hbp, hbp0], by fsimp; exact hfl, hP, by fsimp; exact hb⟩,
    hm⟩, hR, hI, ⟨⟨h0, h4, by fsimp; exact h58, by fsimp; exact h38⟩, by fsimp; exact h34,
    by fsimp; exact h68, by fsimp; exact h40⟩⟩

/-- `LB` moves to a state with the same frame registers, reader registers and memory. -/
theorem LB_mv {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} (h : LB k Ext x ra t₀ s c f)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (hR : Rdr x s') (hI : Ix x (s'.regs.get64 .r8))
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ f c x.idx) : LB k Ext x ra t₀ s' c f := by
  obtain ⟨⟨hC, ⟨hsp0, hbp0, hB⟩, _⟩, _, _, hS⟩ := h
  exact ⟨⟨hC, ⟨by rw [hsp, hsp0], by rw [hbp, hbp0], hB⟩, hm⟩, hR, hI, hS⟩

/-- `LB_wrf` for the state with only the memory replaced (a first of two stores). -/
theorem LB_wrf_m {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {o n : Nat} {v : Int} (h : LB k Ext x ra t₀ s c f) (m : Mem 64)
    (hm : m =⋆ Fr k Ext x ra t₀ (wr f o n v) c x.idx)
    (hd : o + n ≤ 0x08 ∨ (0x1c ≤ o ∧ o + n ≤ 0x34) ∨ (0x48 ≤ o ∧ o + n ≤ 0x58)
      ∨ (0x60 ≤ o ∧ o + n ≤ 0x68)) :
    LB k Ext x ra t₀ { s with dmem := m } c (wr f o n v) :=
  LB_wrf h rfl rfl h.2.1 h.2.2.1 hm hd

/-- `f.length` from `LB`. -/
theorem LB_fl {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} (h : LB k Ext x ra t₀ s c f) : f.length = 0x78 := h.1.2.1.2.2.1

/-- `c.length` from `LB`. -/
theorem LB_cl {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} (h : LB k Ext x ra t₀ s c f) : c.length = 764 := h.1.2.1.2.2.2.1.1

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-! ## The bit reader and flags (as in `PsBlkXLib`, which this chain does not import) -/

theorem lzx_shr_lt (w : BitVec 32) (n : Nat) (hn : n ≤ 32) :
    (BitVec.setWidth 64 (w.ushiftRight n)).toNat < 2 ^ (32 - n) := by
  simp only [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h2 : 2 ^ (32 - n) * 2 ^ n = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have h3 : w.toNat / 2 ^ n < 2 ^ (32 - n) :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, h2]; exact this)
  have h4 : 2 ^ (32 - n) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt (by omega)]; exact h3


/-- `index' = min(index + d, plus8)` (`add $d; cmp; cmovb`), as `vcgen` leaves it: a reader
index again, at least the old one. -/
theorem lix_clamp (x : PArgs) (r d : BitVec 64) (hd : (BitVec.setWidth 32 d).toNat ≤ 256) (hr : Ix x r)
    (hp : x.p8.toNat < 2 ^ 31) (hi : x.idx.toNat ≤ x.p8.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r))
        { cf := (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 d + BitVec.setWidth 32 r).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 d + BitVec.setWidth 32 r))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r))
        { cf := (x.p8 - (BitVec.setWidth 32 d + BitVec.setWidth 32 r)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 d + BitVec.setWidth 32 r).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 d + BitVec.setWidth 32 r)).toNat := by
  obtain ⟨h1, h2⟩ := hr
  have e : (BitVec.setWidth 32 d + BitVec.setWidth 32 r).toNat
      = (BitVec.setWidth 32 d).toNat + r.toNat := by
    have : (BitVec.setWidth 32 r).toNat = r.toNat % 2 ^ 32 := by simp [BitVec.toNat_setWidth]
    have := (BitVec.setWidth 32 d).isLt
    rw [BitVec.toNat_add]; omega
  have h64 : ∀ y : BitVec 32, (BitVec.setWidth 64 y).toNat = y.toNat := fun y => by
    rw [BitVec.toNat_setWidth]; have := y.isLt; omega
  simp only [Ix, h64]
  split
  · have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rename_i h
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, bne_iff_ne, ne_eq,
      Decidable.not_not] at h
    rw [BitVec.toNat_sub] at h
    rw [e] at h ⊢
    have := x.p8.isLt
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega

/-- `lix_clamp` with the addends swapped (`add %r8d,%eax`). -/
theorem ix_clamp2 (x : PArgs) (r d : BitVec 64) (hd : (BitVec.setWidth 32 d).toNat ≤ 256)
    (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31) (hi : x.idx.toNat ≤ x.p8.toNat) (af of : Bool) :
    Ix x (BitVec.setWidth 64 (if CondCode.c.interp (StatusFlags.from_result
        (x.p8 - (BitVec.setWidth 32 r + BitVec.setWidth 32 d))
        { cf := (x.p8 - (BitVec.setWidth 32 r + BitVec.setWidth 32 d)).unsigned !=
            x.p8.unsigned - (BitVec.setWidth 32 r + BitVec.setWidth 32 d).unsigned,
          af := af, of := of }) = true
      then x.p8 else BitVec.setWidth 32 r + BitVec.setWidth 32 d)) := by
  rw [BitVec.add_comm (BitVec.setWidth 32 r)]
  exact (lix_clamp x r d hd hr hp hi af of).1

/-- `get_bits1`'s index: `index + (index < plus8)` (`xor; cmp; setl; add`). -/
theorem lix_setl (x : PArgs) (r z : BitVec 64) (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31)
    (cf af : Bool) :
    Ix x (BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32
      ((BitVec.setWidth 64 (BitVec.setWidth 32 z ^^^ BitVec.setWidth 32 z)).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (BitVec.setWidth 32 r - x.p8)
          { cf := cf, af := af,
            of := (BitVec.setWidth 32 r - x.p8).signed !=
              (BitVec.setWidth 32 r).signed - x.p8.signed })).toNat))))
    ∧ r.toNat ≤ (BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32
      ((BitVec.setWidth 64 (BitVec.setWidth 32 z ^^^ BitVec.setWidth 32 z)).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (BitVec.setWidth 32 r - x.p8)
          { cf := cf, af := af,
            of := (BitVec.setWidth 32 r - x.p8).signed !=
              (BitVec.setWidth 32 r).signed - x.p8.signed })).toNat)))).toNat := by
  obtain ⟨h1, h2⟩ := hr
  rw [CondCode.interp_l_cmp_toInt32, BitVec.xor_self]
  have e0 : (BitVec.setWidth 64 (0#32)) = 0#64 := rfl
  rw [e0]
  have hr32 : (BitVec.setWidth 32 r).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth]; omega
  have hlt : (BitVec.setWidth 32 r).toInt < x.p8.toInt ↔ r.toNat < x.p8.toNat := by
    rw [BitVec.toInt_eq_toNat_of_msb, BitVec.toInt_eq_toNat_of_msb]
    · omega
    · rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
    · rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  have key : ∀ b : Bool, (BitVec.setWidth 64 (BitVec.setWidth 32 r + BitVec.setWidth 32
      ((0#64).replaceLow (BitVec.ofNat 8 b.toNat)))).toNat = r.toNat + b.toNat := by
    intro b
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    have hz : (BitVec.setWidth 32 ((0#64).replaceLow (BitVec.ofNat 8 b.toNat))).toNat
        = b.toNat := by
      rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]
      simp only [BitVec.toNat_ofNat]; omega
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, hz, hr32]
    omega
  simp only [Ix, key]
  by_cases h : r.toNat < x.p8.toNat
  · have : decide ((BitVec.setWidth 32 r).toInt < x.p8.toInt) = true := by
      simp only [decide_eq_true_eq]; exact hlt.mpr h
    rw [this]; simp only [Bool.toNat_true]; omega
  · have : decide ((BitVec.setWidth 32 r).toInt < x.p8.toInt) = false := by
      simp only [decide_eq_false_iff_not]; exact fun h' => h (hlt.mp h')
    rw [this]; simp only [Bool.toNat_false]; omega

/-- `test %eax,%eax; js`. -/
theorem ltest_s32 (w : BitVec 32) (a : Bool) :
    CondCode.s.interp (StatusFlags.from_result (w &&& w) { cf := false, af := a, of := false })
      = w.msb := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self]

/-- A 32-bit count as a variant digit is small. -/
theorem ltoInt_toNat_lt (w : BitVec 32) : w.toInt.toNat + 1 < 2 ^ 64 := by
  have := BitVec.toInt_lt (x := w); simp at this; omega

theorem ltoInt_toNat_lt' (w : BitVec 32) : w.toInt.toNat < 2 ^ 64 := by
  have := ltoInt_toNat_lt w; omega

/-- A lexicographic step on the second digit, or on the third with the second equal. -/
theorem llex3_lt {d a b x y : Nat} {r1 r2 : List Nat} (hl : r1.length = r2.length)
    (hb : b < 2 ^ 64) (hy : y < 2 ^ 64) (h : a < b ∨ (a = b ∧ x < y)) :
    lex (d :: a :: x :: r1) < lex (d :: b :: y :: r2) := by
  rcases h with h | ⟨rfl, h⟩
  · exact lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_of_lt (by simp [hl]) (by omega))
  · exact lex_cons_lt_cons (by simp [hl]) (lex_cons_lt_cons (by simp [hl])
      (lex_cons_lt_of_lt hl (by omega)))

/-- `add $-2` on a count `≥ 8` (the `Ld93 → Ld70` edge). -/
theorem lsub2_lt (w : BitVec 32) (h : 8 ≤ w.toInt) :
    (w + BitVec.setWidth 32 4294967294#64).toInt.toNat + 1 < w.toInt.toNat := by
  have e : BitVec.setWidth 32 4294967294#64 = -2#32 := by decide
  have := BitVec.toInt_lt (x := w)
  rw [e, BitVec.toInt_add, Int.bmod_def]
  have : (-2#32 : BitVec 32).toInt = -2 := by decide
  rw [this]
  split <;> omega

/-- `test %edx,%edx; jle` on a small nonnegative `rdx`. -/
theorem ltest_le_small (d : BitVec 64) (hd : d.toNat < 2 ^ 31) (a : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 32 d &&& BitVec.setWidth 32 d)
      { cf := false, af := a, of := false }) = decide (d.toNat = 0) := by
  have h1 : (BitVec.setWidth 32 d).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_setWidth, decide_eq_false_iff_not]; omega
  have h2 : ((BitVec.setWidth 32 d) == BitVec.zero 32) = decide (d.toNat = 0) := by
    have : (BitVec.setWidth 32 d = BitVec.zero 32) ↔ d.toNat = 0 := by
      have z : (BitVec.zero 32).toNat = 0 := rfl
      rw [← BitVec.toNat_inj, z, BitVec.toNat_setWidth]; omega
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, decide_eq_true_eq, this]
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.and_self, h1, h2]
  cases decide (d.toNat = 0) <;> rfl

/-- `lea (,%rdx,8),%eax` on a small `rdx`. -/
theorem ltoInt_x8 (d : BitVec 64) (hd : d.toNat < 271) :
    (BitVec.setWidth 32 (d * 8#64)).toInt = 8 * d.toNat := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `rd_off` for a 1-byte load (`buffer + (index >> 3)`). -/
theorem lrd_off1 (i p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat) (hL : p.toNat / 8 + 4 ≤ L) :
    ((i.ushiftRight 3).setWidth 64).toNat + 1 ≤ L := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `rd_off` for a 4-byte load. -/
theorem lrd_off4 (i p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat) (hL : p.toNat / 8 + 4 ≤ L) :
    ((i.ushiftRight 3).setWidth 64).toNat + 4 ≤ L := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

end Kraken.Examples.Sbr.Ps

/-- The normalisation of `vcgen`'s states (goal only). -/
macro "lsimp" : tactic => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
    AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
    Int64.toBitVec_ofNat_lit, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
    BitVec.setWidth_32_64_32, ite_true, ite_false])

namespace Kraken.Examples.Sbr.Ps

/-- `get_bits1`'s pending increment (`cmp; setl %sil`): the index plus it is at most
`size_in_bits_plus8`. -/
theorem setl_ix (x : PArgs) (r q : BitVec 64) (hr : Ix x r) (hp : x.p8.toNat < 2 ^ 31)
    (cf af : Bool) :
    r.toNat + (BitVec.setWidth 8 (q.replaceLow (BitVec.ofNat 8 (CondCode.l.interp
      (StatusFlags.from_result (BitVec.setWidth 32 r - x.p8)
        { cf := cf, af := af,
          of := (BitVec.setWidth 32 r - x.p8).signed != (BitVec.setWidth 32 r).signed - x.p8.signed
        })).toNat))).toNat ≤ x.p8.toNat := by
  rw [CondCode.interp_l_cmp_toInt32, BitVec.toNat_setWidth, BitVec.toNat_replaceLow8_mod]
  obtain ⟨h1, h2⟩ := hr
  have hr32 : (BitVec.setWidth 32 r).toNat = r.toNat := by
    rw [BitVec.toNat_setWidth]; omega
  have hlt : (BitVec.setWidth 32 r).toInt < x.p8.toInt ↔ r.toNat < x.p8.toNat := by
    rw [BitVec.toInt_eq_toNat_of_msb, BitVec.toInt_eq_toNat_of_msb]
    · omega
    · rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
    · rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not]; omega
  by_cases h : r.toNat < x.p8.toNat
  · have : decide ((BitVec.setWidth 32 r).toInt < x.p8.toInt) = true := by
      simp only [decide_eq_true_eq]; exact hlt.mpr h
    rw [this]; simp only [Bool.toNat_true, BitVec.toNat_ofNat]; omega
  · have : decide ((BitVec.setWidth 32 r).toInt < x.p8.toInt) = false := by
      simp only [decide_eq_false_iff_not]; exact fun h' => h (hlt.mp h')
    rw [this]; simp only [Bool.toNat_false, BitVec.toNat_ofNat]; omega

/-- A bit (`and $1`), zero-extended. -/
theorem and1_lt (v : BitVec 32) : (BitVec.setWidth 64 (v &&& BitVec.setWidth 32 1#64)).toNat < 2 := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_and]
  have h1 : (BitVec.setWidth 32 1#64).toNat = 1 := rfl
  rw [h1]
  have := Nat.and_le_right (n := v.toNat) (m := 1)
  omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `lea (%rcx,%rax,2),%ecx` with `rcx = iid_quant ∈ {0, 1}`, `rax = dt < 2`: the index into
`huff_iid` is `< 4`. -/
theorem lea_q2 (q : Int) (a : BitVec 64) (hq : q = 0 ∨ q = 1) (ha : a.toNat < 2) :
    (BitVec.setWidth 32 (BitVec.ofInt 64 q + a * 2#64)).toNat < 4 := by
  have h : a = 0#64 ∨ a = 1#64 := by
    rcases (show a.toNat = 0 ∨ a.toNat = 1 by omega) with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (BitVec.eq_of_toNat_eq h)
  rcases hq with rfl | rfl <;> rcases h with rfl | rfl <;> decide

/-- `cmp $4; jae` on a value `< 4`: not taken. -/
theorem nc_sub4 (v : BitVec 32) (hv : v.toNat < 4) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (v - BitVec.setWidth 32 4#64)
      { cf := (v - BitVec.setWidth 32 4#64).unsigned != v.unsigned - (BitVec.setWidth 32 4#64).unsigned,
        af := af, of := of }) = false := by
  have h : v = 0#32 ∨ v = 1#32 ∨ v = 2#32 ∨ v = 3#32 := by
    rcases (show v.toNat = 0 ∨ v.toNat = 1 ∨ v.toNat = 2 ∨ v.toNat = 3 by omega) with h | h | h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq h)
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
    · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
    · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h)))
  rcases h with rfl | rfl | rfl | rfl <;> rfl

end Kraken.Examples.Sbr.Ps

/-- Register reads of `set64` chains. -/
macro "rs" : tactic => `(tactic| simp only [Kraken.Examples.Sbr.Ps.Rdr, Kraken.Examples.Sbr.Ps.Ix,
  Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false])

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-- `huff_iid[j]`. -/
theorem Fr_huff {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 4) :
    m.loadInt (lab "huff_iid" + BitVec.ofNat 64 (4 * j)) 4
      = some (rd [2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] (4 * j) 4) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact lc_load (focus (eq_l (eq_r (eq_r (eq_r eq_h)))) hF) (4 * j) 4 (by simp; omega) (by simp)

theorem huff_lt (j : Nat) (hj : j < 4) :
    rd [2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] (4 * j) 4 < 4
    ∧ 0 ≤ rd [2, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0, 0] (4 * j) 4 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> decide

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `mov %ecx,%ecx; (…,%rcx,4)` on a small index. -/
theorem idx4_zx (r : BitVec 64) (h : r.toNat < 4) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 = BitVec.ofNat 64 (4 * r.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- `movl (…),%ecx; (…,%rcx,8)` on a loaded small `int`. -/
theorem idx8_ofInt (v : Int) (h0 : 0 ≤ v) (h : v < 4) :
    BitVec.setWidth 64 (BitVec.ofInt 32 v) * 8#64 = BitVec.ofNat 64 (8 * v.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- `mov %sil,%dl; add %edx,%r8d` with `rdx = 0`: the reader index stays in range. -/
theorem ix_addb (x : PArgs) (r q : BitVec 64) (hr : Ix x r)
    (h : r.toNat + (BitVec.setWidth 8 q).toNat ≤ x.p8.toNat) (hp : x.p8.toNat < 2 ^ 31) :
    Ix x (BitVec.setWidth 64 (BitVec.setWidth 32 ((0#64).replaceLow (BitVec.setWidth 8 q))
      + BitVec.setWidth 32 r)) := by
  have h1 := BitVec.toNat_replaceLow8_mod 0#64 (BitVec.setWidth 8 q)
  have h2 := BitVec.toNat_replaceLow8_div 0#64 (BitVec.setWidth 8 q)
  rw [BitVec.toNat_zero, Nat.zero_div] at h2
  have h3 := (BitVec.setWidth 8 q).isLt
  obtain ⟨ha, hb⟩ := hr
  constructor <;> simp only [BitVec.toNat_setWidth, BitVec.toNat_add] <;> omega

theorem add_i64z (a : BitVec 64) : a + Int64.toBitVec 0 = a := BitVec.add_zero a

/-- `test %r32,%r32; jle`: taken iff the signed value is `≤ 0`. -/
theorem le_test32 (v : BitVec 32) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (v &&& v) { cf := false, af := af, of := false })
      = decide (v.toInt ≤ 0) := by
  simp only [CondCode.interp_le, StatusFlags.zf_from_result, StatusFlags.sf_from_result,
    StatusFlags.of_from_result, BitVec.and_self]
  rw [BitVec.msb_eq_toInt]
  by_cases h : v = 0
  · subst h; decide
  · have h1 : v.toInt ≠ 0 := fun h' => h (BitVec.toInt_inj.mp (by rw [h']; rfl))
    by_cases h3 : v.toInt < 0
    · have : v.toInt ≤ 0 := by omega
      simp [h3, this]
    · have : ¬ v.toInt ≤ 0 := by omega
      simpa [h3, this] using h

/-- `movl` of a positive `int` read as a zero-extension. -/
theorem sx_pos (n : Int) (h0 : 0 < n) (h : n < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.ofInt 32 n) = BitVec.ofNat 64 n.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

/-- Closing row `e` of the `iid` table after `b ≥ nr_iid_par` bands. -/
theorem IidB_step (c : List UInt8) (e b : Nat) (h : IidB c e) (hr : IidR c e b)
    (hb : i32 c 12 ≤ b) (h4 : i32 c 4 ≠ 0) : IidB c (e + 1) := by
  intro e' he' b' hb' hor
  rcases Nat.lt_or_ge e' e with hl | hl
  · exact h e' (by omega) b' hb' hor
  · have : e' = e := by omega
    subst this
    rcases hor with h0 | h0
    · exact absurd h0 h4
    · exact hr b' (by omega)

theorem WI_step (c f : List UInt8) (e b : Nat) (h : WI c f e b) (hb : i32 c 12 ≤ b)
    (h4 : i32 c 4 ≠ 0) : WI c f (e + 1) 0 :=
  ⟨h.1, h.2.1, h.2.2.1, IidB_step c e b h.2.2.2.1 h.2.2.2.2 hb h4,
    fun _ h' => absurd h' (Nat.not_lt_zero _)⟩


/-- A 4-byte load of an 8-byte slot: the low half. -/
theorem rd48 (l : List UInt8) (o : Nat) :
    BitVec.ofInt 32 (rd l o 4) = BitVec.ofInt 32 (rd l o 8) := by
  simp only [rd]
  rw [BitVec.ofInt_ofBytes_take 32 4 rfl (List.take 8 _), List.take_take]
  rfl

theorem ofInt32_of_64 (a b : Int) (h : BitVec.ofInt 64 a = BitVec.ofInt 64 b) :
    BitVec.ofInt 32 a = BitVec.ofInt 32 b := by
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt] at h' ⊢
  omega

theorem z_small (e : Nat) (he : e ≤ 4) (a : Bool) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.ofNat 64 e &&& BitVec.ofNat 64 e)
      { cf := false, af := a, of := false }) = decide (e = 0) := by
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ofInt32_nn (n : Int) (h : 0 ≤ n) : BitVec.ofInt 32 n = BitVec.ofNat 32 n.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem zx3_ofNat (e : Nat) (he : e < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 e)))
      = BitVec.ofNat 32 e := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem row34 (a : BitVec 64) (ep : Nat) (h : ep ≤ 5) :
    a + 76#64 + (BitVec.ofNat 64 ep <<< 5 + BitVec.ofNat 64 ep * 2#64 + Int64.toBitVec 0)
      = a + BitVec.ofNat 64 (76 + 34 * ep) := by
  rw [add_i64z]
  rcases (show ep = 0 ∨ ep = 1 ∨ ep = 2 ∨ ep = 3 ∨ ep = 4 ∨ ep = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [BitVec.add_assoc]; rfl)

/-- `test %r8b,%r8b; jle` on a register holding `0 ≤ n ≤ 4`: taken iff `n = 0`. -/
theorem le8_nat (r : BitVec 64) (n : Nat) (h : r.toNat = n) (hn : n ≤ 4) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (BitVec.setWidth 8 r &&& BitVec.setWidth 8 r)
      { cf := false, af := af, of := false }) = decide (n = 0) := by
  have : r = BitVec.ofNat 64 n := BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)
  subst this
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- An 8-byte slot written with a small natural number reads back as it. -/
theorem rd_wr_nat (l : List UInt8) (o m : Nat) (h : o + 8 ≤ l.length) (hm : m < 2 ^ 63) :
    rd (wr l o 8 (BitVec.ofNat 64 m).toInt) o 8 = m := by
  rw [rd_wr_same l o 8 _ h, ofBytes_toBytes]
  have : (BitVec.ofNat 64 m).toInt = m := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  rw [this]
  simp only [Int.take]
  omega

/-- The byte offset `index >> 3` of a reader index is at most `plus8 / 8`. -/
theorem shr3_le (r : BitVec 64) (p : BitVec 32) (hi : r.toNat ≤ p.toNat) :
    (((BitVec.setWidth 32 r).ushiftRight 3).setWidth 64).toNat ≤ p.toNat / 8 := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth]
  have := p.isLt
  rw [Nat.mod_eq_of_lt (a := r.toNat) (by omega), Nat.shiftRight_eq_div_pow]
  have h2 : r.toNat / 2 ^ 3 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h2]
  omega

/-- `xor %ecx,%ecx; sete %cl; xor $5,%ecx` scaled by 8: table 4 on a zero bit, else 5. -/
theorem vidx (r : BitVec 64) (b : Bool) :
    BitVec.setWidth 64 (BitVec.setWidth 32 ((BitVec.setWidth 64 (BitVec.setWidth 32 r ^^^
      BitVec.setWidth 32 r)).replaceLow (BitVec.ofNat 8 b.toNat)) ^^^ BitVec.setWidth 32 (Int64.toBitVec 5))
      * 8#64 = if b then BitVec.ofNat 64 32 else BitVec.ofNat 64 40 := by
  rw [BitVec.xor_self]
  cases b <;> decide

/-- `shl $5; lea (,c,2); add base`: the row `246 + 34 ep`. -/
theorem row246 (a : BitVec 64) (ep : Nat) (h : ep ≤ 5) :
    a + 246#64 + (BitVec.ofNat 64 ep <<< 5 + BitVec.ofNat 64 ep * 2#64 + Int64.toBitVec 0)
      = a + BitVec.ofNat 64 (246 + 34 * ep) := by
  rw [add_i64z]
  rcases (show ep = 0 ∨ ep = 1 ∨ ep = 2 ∨ ep = 3 ∨ ep = 4 ∨ ep = 5 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> (simp only [BitVec.add_assoc]; rfl)

/-- `inc %r10; cmp %r10,%r11` on a band counter `b < n`: equal iff `b + 1 = n`. -/
theorem cnt_beq2 (n b : Nat) (hb : b < n) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n - (BitVec.ofNat 64 b + 1) == BitVec.zero 64) = decide (b + 1 = n) := by
  have key : (BitVec.ofNat 64 n - (BitVec.ofNat 64 b + 1) = BitVec.zero 64) ↔ (b + 1 = n) := by
    rw [← BitVec.toNat_inj]
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1' : (1 : BitVec 64).toNat = 1 := rfl
    show _ = 0 ↔ _
    omega
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact key

/-- The band measure `n - b` after `inc`. -/
theorem meas_b (n b : Nat) (hb : b < n) (hn : n < 2 ^ 63) :
    (BitVec.ofNat 64 n - (BitVec.ofNat 64 b + 1)).toNat < (BitVec.ofNat 64 n - BitVec.ofNat 64 b).toNat := by
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1' : (1 : BitVec 64).toNat = 1 := rfl
  omega

theorem shr23_lt (v : BitVec 32) : (v.ushiftRight 23).toNat < 512 := by
  rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := v.isLt; omega

theorem abs8_aux : ∀ n, n < 256 →
    (BitVec.setWidth 32 ((BitVec.ofNat 8 n ^^^ (BitVec.ofNat 8 n).sshiftRight 7)
      - (BitVec.ofNat 8 n).sshiftRight 7)).toInt = ((BitVec.ofNat 8 n).toInt.natAbs : Int) := by
  decide +kernel

/-- `sar $7; xor; sub; movzbl`: the absolute value of a byte. -/
theorem abs8 (y : BitVec 8) :
    (BitVec.setWidth 32 ((y ^^^ y.sshiftRight 7) - y.sshiftRight 7)).toInt = (y.toInt.natAbs : Int) := by
  have h := abs8_aux y.toNat y.isLt
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h

theorem sw8_64_32 (r : BitVec 64) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 r)) = BitVec.setWidth 8 r := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem sw32_64_32_8 (v : BitVec 8) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = BitVec.setWidth 32 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := v.isLt
  omega

theorem natAbs_le (v k : Int) (h : ¬ (k < (v.natAbs : Int))) : -k ≤ v ∧ v ≤ k := by
  rcases Int.le_total 0 v with h0 | h0
  · rw [Int.natAbs_of_nonneg h0] at h; omega
  · rw [Int.ofNat_natAbs_of_nonpos h0] at h; omega

theorem toInt_q (q : Int) (h : q = 0 ∨ q = 1) : (BitVec.ofInt 32 (7 + 8 * q)).toInt = 7 + 8 * q := by
  rcases h with rfl | rfl <;> rfl

end Kraken.Examples.Sbr.Ps
