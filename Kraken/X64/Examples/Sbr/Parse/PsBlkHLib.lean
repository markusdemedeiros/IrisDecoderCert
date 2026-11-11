import Kraken.X64.Examples.Sbr.Parse.PsFrame

/-!
# `ff_ps_read_data`, the header: lemmas for the blocks of `PsBlkH*`

* Loads from the reader `*gb_host` and from the constant tables, focused out of `Fr`.
* Values of loads and stores: `BitVec.ofInt` of the bytes of a bit vector.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

/-! ## Values -/

theorem rd_toBytes32 (b : BitVec 32) : Int.ofBytes (Int.toBytes 4 b.toInt) = b.toNat := by
  rw [ofBytes_toBytes]
  simp only [Int.take]
  rw [BitVec.toInt_eq_toNat_bmod]
  have := b.isLt
  simp only [Int.bmod]
  split <;> omega

theorem rd_toBytes64 (b : BitVec 64) : Int.ofBytes (Int.toBytes 8 b.toInt) = b.toNat := by
  rw [ofBytes_toBytes]
  simp only [Int.take]
  rw [BitVec.toInt_eq_toNat_bmod]
  have := b.isLt
  simp only [Int.bmod]
  split <;> omega

theorem ofInt_toBytes32 (b : BitVec 32) : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 b.toInt)) = b :=
  BitVec.ofInt_ofBytes_toBytes 32 4 rfl b

theorem ofInt_toBytes64 (b : BitVec 64) : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 b.toInt)) = b :=
  BitVec.ofInt_ofBytes_toBytes 64 8 rfl b

variable [CodeEnv]

/-! ## The reader -/

theorem Fr_gb_buf {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    m.loadInt (arg1 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
  simp only [Fr, PF, GbW] at h
  exact loadInt_sep _ _ 8 _ m (focus (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l eq_h))))))) h)
    (Int.toBytes_length 8 _) (by omega)

theorem Fr_gb_idx {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    m.loadInt (arg1 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) := by
  simp only [Fr, PF, GbW] at h
  exact loadInt_sep _ _ 4 _ m
    (focus (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r eq_h)))))))) h)
    (Int.toBytes_length 4 _) (by omega)

theorem Fr_gb_p8 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    m.loadInt (arg1 t₀ + 0x10#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  simp only [Fr, PF, GbW] at h
  exact loadInt_sep _ _ 4 _ m
    (focus (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r (eq_r
      (Std.ExtHashMap.sep_comm _ _)))))))))) h)
    (Int.toBytes_length 4 _) (by omega)

/-! ## The constant tables -/

theorem Fr_const {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    ∃ F, m =⋆ ConstW ⋆ F := by
  obtain ⟨F, hF⟩ := Fr_tabs h
  simp only [PsTabs] at hF
  exact ⟨_, focus (eq_l (eq_r (Std.ExtHashMap.sep_comm _ _))) hF⟩

theorem Fr_nenv {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 8) :
    m.loadInt (lab "num_env_tab" + BitVec.ofNat 64 j) 1
      = some (rd [0, 1, 2, 4, 1, 2, 3, 4] j 1) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact lc_load (focus (eq_l eq_h) hF) j 1 (by simp; omega) (by simp)

theorem Fr_iidicc {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 6) :
    m.loadInt (lab "nr_iidicc_par_tab" + BitVec.ofNat 64 j) 1
      = some (rd [10, 20, 34, 10, 20, 34] j 1) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact lc_load (focus (eq_l (eq_r eq_h)) hF) j 1 (by simp; omega) (by simp)

theorem Fr_iidopd {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 6) :
    m.loadInt (lab "nr_iidopd_par_tab" + BitVec.ofNat 64 j) 1
      = some (rd [5, 11, 17, 5, 11, 17] j 1) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact lc_load (focus (eq_l (eq_r (eq_r eq_h))) hF) j 1 (by simp; omega) (by simp)

theorem Fr_log2got {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i) :
    m.loadInt (lab "ff_log2_tab_got") 8
      = some (Int.ofBytes (Int.toBytes 8 (lab "ff_log2_tab").toInt)) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact loadInt_sep _ _ 8 _ m (focus (eq_l (eq_r (eq_r (eq_r (eq_r eq_h))))) hF)
    (Int.toBytes_length 8 _) (by omega)

theorem Fr_log2 {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (j : Nat) (hj : j < 6) :
    m.loadInt (lab "ff_log2_tab" + BitVec.ofNat 64 j) 1 = some (rd [0, 0, 1, 1, 2, 2] j 1) := by
  obtain ⟨F, hF⟩ := Fr_const h
  simp only [ConstW] at hF
  exact lc_load (focus (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r eq_h)))))) hF) j 1
    (by simp; omega) (by simp)

/-- A local slot's address: `rbp - d` (`rbp = rsp0 - 8`) as an offset into the locals block. -/
theorem fr_addr (t : BitVec 64) (d : Nat) (h1 : 8 < d) (h2 : d ≤ 0xa0) :
    t - 8#64 + BitVec.ofNat 64 (2 ^ 64 - d) = t - 0xa8#64 + BitVec.ofNat 64 (0xa0 - d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A register read through a conditional register file (a shift by a count that may be 0). -/
theorem get64_ite (c : Prop) [Decidable c] (A B : Reg64s) (r : Reg64) :
    (if c then A else B).get64 r = if c then A.get64 r else B.get64 r := by
  split <;> rfl

/-- A local slot can be loaded (the side condition of a store). -/
theorem Fr_f_isSome {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hf : f.length = 0x78) (o n : Nat) (hin : o + n ≤ 0x78) :
    (m.loadInt (rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 o) n).isSome = true := by
  rw [Fr_f_load h hf o n hin]; rfl

theorem toNat_ushiftRight_div {w : Nat} (v : BitVec w) (n : Nat) :
    (v.ushiftRight n).toNat = v.toNat / 2 ^ n := by
  show (v >>> n).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem wr_take_lo (c : List UInt8) (o n j : Nat) (v : Int) (h : j ≤ o) (hl : o ≤ c.length) :
    (wr c o n v).take j = c.take j := by
  rw [wr, List.append_assoc, List.take_append_of_le_length (by simp; omega), List.take_take]
  congr 1; omega

theorem wr_drop_hi (c : List UInt8) (o n j : Nat) (v : Int) (h : o + n ≤ j) (hl : o + n ≤ c.length) :
    (wr c o n v).drop j = c.drop j := by
  have h1 : (c.take o ++ Int.toBytes n v).length = o + n := by
    simp [Int.toBytes_length]; omega
  have e : j = (c.take o ++ Int.toBytes n v).length + (j - (o + n)) := by omega
  rw [wr]
  conv => lhs; rw [e, List.drop_append, List.drop_drop]
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append]; congr 1; omega

/-- A header write (`[o, o+n) ⊆ [4, 0x4c)`) keeps `*ps` outside the header fields. -/
theorem Kp_wr {x : PArgs} {c : List UInt8} (h : Kp x c) (o n : Nat) (v : Int)
    (h1 : 4 ≤ o) (h2 : o + n ≤ 0x4c) (hl : 0x4c ≤ c.length) : Kp x (wr c o n v) :=
  ⟨(wr_take_lo c o n 4 v h1 (by omega)).trans h.1, (wr_drop_hi c o n 0x4c v h2 (by omega)).trans h.2⟩

/-- A write of `enable_iid`/`iid_mode`-free fields keeps `PsInv`. -/
theorem PsInv_wr4 {c : List UInt8} (h : PsInv c) (v : Int) : PsInv (wr c 4 4 v) := by
  obtain ⟨hl, h12, h16, h28, h40, h44, h8⟩ := h
  have hw := fun o' (hd : o' + 4 ≤ 4 ∨ 4 + 4 ≤ o') => i32_wr c 4 4 o' v (by omega) hd
  refine ⟨by rw [wr_length _ _ _ _ (by omega), hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 12 (by omega)]; exact h12
  · rw [hw 16 (by omega)]; exact h16
  · rw [hw 28 (by omega)]; exact h28
  · rw [hw 40 (by omega)]; exact h40
  · rw [hw 44 (by omega)]; exact h44
  · rw [hw 8 (by omega)]; exact h8

theorem int_ofBytes_natH (bs : List UInt8) : Int.ofBytes bs = ((Nat.ofBytes bs : Nat) : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Int.ofBytes bs * 256 + ((b.toNat : Nat) : Int) = ((Nat.ofBytes bs * 256 + b.toNat : Nat) : Int)
    rw [ih]; omega

/-- A 4-byte field written from a bit vector reads back as its signed value. -/
theorem i32_wr_same (c : List UInt8) (o : Nat) (b : BitVec 32) (h : o + 4 ≤ c.length) :
    i32 (wr c o 4 b.toInt) o = b.toInt := by
  simp only [i32]
  rw [wr_drop_take_same _ _ _ _ h, ← BitVec.ofInt_natCast, ← int_ofBytes_natH, ofInt_toBytes32]

/-- A field of `*ps` can be loaded (the side condition of a store). -/
theorem Fr_c_isSome {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hc : c.length = 764) (o n : Nat) (hin : o + n ≤ 764) :
    (m.loadInt (arg2 t₀ + BitVec.ofNat 64 o) n).isSome = true := by
  rw [Fr_c_load h hc o n hin]; rfl

/-! ## Havoc rules (from `GridLib`): `bswap`, `shl %cl` with the value forgotten -/

section Havoc

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

omit [CodeEnv] in
theorem ps_regs_set_get (rs : Reg64s) (r : Reg64) : rs.set64 r (rs.get64 r) = rs := by
  cases rs; cases r <;> rfl

/-- `bswap %r32`, value forgotten. -/
theorem ps_bswap32_havoc (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.bswap (.low r .W32))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Directive.interp, Instr.interp, Operation.interp,
      MachineData.setReg, Reg64s.set_low32, Effects.All]
    exact h _ s.status _ hpl'

/-- `shl %cl, %r32`, value forgotten. -/
theorem ps_shl_cl32_havoc (asz : Width) (r : Reg64) :
    ⦃ fun s => ∀ v : BitVec 64, ∀ st : StatusFlags,
        WP.wp p Q E { s with regs := s.regs.set64 r v, status := st } ⦄
      (Directive.instr (.regular asz .W32 (.shl (.reg (.low r .W32)) .cl)) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (MachineWP.shl_reg_cl_w32_spec (p := p) (Q := Q) (E := E) asz r).le_wp s
    (fun cf af of => by
      split
      · have h := hs (s.regs.get64 r) s.status
        rw [ps_regs_set_get] at h; exact h
      · exact hs _ _)

end Havoc

/-- The flags of `cmp $k, %eax` for a field value `A < 8` (all eight cases decided). -/
abbrev cmpSt (A : BitVec 32) (k : Nat) : StatusFlags :=
  StatusFlags.from_result (A - BitVec.setWidth 32 (BitVec.ofNat 64 k))
    { cf := (A - BitVec.setWidth 32 (BitVec.ofNat 64 k)).unsigned !=
        A.unsigned - (BitVec.setWidth 32 (BitVec.ofNat 64 k)).unsigned,
      af := ((A - BitVec.setWidth 32 (BitVec.ofNat 64 k)).take 4).unsigned !=
        (A.take 4).unsigned - ((BitVec.setWidth 32 (BitVec.ofNat 64 k)).take 4).unsigned,
      of := (A - BitVec.setWidth 32 (BitVec.ofNat 64 k)).signed !=
        A.signed - (BitVec.setWidth 32 (BitVec.ofNat 64 k)).signed }

omit [CodeEnv] in
theorem small8 (A : BitVec 32) (hA : A.toNat < 8) : ∃ m, m < 8 ∧ A = BitVec.ofNat 32 m :=
  ⟨A.toNat, hA, BitVec.eq_of_toNat_eq (by simp)⟩

/-- `cmp $5; jle` on a 3-bit field: taken means `≤ 5`, with `cf ∨ zf` for the `ja` after it. -/
theorem jle5 (A : BitVec 32) (hA : A.toNat < 8) (h : CondCode.le.interp (cmpSt A 5) = true) :
    A.toNat ≤ 5 ∧ ((cmpSt A 5).cf = true ∨ (cmpSt A 5).zf = true) := by
  obtain ⟨m, hm, rfl⟩ := small8 A hA
  revert h
  match m, hm with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide

theorem shr29_lt (v : BitVec 32) : (v.ushiftRight 29).toNat < 8 := by
  rw [toNat_ushiftRight_div]; have := v.isLt; omega

omit [CodeEnv] in
/-- On the error path `Rng0` comes from the input (`*ps` past the header fields, `PsInv`). -/
theorem Rng0_of_Kp {x : PArgs} {c : List UInt8} (hP : PsInv c) (hK : Kp x c) (hw : PsWFb x.c) :
    Rng0 c := by
  refine ⟨?_, hP.2.2.2.2.2.2⟩
  have e : i32 c 756 = i32 x.c 756 := by
    have h2 : c.drop 756 = x.c.drop 756 := by
      rw [show (756 : Nat) = 0x4c + 680 from rfl, ← List.drop_drop, hK.2, List.drop_drop]
    simp only [i32, h2]
  rw [e]; exact hw.2.1

omit [CodeEnv] in
/-- `index' = min(index + d, plus8)` (`add $d; cmp; cmovb`), as `vcgen` leaves it: a reader
index again, at least the old one. -/
theorem ix_clampH (x : PArgs) (r d : BitVec 64) (hd : (BitVec.setWidth 32 d).toNat ≤ 256) (hr : Ix x r)
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

omit [CodeEnv] in
/-- `nr_iidicc_par_tab[j]` sign-extended. -/
theorem iidicc_val (j : Nat) (hj : j < 6) :
    (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [10, 20, 34, 10, 20, 34] j 1))).toInt = 10
    ∨ (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [10, 20, 34, 10, 20, 34] j 1))).toInt = 20
    ∨ (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [10, 20, 34, 10, 20, 34] j 1))).toInt = 34 := by
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide

omit [CodeEnv] in
/-- `nr_iidopd_par_tab[j]` sign-extended. -/
theorem iidopd_val (j : Nat) (hj : j < 6) :
    (BitVec.signExtend 32 (BitVec.ofInt 8 (rd [5, 11, 17, 5, 11, 17] j 1))).toInt ≤ 34 := by
  match j, hj with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide

/-- A write of one of the fields `PsInv` bounds, with a value within the bound. -/
theorem PsInv_wr_field {c : List UInt8} (h : PsInv c) (o : Nat) (W : BitVec 32)
    (ho : o = 4 ∨ o = 8 ∨ o = 12 ∨ o = 16 ∨ o = 20 ∨ o = 24 ∨ o = 28 ∨ o = 32 ∨ o = 36)
    (h8 : o = 8 → W.toInt = 0 ∨ W.toInt = 1)
    (h12 : o = 12 ∨ o = 16 ∨ o = 28 → W.toInt ≤ 34) :
    PsInv (wr c o 4 W.toInt) := by
  obtain ⟨hl, e12, e16, e28, e40, e44, e8⟩ := h
  have hw : ∀ o', o' = 8 ∨ o' = 12 ∨ o' = 16 ∨ o' = 28 ∨ o' = 40 ∨ o' = 44 → o' ≠ o →
      i32 (wr c o 4 W.toInt) o' = i32 c o' := fun o' h1 h2 =>
    i32_wr c o 4 o' _ (by omega) (by omega)
  have hs : i32 (wr c o 4 W.toInt) o = W.toInt := i32_wr_same c o W (by omega)
  refine ⟨by rw [wr_length _ _ _ _ (by omega), hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases e : o = 12
    · subst e; rw [hs]; exact h12 (by omega)
    · rw [hw 12 (by omega) (Ne.symm e)]; exact e12
  · by_cases e : o = 16
    · subst e; rw [hs]; exact h12 (by omega)
    · rw [hw 16 (by omega) (Ne.symm e)]; exact e16
  · by_cases e : o = 28
    · subst e; rw [hs]; exact h12 (by omega)
    · rw [hw 28 (by omega) (Ne.symm e)]; exact e28
  · rw [hw 40 (by omega) (by omega)]; exact e40
  · rw [hw 44 (by omega) (by omega)]; exact e44
  · by_cases e : o = 8
    · subst e; rw [hs]; exact h8 rfl
    · rw [hw 8 (by omega) (Ne.symm e)]; exact e8

/-- The index after a one-bit read (`xor eax; cmp p8, i; setl al; add i, eax`): `i + 1` when
`i < p8` (signed), else `i`; so it stays in `[lo, p8]`. -/
theorem ix_bit1 (lo i p8 : BitVec 32) (a : BitVec 64) (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((i - p8).signed != i.signed - p8.signed))
    (hlo : lo.toNat ≤ i.toNat) (hi : i.toNat ≤ p8.toNat) (hp : p8.toNat < 2 ^ 31) :
    lo.toNat ≤ (BitVec.setWidth 64 (i + BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 a ^^^ BitVec.setWidth 32 a)).replaceLow
          (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (i - p8) f)).toNat)))).toNat
    ∧ (BitVec.setWidth 64 (i + BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 a ^^^ BitVec.setWidth 32 a)).replaceLow
          (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (i - p8) f)).toNat)))).toNat
      ≤ p8.toNat := by
  rw [CondCode.interp_l_sub32 _ _ _ hf, BitVec.xor_self]
  have hit : i.toInt = i.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  have hpt : p8.toInt = p8.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  by_cases h : i.toNat < p8.toNat
  · have : decide (i.toInt < p8.toInt) = true := by simp only [hit, hpt]; simp; omega
    rw [this, show (BitVec.setWidth 64 (0#32)).replaceLow (BitVec.ofNat 8 true.toNat) = 1#64
      from by decide]
    constructor <;> bv_omega
  · have : decide (i.toInt < p8.toInt) = false := by simp only [hit, hpt]; simp; omega
    rw [this, show (BitVec.setWidth 64 (0#32)).replaceLow (BitVec.ofNat 8 false.toNat) = 0#64
      from by decide]
    constructor <;> bv_omega

end Kraken.Examples.Sbr.Ps

/-- The normal form of addresses and register reads after `vcgen` (block proofs of `PsBlkH*`). -/
syntax "pnorm" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| pnorm $[$loc]?) => `(tactic| simp only [Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub, BitVec.toNat_ofNat, reduceIte, Kraken.Examples.Sbr.Ps.rsp0, Kraken.Examples.Sbr.arg0,
      Kraken.Examples.Sbr.arg1, Kraken.Examples.Sbr.arg2, Kraken.Examples.Sbr.arg3] $[$loc]?)

namespace Kraken.Examples.Sbr.Ps

/-- `xor r,r; setcc r8b`: the 32-bit value is `0` or `1`. -/
theorem setb_toInt (y : BitVec 32) (b : Bool) :
    (BitVec.setWidth 32 ((BitVec.setWidth 64 (y ^^^ y)).replaceLow (BitVec.ofNat 8 b.toNat))).toInt = 0
    ∨ (BitVec.setWidth 32 ((BitVec.setWidth 64 (y ^^^ y)).replaceLow
        (BitVec.ofNat 8 b.toNat))).toInt = 1 := by
  rw [BitVec.xor_self]; cases b <;> decide

/-- A write past `iid_mode` keeps `IidH`. -/
theorem IidH_wr {c : List UInt8} (h : IidH c) (o : Nat) (v : Int) (ho : 16 ≤ o)
    (hl : o + 4 ≤ c.length) : IidH (wr c o 4 v) := by
  unfold IidH at *
  rw [i32_wr c o 4 4 v hl (by omega), i32_wr c o 4 12 v hl (by omega)]; exact h

/-- `cmp $6; jl` on a 3-bit field: taken means `< 6`, with `cf` for the `jae` after it. -/
theorem jl6 (A : BitVec 32) (hA : A.toNat < 8) (h : CondCode.l.interp (cmpSt A 6) = true) :
    A.toNat < 6 ∧ (cmpSt A 6).cf = true := by
  obtain ⟨m, hm, rfl⟩ := small8 A hA
  revert h
  match m, hm with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `xor edi; cmp p8, eax; setl dil; lea (rax, rdi), edx`: `rdi ∈ {0, 1}`, `edx = eax + rdi`,
and `edx ≤ p8`. -/
theorem ix_lea1 (a y : BitVec 64) (p8 : BitVec 32) (f : StatusFlags.from_result.Remaining)
    (hf : f.of = ((BitVec.setWidth 32 a - p8).signed != (BitVec.setWidth 32 a).signed - p8.signed))
    (ha : a.toNat ≤ p8.toNat) (hp : p8.toNat < 2 ^ 31) :
    ((BitVec.setWidth 64 (BitVec.setWidth 32 y ^^^ BitVec.setWidth 32 y)).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp
          (StatusFlags.from_result (BitVec.setWidth 32 a - p8) f)).toNat)).toNat ≤ 1
    ∧ (BitVec.setWidth 64 (BitVec.setWidth 32 (a +
        (BitVec.setWidth 64 (BitVec.setWidth 32 y ^^^ BitVec.setWidth 32 y)).replaceLow
          (BitVec.ofNat 8 (CondCode.l.interp
            (StatusFlags.from_result (BitVec.setWidth 32 a - p8) f)).toNat)))).toNat
      = a.toNat + ((BitVec.setWidth 64 (BitVec.setWidth 32 y ^^^ BitVec.setWidth 32 y)).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp
          (StatusFlags.from_result (BitVec.setWidth 32 a - p8) f)).toNat)).toNat
    ∧ (BitVec.setWidth 64 (BitVec.setWidth 32 (a +
        (BitVec.setWidth 64 (BitVec.setWidth 32 y ^^^ BitVec.setWidth 32 y)).replaceLow
          (BitVec.ofNat 8 (CondCode.l.interp
            (StatusFlags.from_result (BitVec.setWidth 32 a - p8) f)).toNat)))).toNat
      ≤ p8.toNat
    ∧ a.toNat ≤ (BitVec.setWidth 64 (BitVec.setWidth 32 (a +
        (BitVec.setWidth 64 (BitVec.setWidth 32 y ^^^ BitVec.setWidth 32 y)).replaceLow
          (BitVec.ofNat 8 (CondCode.l.interp
            (StatusFlags.from_result (BitVec.setWidth 32 a - p8) f)).toNat)))).toNat := by
  rw [CondCode.interp_l_sub32 _ _ _ hf, BitVec.xor_self]
  have hat : (BitVec.setWidth 32 a).toNat = a.toNat := by
    rw [BitVec.toNat_setWidth]; omega
  have hit : (BitVec.setWidth 32 a).toInt = a.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt, hat]; omega
  have hpt : p8.toInt = p8.toNat := by
    rw [BitVec.toInt_eq_toNat_of_lt]; omega
  by_cases h : a.toNat < p8.toNat
  · have : decide ((BitVec.setWidth 32 a).toInt < p8.toInt) = true := by
      simp only [hit, hpt]; simp; omega
    rw [this, show (BitVec.setWidth 64 (0#32)).replaceLow (BitVec.ofNat 8 true.toNat) = 1#64
      from by decide]
    refine ⟨by decide, ?_, ?_, ?_⟩ <;> bv_omega
  · have : decide ((BitVec.setWidth 32 a).toInt < p8.toInt) = false := by
      simp only [hit, hpt]; simp; omega
    rw [this, show (BitVec.setWidth 64 (0#32)).replaceLow (BitVec.ofNat 8 false.toNat) = 0#64
      from by decide]
    refine ⟨by decide, ?_, ?_, ?_⟩ <;> bv_omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv] in
/-- A write past the header fields keeps `HdrOk`. -/
theorem HdrOk_wr {x : PArgs} {c f : List UInt8} (h : HdrOk x c f) (o : Nat) (v : Int)
    (ho : 0x24 ≤ o) (hl : o + 4 ≤ c.length) : HdrOk x (wr c o 4 v) f := by
  refine ⟨fun h0 => ?_, fun h0 => IidH_wr (h.2 h0) o v (by omega) hl⟩
  have e := congrArg (List.drop 4) (wr_take_lo c o 4 0x24 v ho (by omega))
  simp only [List.drop_take] at e
  exact e.trans (h.1 h0)

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- A one-bit field (`and $1`) zero-extended. -/
theorem and1_le (v : BitVec 32) : (BitVec.setWidth 64 (v &&& BitVec.setWidth 32 1#64)).toNat ≤ 1 := by
  rw [show BitVec.setWidth 32 1#64 = 1#32 from rfl, BitVec.toNat_setWidth, BitVec.toNat_and]
  have := Nat.and_le_right (n := v.toNat) (m := (1#32).toNat)
  have h1 : (1#32).toNat = 1 := rfl
  have := v.isLt
  omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-- `num_env_old := num_env` keeps `PsInv`. -/
theorem PsInv_wr40 {c : List UInt8} (h : PsInv c) (W : BitVec 32) (h0 : 0 ≤ W.toInt)
    (h5 : W.toInt ≤ 5) : PsInv (wr c 40 4 W.toInt) := by
  obtain ⟨hl, e12, e16, e28, e40, e44, e8⟩ := h
  have hw : ∀ o', o' = 8 ∨ o' = 12 ∨ o' = 16 ∨ o' = 28 ∨ o' = 44 →
      i32 (wr c 40 4 W.toInt) o' = i32 c o' := fun o' h1 =>
    i32_wr c 40 4 o' _ (by omega) (by omega)
  have hs : i32 (wr c 40 4 W.toInt) 40 = W.toInt := i32_wr_same c 40 W (by omega)
  refine ⟨by rw [wr_length _ _ _ _ (by omega), hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw 12 (by omega)]; exact e12
  · rw [hw 16 (by omega)]; exact e16
  · rw [hw 28 (by omega)]; exact e28
  · rw [hs]; exact ⟨h0, h5⟩
  · rw [hw 44 (by omega)]; exact e44
  · rw [hw 8 (by omega)]; exact e8

/-- The 32-bit load of `num_env` as an `i32` field. -/
theorem ofInt_rd_i32 (c : List UInt8) (o : Nat) :
    (BitVec.ofInt 32 (rd c o 4)).toInt = i32 c o := by
  simp only [rd, i32, int_ofBytes_natH, BitVec.ofInt_natCast]

/-- A non-negative 32-bit value stored zero-extended in a 64-bit slot (`S38`). -/
theorem s38_lem (W : BitVec 32) (h : 0 ≤ W.toInt) :
    BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (BitVec.setWidth 64 W).toInt))
      = BitVec.ofInt 64 W.toInt := by
  rw [rd_toBytes64, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans W.isLt (by decide))]
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split
  · rfl
  · rename_i hc; simp only [hc, if_false] at h; have := W.isLt; omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv] in
/-- A two-bit field (`shr $30`) zero-extended. -/
theorem shr30_lt64 (v : BitVec 32) : (BitVec.setWidth 64 (v.ushiftRight 30)).toNat < 4 := by
  rw [BitVec.toNat_setWidth, toNat_ushiftRight_div]; have := v.isLt; omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv] in
/-- `cmp $4; jae` on a two-bit field is not taken. -/
theorem nc_cmp4 (A : BitVec 32) (hA : A.toNat < 4) : CondCode.nc.interp (cmpSt A 4) = false := by
  obtain ⟨m, hm, rfl⟩ := small8 A (by omega)
  match m, hm with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => simp at hA
  | 5, _ => simp at hA
  | 6, _ => simp at hA
  | 7, _ => simp at hA

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

open scoped Kraken.Rules.GenericMem.Norm

/-- The prologue pushes: the first four slots can be loaded. -/
theorem push6_a {m : Mem 64} {f : List UInt8} {t : BitVec 64} {R : Mem 64 → Prop}
    (a b c d e g : Int)
    (h : (f =@ (t - 168#64) ⋆ ((8 ?@ (t - 8#64) ⋆ (8 ?@ (t - 16#64) ⋆ (8 ?@ (t - 24#64)
      ⋆ (8 ?@ (t - 32#64) ⋆ (8 ?@ (t - 40#64) ⋆ 8 ?@ (t - 48#64)))))) ⋆ R)) m) :
    (m.loadInt (t - 8#64) 8).isSome = true ∧ ((m.storeInt (t - 8#64) 8 a).loadInt (t - 16#64) 8).isSome = true ∧ (((m.storeInt (t - 8#64) 8 a).storeInt (t - 16#64) 8 b).loadInt (t - 24#64) 8).isSome = true ∧ ((((m.storeInt (t - 8#64) 8 a).storeInt (t - 16#64) 8 b).storeInt (t - 24#64) 8 c).loadInt
        (t - 32#64) 8).isSome = true := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals cells_grind

/-- The prologue pushes: the last two slots can be loaded. -/
theorem push6_b {m : Mem 64} {f : List UInt8} {t : BitVec 64} {R : Mem 64 → Prop}
    (a b c d e g : Int)
    (h : (f =@ (t - 168#64) ⋆ ((8 ?@ (t - 8#64) ⋆ (8 ?@ (t - 16#64) ⋆ (8 ?@ (t - 24#64)
      ⋆ (8 ?@ (t - 32#64) ⋆ (8 ?@ (t - 40#64) ⋆ 8 ?@ (t - 48#64)))))) ⋆ R)) m) :
    (((((m.storeInt (t - 8#64) 8 a).storeInt (t - 16#64) 8 b).storeInt (t - 24#64) 8 c).storeInt
        (t - 32#64) 8 d).loadInt (t - 40#64) 8).isSome = true ∧ ((((((m.storeInt (t - 8#64) 8 a).storeInt (t - 16#64) 8 b).storeInt (t - 24#64) 8 c).storeInt
        (t - 32#64) 8 d).storeInt (t - 40#64) 8 e).loadInt (t - 48#64) 8).isSome = true := by
  refine ⟨?_, ?_⟩
  all_goals cells_grind

/-- The prologue pushes: the six saved registers in their slots. -/
theorem push6_m {m : Mem 64} {f : List UInt8} {t : BitVec 64} {R : Mem 64 → Prop}
    (a b c d e g : Int)
    (h : (f =@ (t - 168#64) ⋆ ((8 ?@ (t - 8#64) ⋆ (8 ?@ (t - 16#64) ⋆ (8 ?@ (t - 24#64)
      ⋆ (8 ?@ (t - 32#64) ⋆ (8 ?@ (t - 40#64) ⋆ 8 ?@ (t - 48#64)))))) ⋆ R)) m) :
    (f =@ (t - 168#64) ⋆ ((Int.toBytes 8 a =@ (t - 8#64) ⋆ (Int.toBytes 8 b =@ (t - 16#64)
        ⋆ (Int.toBytes 8 c =@ (t - 24#64) ⋆ (Int.toBytes 8 d =@ (t - 32#64)
        ⋆ (Int.toBytes 8 e =@ (t - 40#64) ⋆ Int.toBytes 8 g =@ (t - 48#64)))))) ⋆ R))
      ((((((m.storeInt (t - 8#64) 8 a).storeInt (t - 16#64) 8 b).storeInt (t - 24#64) 8 c).storeInt
        (t - 32#64) 8 d).storeInt (t - 40#64) 8 e).storeInt (t - 48#64) 8 g) := by
  refine ?_
  all_goals cells_grind

end Kraken.Examples.Sbr.Ps
