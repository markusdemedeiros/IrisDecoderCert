import Kraken.X64.Examples.Sbr.Parse.DtdfSpec

/-!
# `read_sbr_dtdf`: the block table

Six copies of the `get_bits1_vector` loop (env/noise × {USAC with `indep_flag`, USAC without,
not USAC}); each two-element loop body is cut in two halves. The values between blocks are a
`DSt` (the flag bytes and the reader's index); the loop registers are stated as numbers:
`cnt` the element count, `j` the even loop index, `r8 = cnt / 2 * 2`.

With `bs_num_noise ≤ 2` the noise loop of the USAC `indep_flag` path (count
`bs_num_noise - 1 ≤ 1`) never runs its two-element body: those entries are `False`.

The variant decreases along each loop's back edge (`40 - j` in the env loops, `20 - j` in the
noise loops) and never increases from one loop to the next; it is `1` on the way out (the
`jmp` to `done` goes backwards in the label order) and `0` at `done`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Dtdf

variable [CodeEnv]

/-- The memory at every label, with the reader index `i`. -/
abbrev T (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) (i : BitVec 32) :
    Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve k (t₀.regs.get64 .rsp) ⋆ (DtdfF x t₀ i ⋆ x.R))

/-- The registers kept everywhere. -/
abbrev R0 (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
  ∧ SavedRegs t₀ s ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀

abbrev Base (k : Nat) (x : DArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  DtdfC x ∧ R0 t₀ s ∧ ∃ i : BitVec 32, i.toNat ≤ x.p8.toNat ∧ (s.dmem =⋆ T k x ra t₀ i)

/-- Inside a two-element loop body over `cnt` elements, at the even index `j`. -/
abbrev Lp (cnt : Nat) (s : MachineData) : Prop :=
  ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 j ∧ j % 2 = 0 ∧ j + 2 ≤ cnt / 2 * 2
    ∧ s.regs.get64 .rdi = BitVec.ofNat 64 cnt ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (cnt / 2 * 2)

/-- At the last element `j < cnt`. -/
abbrev Tl (cnt : Nat) (s : MachineData) : Prop :=
  ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 j ∧ j < cnt

abbrev table (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "read_sbr_dtdf", s => s = t₀ ∧ DtdfC x ∧ (t₀.dmem =⋆ T k x ra t₀ x.idx)
  | "read_sbr_dtdf.L5185", s => Base k x ra t₀ s
  | "read_sbr_dtdf.L51a2", s => Base k x ra t₀ s
  | "read_sbr_dtdf.L51bf", s => Base k x ra t₀ s ∧ 3 ≤ x.v.nenv
      ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.v.nenv - 1)
  | "read_sbr_dtdf.L51d0", s => Base k x ra t₀ s ∧ Lp (x.v.nenv - 1) s
  | "read_sbr_dtdf.L5202", s => Base k x ra t₀ s ∧ Lp (x.v.nenv - 1) s
  | "read_sbr_dtdf.L5243", s => Base k x ra t₀ s ∧ Tl (x.v.nenv - 1) s
  | "read_sbr_dtdf.L5272", s => Base k x ra t₀ s
  | "read_sbr_dtdf.L528f", _ => False
  | "read_sbr_dtdf.L52a0", _ => False
  | "read_sbr_dtdf.L52d2", _ => False
  | "read_sbr_dtdf.L5317", s => Base k x ra t₀ s ∧ Tl (x.v.nnoise - 1) s
  | "read_sbr_dtdf.done", s => Base k x ra t₀ s
  | "read_sbr_dtdf.L5347", s => Base k x ra t₀ s ∧ 2 ≤ x.v.nenv
      ∧ s.regs.get64 .rdi = BitVec.ofNat 64 x.v.nenv
  | "read_sbr_dtdf.L5360", s => Base k x ra t₀ s ∧ Lp x.v.nenv s
  | "read_sbr_dtdf.L5392", s => Base k x ra t₀ s ∧ Lp x.v.nenv s
  | "read_sbr_dtdf.L53d3", s => Base k x ra t₀ s ∧ Tl x.v.nenv s
  | "read_sbr_dtdf.L5402", s => Base k x ra t₀ s
  | "read_sbr_dtdf.L5430", s => Base k x ra t₀ s ∧ Lp x.v.nnoise s
  | "read_sbr_dtdf.L5462", s => Base k x ra t₀ s ∧ Lp x.v.nnoise s
  | "read_sbr_dtdf.L54a2", s => Base k x ra t₀ s ∧ 2 ≤ x.v.nenv
      ∧ s.regs.get64 .rdi = BitVec.ofNat 64 x.v.nenv
  | "read_sbr_dtdf.L54b0", s => Base k x ra t₀ s ∧ Lp x.v.nenv s
  | "read_sbr_dtdf.L54e2", s => Base k x ra t₀ s ∧ Lp x.v.nenv s
  | "read_sbr_dtdf.L5523", s => Base k x ra t₀ s ∧ Tl x.v.nenv s
  | "read_sbr_dtdf.L5552", s => Base k x ra t₀ s
  | "read_sbr_dtdf.L5564", s => Base k x ra t₀ s ∧ x.v.nnoise = 1
  | "read_sbr_dtdf.L556b", s => Base k x ra t₀ s ∧ 2 ≤ x.v.nnoise
      ∧ s.regs.get64 .rdi = BitVec.ofNat 64 x.v.nnoise
  | "read_sbr_dtdf.L5580", s => Base k x ra t₀ s ∧ Lp x.v.nnoise s
  | "read_sbr_dtdf.L55b2", s => Base k x ra t₀ s ∧ Lp x.v.nnoise s
  | "read_sbr_dtdf.L55ed", s => Base k x ra t₀ s
      ∧ s.regs.get64 .rdi = BitVec.ofNat 64 x.v.nnoise
      ∧ s.regs.get64 .rax = BitVec.ofNat 64 (x.v.nnoise / 2 * 2)
  | "read_sbr_dtdf.L55f3", s => Base k x ra t₀ s ∧ Tl x.v.nnoise s
  | "read_sbr_dtdf.L5622", s => Base k x ra t₀ s
  | _, _ => False

abbrev var : Label → MachineData → Nat
  | "read_sbr_dtdf", _ => 40
  | "read_sbr_dtdf.L5185", _ => 40
  | "read_sbr_dtdf.L51a2", _ => 40
  | "read_sbr_dtdf.L51bf", _ => 40
  | "read_sbr_dtdf.L5347", _ => 40
  | "read_sbr_dtdf.L54a2", _ => 40
  | "read_sbr_dtdf.L51d0", s => 40 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5202", s => 40 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5360", s => 40 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5392", s => 40 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L54b0", s => 40 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L54e2", s => 40 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5243", _ => 20
  | "read_sbr_dtdf.L53d3", _ => 20
  | "read_sbr_dtdf.L5523", _ => 20
  | "read_sbr_dtdf.L5272", _ => 20
  | "read_sbr_dtdf.L5402", _ => 20
  | "read_sbr_dtdf.L5552", _ => 20
  | "read_sbr_dtdf.L528f", _ => 20
  | "read_sbr_dtdf.L5564", _ => 20
  | "read_sbr_dtdf.L556b", _ => 20
  | "read_sbr_dtdf.L52a0", s => 20 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L52d2", s => 20 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5430", s => 20 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5462", s => 20 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L5580", s => 20 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L55b2", s => 20 - (s.regs.get64 .rax).toNat
  | "read_sbr_dtdf.L55ed", _ => 1
  | "read_sbr_dtdf.L55f3", _ => 1
  | "read_sbr_dtdf.L5622", _ => 1
  | _, _ => 0

/-- The exit: the return, with `CallPost`'s memory. -/
abbrev Post' (k : Nat) (x : DArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  DtdfPost k x ra t₀ s

abbrev BlockOb (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k x ra t₀ s) ⦄

macro "grind_cells'" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

/-! ## Focus: each atom of `T` at the head (an AC path), then one access lemma -/

omit [CodeEnv] in
theorem eq_r {A B X G : Mem 64 → Prop} (h : B = X ⋆ G) : A ⋆ B = X ⋆ (A ⋆ G) := by
  rw [h, Std.ExtHashMap.sep_comm_l]

omit [CodeEnv] in
theorem eq_l {A B X G : Mem 64 → Prop} (h : A = X ⋆ G) : A ⋆ B = X ⋆ (G ⋆ B) := by
  rw [h, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem eq_h {X B : Mem 64 → Prop} : X ⋆ B = X ⋆ B := rfl

omit [CodeEnv] in
theorem eq_last {A X : Mem 64 → Prop} : A ⋆ X = X ⋆ A := Std.ExtHashMap.sep_comm _ _

/-! ## `get_bits1` arithmetic -/

omit [CodeEnv] in
omit [CodeEnv] in
/-- The byte `get_bits1` loads (`buffer[index >> 3]`) is inside the buffer. -/
theorem rd_off1 (i p : BitVec 32) (L : Nat) (hi : i.toNat ≤ p.toNat) (hL : p.toNat / 8 + 4 ≤ L) :
    (BitVec.setWidth 64 (i.ushiftRight 3)).toNat + 1 ≤ L := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  have := i.isLt
  rw [Nat.mod_eq_of_lt (by omega)]; omega

omit [CodeEnv] in
theorem replaceLow_zero (b : BitVec 8) :
    (BitVec.setWidth 32 ((0#64).replaceLow b)).toNat = b.toNat := by
  have h1 := BitVec.toNat_replaceLow8_mod 0#64 b
  have h2 := BitVec.toNat_replaceLow8_div 0#64 b
  rw [BitVec.toNat_setWidth]
  simp at h2
  omega

omit [CodeEnv] in
/-- `get_bits1`'s index update (`xor; cmp; setl; add`: `index + (index < size_in_bits_plus8)`)
stays within `size_in_bits_plus8`. -/
theorem gb1_next (i p a : BitVec 32) (cf af : Bool) (hi : i.toNat ≤ p.toNat)
    (hp : p.toNat < 2 ^ 31) :
    (i + BitVec.setWidth 32 ((BitVec.setWidth 64 (a ^^^ a)).replaceLow (BitVec.ofNat 8
      (CondCode.l.interp (StatusFlags.from_result (i - p) ⟨cf, af,
        (i - p).signed != i.signed - p.signed⟩)).toNat))).toNat ≤ p.toNat := by
  rw [CondCode.interp_l_cmp_toInt32, BitVec.xor_self, BitVec.setWidth_zero]
  have hti : i.toInt = i.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have htp : p.toInt = p.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  rw [hti, htp]
  by_cases h : i.toNat < p.toNat
  · have : decide ((i.toNat : Int) < p.toNat) = true := by simp; omega
    rw [this]
    have e := replaceLow_zero (BitVec.ofNat 8 (true.toNat))
    rw [BitVec.toNat_add, e]
    simp; omega
  · have : decide ((i.toNat : Int) < p.toNat) = false := by simp; omega
    rw [this]
    have e := replaceLow_zero (BitVec.ofNat 8 (false.toNat))
    rw [BitVec.toNat_add, e]
    simp; omega

/-! ## The loop tests (`add $2, %rax; cmp %rax, %r8; jne` and `test $1, %dil; je`) -/

omit [CodeEnv] in
theorem cmp2_eq {a r : BitVec 64} {c j : Nat} {f : StatusFlags.from_result.Remaining}
    (ha : a = BitVec.ofNat 64 c) (hr : r = BitVec.ofNat 64 j) (hc : c < 2 ^ 32) (_hj : j < 2 ^ 32)
    (h : CondCode.nz.interp (StatusFlags.from_result (a - (BitVec.setWidth 64 2#64 + r)) f)
      = false) : c = j + 2 := by
  subst ha hr
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result, Bool.not_eq_false',
    beq_iff_eq, BitVec.zero_eq] at h
  bv_omega

omit [CodeEnv] in
theorem cmp2_ne {a r : BitVec 64} {c j : Nat} {f : StatusFlags.from_result.Remaining}
    (ha : a = BitVec.ofNat 64 c) (hr : r = BitVec.ofNat 64 j) (hc : c < 2 ^ 32) (_hj : j < 2 ^ 32)
    (h : CondCode.nz.interp (StatusFlags.from_result (a - (BitVec.setWidth 64 2#64 + r)) f)
      = true) : c ≠ j + 2 := by
  subst ha hr
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, BitVec.zero_eq] at h
  intro e; apply h; subst e; bv_omega

omit [CodeEnv] in
theorem add2 (j : Nat) (_hj : j < 2 ^ 32) :
    BitVec.setWidth 64 2#64 + BitVec.ofNat 64 j = BitVec.ofNat 64 (j + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem and1 (c : Nat) :
    BitVec.setWidth 8 (BitVec.ofNat 64 c) &&& BitVec.setWidth 8 1#64 = BitVec.ofNat 8 (c % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.and_one_is_mod]; omega

omit [CodeEnv] in
theorem test1_odd {d : BitVec 64} {c : Nat} {f : StatusFlags.from_result.Remaining}
    (hd : d = BitVec.ofNat 64 c)
    (h : CondCode.z.interp (StatusFlags.from_result (BitVec.setWidth 8 d &&& BitVec.setWidth 8 1#64)
      f) = false) : c % 2 = 1 := by
  subst hd
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_eq_false_iff_ne, ne_eq,
    BitVec.zero_eq, and1] at h
  bv_omega

omit [CodeEnv] in
theorem test1_even {d : BitVec 64} {c : Nat} {f : StatusFlags.from_result.Remaining}
    (hd : d = BitVec.ofNat 64 c)
    (h : CondCode.z.interp (StatusFlags.from_result (BitVec.setWidth 8 d &&& BitVec.setWidth 8 1#64)
      f) = true) : c % 2 = 0 := by
  subst hd
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_iff_eq, BitVec.zero_eq,
    and1] at h
  bv_omega

/-! ## The count tests (`dec; test; jle` and `cmp $1; jne`) -/

/-- A 4-byte load, as a `def` (see `GbL`). -/
def Ld4 (m : Mem 64) (a : BitVec 64) (c : Nat) : Prop :=
  m.loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 (c : Int)))

omit [CodeEnv] in
theorem Ld4.get {m : Mem 64} {a : BitVec 64} {c : Nat} (h : Ld4 m a c) :
    m.loadInt a 4 = some (Int.ofBytes (Int.toBytes 4 (c : Int))) := h

omit [CodeEnv] in
theorem le_dec (c : Nat) (hc : c ≤ 8) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result
      (BitVec.ofInt 32 (c : Int) - 1#32 &&& BitVec.ofInt 32 (c : Int) - 1#32) ⟨false, af, false⟩)
      = decide (c ≤ 1) := by
  simp only [CondCode.interp_le, StatusFlags.sf_from_result, StatusFlags.of_from_result,
    StatusFlags.zf_from_result]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem nz_dec (c : Nat) (hc : c ≤ 8) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result
      (BitVec.ofInt 32 (c : Int) - 1#32 - BitVec.setWidth 32 1#64) f) = decide (c ≠ 2) := by
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem rax_dec (c : Nat) (hc : 1 ≤ c) (hc8 : c ≤ 8) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (c : Int) - 1#32) = BitVec.ofNat 64 (c - 1) := by
  rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem le_sx (c : Nat) (hc : c ≤ 8) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result
      (BitVec.signExtend 64 (BitVec.ofInt 32 (c : Int))
        &&& BitVec.signExtend 64 (BitVec.ofInt 32 (c : Int))) ⟨false, af, false⟩)
      = decide (c = 0) := by
  simp only [CondCode.interp_le, StatusFlags.sf_from_result, StatusFlags.of_from_result,
    StatusFlags.zf_from_result]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem nz_sx (c : Nat) (hc : c ≤ 8) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.signExtend 64 (BitVec.ofInt 32 (c : Int)))
        - BitVec.setWidth 32 1#64) f) = decide (c ≠ 1) := by
  simp only [CondCode.interp_nz, StatusFlags.zf_from_result]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem z_sx (c : Nat) (hc : c ≤ 8) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.signExtend 64 (BitVec.ofInt 32 (c : Int)))
        - BitVec.setWidth 32 1#64) f) = decide (c = 1) := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result]
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem sx_eq (c : Nat) (hc : c ≤ 8) :
    BitVec.signExtend 64 (BitVec.ofInt 32 (c : Int)) = BitVec.ofNat 64 c := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem and_sx (c : Nat) (hc : c ≤ 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.signExtend 64 (BitVec.ofInt 32 (c : Int)))
      &&& BitVec.setWidth 32 2147483646#64) = BitVec.ofNat 64 (c / 2 * 2) := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem and_nat (c : Nat) (hc : c ≤ 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 c) &&& BitVec.setWidth 32 2147483646#64)
      = BitVec.ofNat 64 (c / 2 * 2) := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem zx_nat (c : Nat) (hc : c ≤ 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 c)) = BitVec.ofNat 64 c := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5 ∨ c = 6 ∨ c = 7 ∨ c = 8)
    with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

omit [CodeEnv] in
theorem xor0 (a : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 a ^^^ BitVec.setWidth 32 a) = BitVec.ofNat 64 0 := by
  simp

section
omit [CodeEnv]
variable {k : Nat} {x : DArgs} {ra : Int64} {t₀ : MachineData} {i : BitVec 32} {m : Mem 64}

theorem T_nenv : ∃ F, T k x ra t₀ i = c4 (arg2 t₀ + 8#64) x.v.nenv ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l eq_h))⟩

theorem T_nn : ∃ F, T k x ra t₀ i = c4 (arg2 t₀ + 0x18#64) x.v.nnoise ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r eq_h)))⟩

theorem T_df : ∃ F, T k x ra t₀ i = 11 ?@ (arg2 t₀ + 0x1c#64) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r eq_h))))⟩

theorem T_buf : ∃ F, T k x ra t₀ i = Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_l eq_h))))))⟩

theorem T_i : ∃ F, T k x ra t₀ i = cell4 (arg1 t₀ + 8#64) i ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_l (eq_r eq_h)))))))⟩

theorem T_p8 : ∃ F, T k x ra t₀ i = cell4 (arg1 t₀ + 0x10#64) x.p8 ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r eq_last))))))))⟩

theorem T_blocks : ∃ F, T k x ra t₀ i = Blocks [(x.buf, x.L)] ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r eq_last)))))⟩

/-- `T` with the index cell carved out, for the store of the index. -/
theorem T_i_eq (j : BitVec 32) : ∃ F, T k x ra t₀ i = cell4 (arg1 t₀ + 8#64) i ⋆ F
    ∧ T k x ra t₀ j = cell4 (arg1 t₀ + 8#64) j ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_l (eq_r eq_h))))))),
    eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_l (eq_r eq_h)))))))⟩

theorem T_ld_nenv (h : m =⋆ T k x ra t₀ i) :
    m.loadInt (arg2 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.v.nenv : Int))) := by
  obtain ⟨F, hF⟩ := (T_nenv : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_nn (h : m =⋆ T k x ra t₀ i) :
    m.loadInt (arg2 t₀ + 0x18#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.v.nnoise : Int))) := by
  obtain ⟨F, hF⟩ := (T_nn : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_buf (h : m =⋆ T k x ra t₀ i) :
    m.loadInt (arg1 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
  obtain ⟨F, hF⟩ := (T_buf : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem T_ld_i (h : m =⋆ T k x ra t₀ i) :
    m.loadInt (arg1 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) := by
  obtain ⟨F, hF⟩ := (T_i : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_p8 (h : m =⋆ T k x ra t₀ i) :
    m.loadInt (arg1 t₀ + 0x10#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  obtain ⟨F, hF⟩ := (T_p8 : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_st_i (h : m =⋆ T k x ra t₀ i) (j : BitVec 32) :
    m.storeInt (arg1 t₀ + 8#64) 4 j.toInt =⋆ T k x ra t₀ j := by
  obtain ⟨F, hF, hF'⟩ := (T_i_eq j : ∃ F, T k x ra t₀ i = _ ⋆ F ∧ _)
  rw [hF] at h
  rw [hF']
  exact storeInt_sep _ 4 _ _ m ⟨h, Int.toBytes_length 4 _⟩ j.toInt

/-- A load of a flag byte. -/
theorem T_ld_df (h : m =⋆ T k x ra t₀ i) (a : BitVec 64)
    (ha : (a - (arg2 t₀ + 0x1c#64)).toNat + 1 ≤ 11) : (m.loadInt a 1).isSome = true := by
  obtain ⟨F, hF⟩ := (T_df : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact Block.loadInt_isSome h ha

/-- A store of a flag byte. -/
theorem T_st_df (h : m =⋆ T k x ra t₀ i) (a : BitVec 64)
    (ha : (a - (arg2 t₀ + 0x1c#64)).toNat + 1 ≤ 11) (v : Int) :
    m.storeInt a 1 v =⋆ T k x ra t₀ i := by
  obtain ⟨F, hF⟩ := (T_df : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h ⊢
  exact Block.storeInt h ha v

/-- The three loads of `*gb` (`buffer`, `index`, `size_in_bits_plus8`) at the state `s`. A
`def` over atoms, so that `simp … at *` leaves it alone. -/
def GbL (x : DArgs) (i : BitVec 32) (s : MachineData) : Prop :=
  s.dmem.loadInt (s.regs.get64 .rsi + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rsi) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rsi + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))

theorem GbL.of {s : MachineData} (h : s.dmem =⋆ T k x ra t₀ i)
    (hrsi : s.regs.get64 .rsi = arg1 t₀) : GbL x i s := by
  unfold GbL; rw [hrsi]; exact ⟨T_ld_i h, T_ld_buf h, T_ld_p8 h⟩

theorem GbL.ld_i {s : MachineData} (h : GbL x i s) :
    s.dmem.loadInt (s.regs.get64 .rsi + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) :=
  h.1

theorem GbL.ld_p8 {s : MachineData} (h : GbL x i s) :
    s.dmem.loadInt (s.regs.get64 .rsi + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) :=
  h.2.2

theorem GbL.ld_buf {s : MachineData} (h : GbL x i s) :
    s.dmem.loadInt (s.regs.get64 .rsi) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) :=
  h.2.1

/-- The loads of `bs_num_env` and `bs_num_noise` at the state `s` (a `def`, as `GbL`). -/
def NL (x : DArgs) (s : MachineData) : Prop :=
  s.dmem.loadInt (s.regs.get64 .rdx + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.v.nenv : Int)))
  ∧ s.dmem.loadInt (s.regs.get64 .rdx + 24#64) 4
    = some (Int.ofBytes (Int.toBytes 4 (x.v.nnoise : Int)))

theorem NL.of {s : MachineData} (h : s.dmem =⋆ T k x ra t₀ i)
    (hrdx : s.regs.get64 .rdx = arg2 t₀) : NL x s := by
  unfold NL; rw [hrdx]; exact ⟨T_ld_nenv h, T_ld_nn h⟩

theorem NL.nenv {s : MachineData} (h : NL x s) :
    s.dmem.loadInt (s.regs.get64 .rdx + 8#64) 4
      = some (Int.ofBytes (Int.toBytes 4 (x.v.nenv : Int))) := h.1

theorem NL.nn {s : MachineData} (h : NL x s) :
    s.dmem.loadInt (s.regs.get64 .rdx + 24#64) 4
      = some (Int.ofBytes (Int.toBytes 4 (x.v.nnoise : Int))) := h.2

/-- A load from the bitstream buffer. -/
theorem T_ld_bs (h : m =⋆ T k x ra t₀ i) (off : BitVec 64) (n : Nat)
    (hin : off.toNat + n ≤ x.L) : (m.loadInt (x.buf + off) n).isSome = true := by
  obtain ⟨F, hF⟩ := (T_blocks : ∃ F, T k x ra t₀ i = _ ⋆ F)
  rw [hF] at h
  exact Blocks.loadInt_isSome h (Blocks.Inside.base_add hin)

end

end Kraken.Examples.Sbr.Dtdf
