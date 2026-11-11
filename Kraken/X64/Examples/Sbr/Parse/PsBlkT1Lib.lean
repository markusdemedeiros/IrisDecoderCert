import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib
import Kraken.Rules.PackedSse

/-!
# `ff_ps_read_data`, the fix-ups: lemmas for the blocks of `PsBlkT1_*`

* `vmovdqu` of a `ymm` (load and store): the rules of `Rules/PackedSse.lean` for `vmovups`,
  for the other mnemonic (same semantics, no alignment check).
* Byte lists: a store of bytes copied from the list itself, of zeros; the row clauses of `Rng`
  as one byte range.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP Lean.Order
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

/-! ## `vmovdqu` -/

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "t1_wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

local macro "t1_mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

/-- `vmovdqu m256, %ymm`: 32 readable bytes, at any alignment. -/
@[spec low] theorem MachineWP.t1_vmovdqu256_load_mem_spec (y : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ (∀ v, Mem.loadInt s.dmem a 32 = some v →
            WP.wp p Q E { s with zmms := s.zmms.set y (BitVec.ofInt 256 v) }) ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovdqu (.avx y) (.mem ⟨some (.reg b), idx, .int64 d⟩))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨hsome, hk⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr hseg]
  refine step_here hseg (Or.inl ?_)
  t1_wp_step
  t1_mem_access hv hv
  exact hk v hv _ hpl'

/-- `vmovdqu %ymm, m256`: 32 owned bytes, at any alignment. -/
@[spec low] theorem MachineWP.t1_vmovdqu256_store_mem_spec (y : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 32 (s.zmms.get y).toInt } ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovdqu (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx y))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨hsome, hk⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr hseg]
  refine step_here hseg (Or.inl ?_)
  t1_wp_step
  t1_mem_access hv hv
  exact hk _ hpl'

end Specs

namespace Kraken.Examples.Sbr.Ps

end Kraken.Examples.Sbr.Ps

/-- A jump exit to label `l` (the assertion left as the goal). -/
syntax "t1_jump " str : tactic
macro_rules
  | `(tactic| t1_jump $l) => `(tactic| (left; refine Table.ofLabels_at (l := $l) ⟨rfl, ?_, by edge_step⟩))

/-! ## Byte lists -/

namespace Kraken.Examples.Sbr.Ps

set_option exponentiation.threshold 512 in
theorem t1_get_set_ymm_same (s : RegZmms) (x : RegMm) (v : BitVec 256) :
    (s.set (.ymm x) v).get (.ymm x) = v := by
  simp only [RegZmms.get, RegZmms.set, AvxReg.base]
  rw [RegZmms.get512_set512_same]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, BitVec.extractLsb'_toNat, AvxWidth.bits]
  exact v.isLt

/-! ## Bytes of a store -/

theorem t1_toBytes_ofInt (n : Nat) (v : Int) :
    Int.toBytes n (BitVec.ofInt (8 * n) v).toInt = Int.toBytes n v := by
  rw [← Int.toBytes_emod n (BitVec.ofInt _ v).toInt, ← Int.toBytes_emod n v]
  congr 1
  simp only [Int.take, BitVec.toInt_ofInt]
  exact Int.bmod_emod

theorem t1_toBytes_rd (c : List UInt8) (o n : Nat) (h : o + n ≤ c.length) :
    Int.toBytes n (rd c o n) = (c.drop o).take n := by
  rw [rd, Int.toBytes_ofBytes n _ (by simp only [List.length_take, List.length_drop]; omega)]
  simp only [List.take_take, Nat.min_self]

theorem t1_wr_congr (c : List UInt8) (o n : Nat) (v v' : Int) (h : Int.toBytes n v = Int.toBytes n v') :
    wr c o n v = wr c o n v' := by
  simp only [wr, h]

theorem t1_getD_wr (c : List UInt8) (o n j : Nat) (v : Int) (h : o + n ≤ c.length) :
    (wr c o n v).getD j 0
      = if o ≤ j ∧ j < o + n then (Int.toBytes n v).getD (j - o) 0 else c.getD j 0 := by
  simp only [wr, List.append_assoc, List.getD_eq_getElem?_getD]
  have h1 : (c.take o).length = o := by simp only [List.length_take]; omega
  have h2 : (Int.toBytes n v).length = n := Int.toBytes_length n v
  split
  · rename_i hj
    rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega), h1]
  · rename_i hj
    by_cases hlt : j < o
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hlt]
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_drop, h1, h2]
      congr 2
      omega

/-- After a copy of `n` bytes from `o'` to `o` (non-overlapping or not: the bytes are read
before the store). -/
theorem t1_getD_copy (c : List UInt8) (o o' n j : Nat) (h : o + n ≤ c.length)
    (h' : o' + n ≤ c.length) :
    (wr c o n (rd c o' n)).getD j 0
      = if o ≤ j ∧ j < o + n then c.getD (j - o + o') 0 else c.getD j 0 := by
  rw [t1_getD_wr c o n j _ h, t1_toBytes_rd c o' n h']
  split
  · rename_i hj
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
    have hc : j - o < n := by omega
    simp only [hc, ite_true]
    congr 2
    omega
  · rfl

/-! ## Byte ranges -/

/-- Every byte `i8 c j`, `a ≤ j < a + len`, satisfies `P`. -/
def T1BR (c : List UInt8) (a len : Nat) (P : Int → Prop) : Prop :=
  ∀ j, a ≤ j → j < a + len → P (i8 c j)

theorem t1_rows_iff (c : List UInt8) (a : Nat) (P : Int → Prop) :
    (∀ e < 5, ∀ b < 34, P (i8 c (a + 34 * e + b))) ↔ T1BR c a 170 P := by
  constructor
  · intro h j hj1 hj2
    have := h ((j - a) / 34) (by omega) ((j - a) % 34) (by omega)
    rwa [show a + 34 * ((j - a) / 34) + (j - a) % 34 = j by omega] at this
  · intro h e he b hb
    exact h _ (by omega) (by omega)

/-- A copy inside or outside the range keeps `T1BR`. -/
theorem t1_BR_copy {c : List UInt8} {a len : Nat} {P : Int → Prop} (hB : T1BR c a len P)
    (o o' n : Nat) (h : o + n ≤ c.length) (h' : o' + n ≤ c.length)
    (hsrc : a ≤ o' ∧ o' + n ≤ a + len) (_hdst : (a ≤ o ∧ o + n ≤ a + len) ∨ o + n ≤ a ∨ a + len ≤ o) :
    T1BR (wr c o n (rd c o' n)) a len P := by
  intro j hj1 hj2
  simp only [i8]
  rw [t1_getD_copy c o o' n j h h']
  split
  · have := hB (j - o + o') (by omega) (by omega)
    simpa only [i8] using this
  · simpa only [i8] using hB j hj1 hj2

/-- A store outside the range keeps `T1BR`. -/
theorem t1_BR_out {c : List UInt8} {a len : Nat} {P : Int → Prop} (hB : T1BR c a len P)
    (o n : Nat) (v : Int) (h : o + n ≤ c.length) (hd : o + n ≤ a ∨ a + len ≤ o) :
    T1BR (wr c o n v) a len P := by
  intro j hj1 hj2
  rw [i8_wr c o n j v h (by omega)]
  exact hB j hj1 hj2

theorem t1_toBytes_zero_getD : ∀ n j : Nat, (Int.toBytes n 0).getD j 0 = 0
  | 0, j => by simp [Int.toBytes]
  | n + 1, 0 => by simp [Int.toBytes, Int.take]
  | n + 1, j + 1 => by
    simp only [Int.toBytes, Int.zero_ediv, List.getD_cons_succ]
    exact t1_toBytes_zero_getD n j

/-- A store of zeros inside the range keeps a `T1BR` that holds of `0`. -/
theorem t1_BR_zero {c : List UInt8} {a len : Nat} {P : Int → Prop} (hB : T1BR c a len P)
    (hP : P 0) (o n : Nat) (h : o + n ≤ c.length) :
    T1BR (wr c o n 0) a len P := by
  intro j hj1 hj2
  simp only [i8]
  rw [t1_getD_wr c o n j _ h]
  split
  · rw [t1_toBytes_zero_getD]; exact hP
  · simpa only [i8] using hB j hj1 hj2


/-! ## Stores that keep the invariants -/

section
variable {c : List UInt8} (o n : Nat) (v : Int)

theorem t1_PsInv_wr (h : PsInv c) (ho : 48 ≤ o) (hn : o + n ≤ 764) : PsInv (wr c o n v) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6⟩ := h
  have hL : o + n ≤ c.length := by omega
  refine ⟨by rw [wr_length _ _ _ _ hL, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [i32_wr] <;> assumption

theorem t1_IidS_wr {hd : Int} (h : IidS c hd) (hl : c.length = 764) (ho : 16 ≤ o)
    (hn : o + n ≤ 764) : IidS (wr c o n v) hd := by
  simp (disch := omega) only [IidS, i32_wr] at h ⊢
  exact h

theorem t1_H_wr {N : Nat} (h : T1H c N) (hl : c.length = 764) (hN : N ≤ 5)
    (hd : 76 ≤ o ∨ o + n ≤ 52) (hn : o + n ≤ 764) : T1H (wr c o n v) N := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, fun e he => ?_, fun e he => ?_⟩
  · simp (disch := omega) only [bord, i32_wr]; exact h1
  · simp (disch := omega) only [bord, i32_wr]; exact h2 e he
  · simp (disch := omega) only [bord, i32_wr]; exact h3 e he

theorem t1_IidB_wr {M : Nat} (h : IidB c M) (hl : c.length = 764) (hM : M ≤ 5) (ho : 16 ≤ o)
    (hd : 76 + 34 * M ≤ o ∨ o + n ≤ 76) (hn : o + n ≤ 764) : IidB (wr c o n v) M := by
  intro e he b hb hc
  have he' : e < M := by omega
  simp (disch := omega) only [i32_wr, i8_wr] at hc ⊢
  exact h e he b hb hc

theorem t1_IidZ_wr (h : IidZ c) (hl : c.length = 764) (ho : 16 ≤ o)
    (hd : 246 ≤ o ∨ o + n ≤ 76) (hn : o + n ≤ 764) : IidZ (wr c o n v) := by
  intro h4 e he b hb hc
  have he' : e < 5 := by omega
  simp (disch := omega) only [i32_wr, i8_wr] at h4 hc ⊢
  exact h h4 e he b hb hc

theorem t1_Row_wr {N m : Nat} (h : T1Row c N m) (hl : c.length = 764) (hm : m ≤ 34)
    (ho : 12 ≤ o) (hd : 76 + 34 * N + 34 ≤ o ∨ o + n ≤ 76 + 34 * N) (hn : o + n ≤ 764) :
    T1Row (wr c o n v) N m := by
  intro b hb
  simp (disch := omega) only [i32_wr, i8_wr]
  exact h b hb

/-- `Rng` as conditions on `is34bands`, `iid_quant` and two byte ranges. -/
theorem t1_Rng_iff (c : List UInt8) :
    Rng c ↔ ((i32 c 756 = 0 ∨ i32 c 756 = 1) ∧ (i32 c 8 = 0 ∨ i32 c 8 = 1))
      ∧ T1BR c 246 170 (fun v => 0 ≤ v ∧ v ≤ 7) ∧ T1BR c 416 340 (fun v => 0 ≤ v ∧ v ≤ 7) := by
  unfold Rng
  rw [t1_rows_iff c 246 (fun v => 0 ≤ v ∧ v ≤ 7)]
  constructor
  · rintro ⟨a, b, hc, hp⟩
    refine ⟨⟨a, b⟩, hc, fun j hj1 hj2 => ?_⟩
    by_cases hj : j < 586
    · have := hp ((j - 416) / 34) (by omega) ((j - 416) % 34) (by omega)
      rw [show 416 + 34 * ((j - 416) / 34) + (j - 416) % 34 = j by omega] at this
      exact ⟨this.1, this.2.1⟩
    · have := hp ((j - 586) / 34) (by omega) ((j - 586) % 34) (by omega)
      rw [show 586 + 34 * ((j - 586) / 34) + (j - 586) % 34 = j by omega] at this
      exact ⟨this.2.2.1, this.2.2.2⟩
  · rintro ⟨⟨a, b⟩, hc, hp⟩
    refine ⟨a, b, hc, fun e he b' hb' => ?_⟩
    have h1 := hp (416 + 34 * e + b') (by omega) (by omega)
    have h2 := hp (586 + 34 * e + b') (by omega) (by omega)
    exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- A store outside `[246, 760)` and `[8, 12)` keeps `Rng`. -/
theorem t1_Rng_wr (h : Rng c) (hl : c.length = 764) (ho : 12 ≤ o)
    (hd : o + n ≤ 246 ∨ 760 ≤ o) (hn : o + n ≤ 764) : Rng (wr c o n v) := by
  rw [t1_Rng_iff] at h ⊢
  obtain ⟨⟨a, b⟩, h1, h2⟩ := h
  have hL : o + n ≤ c.length := by omega
  refine ⟨⟨?_, ?_⟩, t1_BR_out h1 o n v hL (by omega), t1_BR_out h2 o n v hL (by omega)⟩ <;>
    simp (disch := omega) only [i32_wr] <;> assumption

end

end Kraken.Examples.Sbr.Ps

/-- `pnorm` and the scaled index registers. -/
syntax "t1norm" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| t1norm $[$loc]?) => `(tactic| simp only [Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, AddrIndex.offset64_scale1,
      AddrIndex.offset64_scale2, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
      BitVec.add_zero, BitVec.ofNat_eq_ofNat,
      Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, Nat.reducePow, Nat.reduceMod,
      Nat.reduceSub, BitVec.toNat_ofNat, reduceIte, Kraken.Examples.Sbr.Ps.rsp0, Kraken.Examples.Sbr.arg0,
      Kraken.Examples.Sbr.arg1, Kraken.Examples.Sbr.arg2, Kraken.Examples.Sbr.arg3] $[$loc]?)

namespace Kraken.Examples.Sbr.Ps

section
variable [CodeEnv]

/-! ## The frame part of the assertions -/

theorem t1_B_st {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) (o n : Nat) (v : Int)
    (ho : 48 ≤ o) (hn : o + n ≤ 764)
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 o) n v)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15) :
    T1B k Ext x ra t₀ s' (wr c o n v) f N := by
  obtain ⟨⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hM⟩, hI, hr, hN, h40, h68⟩ := h
  refine ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3,
    t1_PsInv_wr o n v a4 ho hn, a5, a6, a7⟩, by rw [hm]; exact Fr_c_store hM a4.1 o n hn v⟩,
    by rw [h8]; exact hI, by rw [h15]; exact hr, hN, h40, h68⟩

theorem t1_B_eq {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N)
    (hm : s'.dmem = s.dmem)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15) :
    T1B k Ext x ra t₀ s' c f N := by
  obtain ⟨⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hM⟩, hI, hr, hN, h40, h68⟩ := h
  exact ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3, a4, a5, a6, a7⟩,
    by rw [hm]; exact hM⟩, by rw [h8]; exact hI, by rw [h15]; exact hr, hN, h40, h68⟩

theorem t1_B_len {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) : c.length = 764 := by
  obtain ⟨⟨_, ⟨_, _, _, a4, _⟩, _⟩, _⟩ := h
  exact a4.1

theorem t1_B_load {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) (o n : Nat) (hn : o + n ≤ 764) :
    s.dmem.loadInt (arg2 t₀ + BitVec.ofNat 64 o) n = some (rd c o n) :=
  Fr_c_load h.1.2.2 (t1_B_len h) o n hn

omit [CodeEnv] in
theorem t1_sw (N : Nat) (h : N < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 N)) = BitVec.ofNat 64 N := by
  apply BitVec.eq_of_toNat_eq
  have h1 : N % 2 ^ 64 = N := Nat.mod_eq_of_lt (by omega)
  have h2 : N % 2 ^ 32 = N := Nat.mod_eq_of_lt h
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, h1, h2]

/-! ## Row addresses -/

omit [CodeEnv] in
theorem t1_r34 (S : Nat) :
    BitVec.ofNat 64 S <<< 5 + BitVec.ofNat 64 S * 2#64 = BitVec.ofNat 64 (34 * S) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
theorem t1_addr (a : BitVec 64) (m o : Nat) :
    a + BitVec.ofNat 64 m + BitVec.ofNat 64 o = a + BitVec.ofNat 64 (m + o) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

end

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

section
variable [CodeEnv]

omit [CodeEnv] in
theorem t1_sw16 (v : BitVec 16) :
    BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = v := by
  apply BitVec.eq_of_toNat_eq
  have := v.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-- The row copy (`movzwl`/`mov %di` of the last 2 bytes, `vmovdqu` of the first 32): the
frame part. The result is `T1Cp c src dst`. -/
abbrev T1Cp (c : List UInt8) (src dst : Nat) : List UInt8 :=
  wr (wr c (dst + 32) 2 (rd c (src + 32) 2)) dst 32
    (rd (wr c (dst + 32) 2 (rd c (src + 32) 2)) src 32)

theorem t1_copy {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) (src dst : Nat)
    (hs : src + 34 ≤ 764) (hd : dst + 34 ≤ 764) (hd48 : 48 ≤ dst) {v2 v32 : Int}
    (hv2 : s.dmem.loadInt (arg2 t₀ + BitVec.ofNat 64 (src + 32)) 2 = some v2)
    (hv32 : (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 (dst + 32)) 2
        (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 v2)))).toInt).loadInt
        (arg2 t₀ + BitVec.ofNat 64 src) 32 = some v32)
    (hm : s'.dmem = (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 (dst + 32)) 2
        (BitVec.setWidth 16 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 v2)))).toInt).storeInt
        (arg2 t₀ + BitVec.ofNat 64 dst) 32 (BitVec.ofInt 256 v32).toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15) :
    T1B k Ext x ra t₀ s' (T1Cp c src dst) f N := by
  have hl := t1_B_len h
  rw [t1_B_load h _ _ (by omega)] at hv2
  cases hv2
  rw [t1_sw16] at hv32 hm
  have e2 : wr c (dst + 32) 2 (BitVec.ofInt 16 (rd c (src + 32) 2)).toInt
      = wr c (dst + 32) 2 (rd c (src + 32) 2) := t1_wr_congr _ _ _ _ _ (t1_toBytes_ofInt 2 _)
  have hM := Fr_c_store h.1.2.2 hl (dst + 32) 2 (by omega)
    (BitVec.ofInt 16 (rd c (src + 32) 2)).toInt
  rw [e2] at hM
  have hl1 : (wr c (dst + 32) 2 (rd c (src + 32) 2)).length = 764 := by
    rw [wr_length _ _ _ _ (by omega), hl]
  rw [Fr_c_load hM hl1 src 32 (by omega)] at hv32
  cases hv32
  have h1 := t1_B_st h (dst + 32) 2 (BitVec.ofInt 16 (rd c (src + 32) 2)).toInt (by omega) (by omega)
    (s' := { s with dmem := Mem.storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 (dst + 32)) 2 (BitVec.ofInt 16 (rd c (src + 32) 2)).toInt }) rfl rfl rfl rfl rfl
  rw [e2] at h1
  have h2 := t1_B_st h1 dst 32 (BitVec.ofInt 256 (rd (wr c (dst + 32) 2 (rd c (src + 32) 2)) src 32)).toInt
    (by omega) (by omega) hm hsp hbp h8 h15
  rwa [t1_wr_congr _ _ _ _ _ (t1_toBytes_ofInt 32 _)] at h2

omit [CodeEnv] in
/-- A copy inside the `icc` rows, or inside the `ipd`/`opd` rows, keeps `Rng`. -/
theorem t1_Rng_copy {c : List UInt8} (h : Rng c) (hl : c.length = 764) (o o' n : Nat)
    (hr : (246 ≤ o' ∧ o' + n ≤ 416 ∧ 246 ≤ o ∧ o + n ≤ 416)
      ∨ (416 ≤ o' ∧ o' + n ≤ 756 ∧ 416 ≤ o ∧ o + n ≤ 756)) :
    Rng (wr c o n (rd c o' n)) := by
  rw [t1_Rng_iff] at h ⊢
  obtain ⟨⟨a, b⟩, h1, h2⟩ := h
  have hL : o + n ≤ c.length := by omega
  have hL' : o' + n ≤ c.length := by omega
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp (disch := omega) only [i32_wr]; exact a
  · simp (disch := omega) only [i32_wr]; exact b
  · rcases hr with hr | hr
    · exact t1_BR_copy h1 o o' n hL hL' (by omega) (by omega)
    · exact t1_BR_out h1 o n _ hL (by omega)
  · rcases hr with hr | hr
    · exact t1_BR_out h2 o n _ hL (by omega)
    · exact t1_BR_copy h2 o o' n hL hL' (by omega) (by omega)

omit [CodeEnv] in
theorem t1_len_Cp {c : List UInt8} (hl : c.length = 764) (src dst : Nat) (hd : dst + 34 ≤ 764) :
    (T1Cp c src dst).length = 764 := by
  simp only [T1Cp]
  rw [wr_length _ _ _ _ (by rw [wr_length _ _ _ _ (by omega)]; omega),
    wr_length _ _ _ _ (by omega), hl]

omit [CodeEnv] in
theorem t1_i32_Cp {c : List UInt8} (hl : c.length = 764) (src dst o : Nat) (hd : dst + 34 ≤ 764)
    (ho : o + 4 ≤ dst ∨ dst + 34 ≤ o) : i32 (T1Cp c src dst) o = i32 c o := by
  simp only [T1Cp]
  have hl1 : (wr c (dst + 32) 2 (rd c (src + 32) 2)).length = 764 := by
    rw [wr_length _ _ _ _ (by omega), hl]
  rw [i32_wr _ _ _ _ _ (by omega) (by omega), i32_wr _ _ _ _ _ (by omega) (by omega)]

omit [CodeEnv] in
/-- The `iid` row copy keeps `T1W0` (with `enable_iid ≠ 0`). -/
theorem t1_W0_iid {c f : List UInt8} {N S : Nat} (h : T1W0 c f N) (hl : c.length = 764)
    (hN : N ≤ 4) (_hS : S < 5) (h4 : i32 c 4 ≠ 0) :
    T1W0 (T1Cp c (76 + 34 * S) (76 + 34 * N)) f N := by
  obtain ⟨hR, hH, hI, hB, -⟩ := h
  have hl1 : (wr c (76 + 34 * N + 32) 2 (rd c (76 + 34 * S + 32) 2)).length = 764 := by
    rw [wr_length _ _ _ _ (by omega), hl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact t1_Rng_wr _ _ _ (t1_Rng_wr _ _ _ hR hl (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega)
  · exact t1_H_wr _ _ _ (t1_H_wr _ _ _ hH hl (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega)
  · exact t1_IidS_wr _ _ _ (t1_IidS_wr _ _ _ hI hl (by omega) (by omega)) hl1 (by omega) (by omega)
  · exact t1_IidB_wr _ _ _ (t1_IidB_wr _ _ _ hB hl (by omega) (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega) (by omega)
  · intro h4'
    rw [t1_i32_Cp hl _ _ _ (by omega) (by omega)] at h4'
    exact absurd h4' h4

omit [CodeEnv] in
/-- An `icc`/`ipd`/`opd` row copy keeps `T1W0`. -/
theorem t1_W0_rng {c f : List UInt8} {N S : Nat} (h : T1W0 c f N) (hl : c.length = 764)
    (hN : N ≤ 4) (hS : S < 5) (a : Nat) (ha : a = 246 ∨ a = 416 ∨ a = 586) :
    T1W0 (T1Cp c (a + 34 * S) (a + 34 * N)) f N := by
  obtain ⟨hR, hH, hI, hB, hZ⟩ := h
  have hl1 : (wr c (a + 34 * N + 32) 2 (rd c (a + 34 * S + 32) 2)).length = 764 := by
    rw [wr_length _ _ _ _ (by omega), hl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact t1_Rng_copy (t1_Rng_copy hR hl _ _ _ (by omega)) hl1 _ _ _ (by omega)
  · exact t1_H_wr _ _ _ (t1_H_wr _ _ _ hH hl (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega)
  · exact t1_IidS_wr _ _ _ (t1_IidS_wr _ _ _ hI hl (by omega) (by omega)) hl1 (by omega) (by omega)
  · exact t1_IidB_wr _ _ _ (t1_IidB_wr _ _ _ hB hl (by omega) (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega) (by omega)
  · exact t1_IidZ_wr _ _ _ (t1_IidZ_wr _ _ _ hZ hl (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega)

end

end Kraken.Examples.Sbr.Ps

/-- A register read of a register-file update (the frame register side goals). -/
macro "t1r" : tactic => `(tactic| simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, reduceIte])

namespace Kraken.Examples.Sbr.Ps

section
variable {c f : List UInt8} (o n : Nat) (v : Int)

theorem t1_Fix_wr (h : T1Fix c) (hl : c.length = 764) (ho : 246 ≤ o) (hn : o + n ≤ 764) :
    T1Fix (wr c o n v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hL : o + n ≤ c.length := by omega
  have e44 : ne (wr c o n v) = ne c := i32_wr _ _ _ _ _ hL (by omega)
  have hb : ∀ e : Nat, e ≤ 5 → bord (wr c o n v) e = bord c e := fun e he =>
    i32_wr _ _ _ _ _ hL (by omega)
  refine ⟨by rw [e44]; exact h1, by rw [e44]; exact h2, by rw [hb 0 (by omega)]; exact h3,
    fun e he => ?_, ?_, ?_⟩
  · rw [e44] at he
    rw [hb e (by omega), hb (e + 1) (by omega)]; exact h4 e he
  · rw [e44, hb _ (by omega)]; exact h5
  · rw [e44]
    intro e he b hb' hc
    simp (disch := omega) only [i32_wr, i8_wr] at hc ⊢
    exact h6 e he b hb' hc

theorem t1_W2_756 [CodeEnv] (h : T1W2 c f) (hl : c.length = 764) (b : BitVec 32)
    (hb : b.toInt = 0 ∨ b.toInt = 1) : T1W2 (wr c 756 4 b.toInt) f := by
  obtain ⟨hR, hI, hF⟩ := h
  refine ⟨?_, t1_IidS_wr _ _ _ hI hl (by omega) (by omega), t1_Fix_wr _ _ _ hF hl (by omega) (by omega)⟩
  rw [t1_Rng_iff] at hR ⊢
  obtain ⟨⟨-, a⟩, h1, h2⟩ := hR
  have hL : 756 + 4 ≤ c.length := by omega
  refine ⟨⟨by rw [i32_wr_same _ _ _ hL]; exact hb, ?_⟩, t1_BR_out h1 _ _ _ hL (by omega),
    t1_BR_out h2 _ _ _ hL (by omega)⟩
  simp (disch := omega) only [i32_wr]; exact a

theorem t1_W2_zero (h : T1W2 c f) (hl : c.length = 764) (ho : 416 ≤ o) (hn : o + n ≤ 756) :
    T1W2 (wr c o n 0) f := by
  obtain ⟨hR, hI, hF⟩ := h
  refine ⟨?_, t1_IidS_wr _ _ _ hI hl (by omega) (by omega), t1_Fix_wr _ _ _ hF hl (by omega) (by omega)⟩
  rw [t1_Rng_iff] at hR ⊢
  obtain ⟨⟨a, b⟩, h1, h2⟩ := hR
  have hL : o + n ≤ c.length := by omega
  refine ⟨⟨?_, ?_⟩, t1_BR_out h1 _ _ _ hL (by omega), t1_BR_zero h2 (by omega) _ _ hL⟩
  · simp (disch := omega) only [i32_wr]; exact a
  · simp (disch := omega) only [i32_wr]; exact b

theorem t1_W0_760 {N : Nat} (h : T1W0 c f N) (hl : c.length = 764) (hN : N ≤ 5) :
    T1W0 (wr c 760 4 v) f N := by
  obtain ⟨hR, hH, hI, hB, hZ⟩ := h
  exact ⟨t1_Rng_wr _ _ _ hR hl (by omega) (by omega) (by omega),
    t1_H_wr _ _ _ hH hl hN (by omega) (by omega), t1_IidS_wr _ _ _ hI hl (by omega) (by omega),
    t1_IidB_wr _ _ _ hB hl hN (by omega) (by omega) (by omega),
    t1_IidZ_wr _ _ _ hZ hl (by omega) (by omega) (by omega)⟩

end

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `vpxor %xmm0, %xmm0, %xmm0` clears the whole `ymm0`. -/
theorem t1_vpxor_ymm (s : RegZmms) (x : RegMm) (a : BitVec 128) :
    (s.set (.xmm x) (a ^^^ a)).get (.ymm x) = 0#256 := by
  simp only [RegZmms.get, RegZmms.set, AvxReg.base, BitVec.xor_self]
  rw [RegZmms.get512_set512_same]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, AvxWidth.bits]

end Kraken.Examples.Sbr.Ps

/-- A load from `*ps`, or from `*ps` after one store (the side goals of loads and stores). -/
syntax "t1_some " term : tactic
macro_rules
  | `(tactic| t1_some $hB) => `(tactic| first
      | (rw [Kraken.Examples.Sbr.Ps.t1_B_load $hB _ _ (by omega)]; rfl)
      | (rw [Kraken.Examples.Sbr.Ps.Fr_c_load (Kraken.Examples.Sbr.Ps.Fr_c_store $hB.1.2.2
            (Kraken.Examples.Sbr.Ps.t1_B_len $hB) _ _ (by omega) _)
            (by rw [Kraken.Examples.Sbr.Ps.wr_length _ _ _ _ (by rw [Kraken.Examples.Sbr.Ps.t1_B_len $hB]; omega),
              Kraken.Examples.Sbr.Ps.t1_B_len $hB]) _ _ (by omega)]; rfl))

namespace Kraken.Examples.Sbr.Ps

/-- `movzbl %cl, %ecx` of a flag. -/
theorem t1_zext_le1 (b : BitVec 8) (h : b ≤ 1#8) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))).toInt = 0
      ∨ (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))).toInt = 1 := by
  have : b = 0#8 ∨ b = 1#8 := by bv_omega
  rcases this with rfl | rfl <;> decide

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

theorem t1_setcc_le1 (r : BitVec 64) (b : Bool) :
    BitVec.setWidth 8 (r.replaceLow (BitVec.ofNat 8 b.toNat)) ≤ 1#8 := by
  rw [BitVec.setWidth_replaceLow8]; cases b <;> decide

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

theorem t1_B_st2 [CodeEnv] {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s s' : MachineData} {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N)
    (o1 n1 : Nat) (v1 : Int) (o2 n2 : Nat) (v2 : Int)
    (ho1 : 48 ≤ o1) (hn1 : o1 + n1 ≤ 764) (ho2 : 48 ≤ o2) (hn2 : o2 + n2 ≤ 764)
    (hm : s'.dmem = (s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 o1) n1 v1).storeInt
      (arg2 t₀ + BitVec.ofNat 64 o2) n2 v2)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15) :
    T1B k Ext x ra t₀ s' (wr (wr c o1 n1 v1) o2 n2 v2) f N :=
  t1_B_st (s := { s with dmem := s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 o1) n1 v1 })
    (t1_B_st h o1 n1 v1 ho1 hn1 rfl rfl rfl rfl rfl) o2 n2 v2 ho2 hn2 hm hsp hbp h8 h15

theorem t1_ymm_toInt {v : BitVec 256} (h : BitVec.setWidth 256 v = 0#256) : v.toInt = 0 := by
  rw [BitVec.setWidth_eq] at h; rw [h]; rfl

/-- Two zero stores into `ipd`/`opd` keep `T1W2`. -/
theorem t1_W2_zero2 {c f : List UInt8} (h : T1W2 c f) (hl : c.length = 764) (o1 o2 : Nat)
    (h1 : 416 ≤ o1) (h1' : o1 + 32 ≤ 756) (h2 : 416 ≤ o2) (h2' : o2 + 32 ≤ 756) :
    T1W2 (wr (wr c o1 32 0) o2 32 0) f :=
  t1_W2_zero _ _ (t1_W2_zero _ _ h hl h1 h1') (by rw [wr_length _ _ _ _ (by omega), hl]) h2 h2'

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-! ## Condition codes (the flags literal as `cmp`/`test` leave it) -/

theorem t1_zf {w} (v : BitVec w) (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result v f).zf = (v == 0#w) := rfl

theorem t1_z (s : StatusFlags) : CondCode.z.interp s = s.zf := rfl

theorem t1_nc8 (a b : BitVec 8) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  grind [BitVec.unsigned_eq]

theorem t1_a8 (a b : BitVec 8) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat < a.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, t1_zf]
  have h1 : ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
    grind [BitVec.unsigned_eq]
  have h2 : (a - b == 0#8) = decide (a.toNat = b.toNat) := by
    by_cases h : a.toNat = b.toNat
    · have : a = b := BitVec.eq_of_toNat_eq h
      subst this; simp
    · have : a - b ≠ 0#8 := by
        intro h'; apply h; have := congrArg (· + b) h'
        simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this; rw [this]
      simp [this, h]
  rw [h1, h2]
  by_cases hl : a.toNat < b.toNat <;> by_cases he : a.toNat = b.toNat <;> simp [hl, he] <;> omega

theorem t1_be8 (a b : BitVec 8) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat ≤ b.toNat) := by
  have h := t1_a8 a b af of
  rw [CondCode.interp_a] at h
  rw [CondCode.interp_be]
  have : ∀ x y : Bool, (!x && !y) = decide (b.toNat < a.toNat) →
      (x || y) = decide (a.toNat ≤ b.toNat) := by
    intro x y hxy; cases x <;> cases y <;> simp at hxy ⊢ <;> omega
  exact this _ _ h

theorem t1_nc32 (a b : BitVec 32) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  grind [BitVec.unsigned_eq]

theorem t1_a32 (a b : BitVec 32) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat < a.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, t1_zf]
  have h1 : ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
    grind [BitVec.unsigned_eq]
  have h2 : (a - b == 0#32) = decide (a.toNat = b.toNat) := by
    by_cases h : a.toNat = b.toNat
    · have : a = b := BitVec.eq_of_toNat_eq h
      subst this; simp
    · have : a - b ≠ 0#32 := by
        intro h'; apply h; have := congrArg (· + b) h'
        simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this; rw [this]
      simp [this, h]
  rw [h1, h2]
  by_cases hl : a.toNat < b.toNat <;> by_cases he : a.toNat = b.toNat <;> simp [hl, he] <;> omega

theorem t1_be32 (a b : BitVec 32) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat ≤ b.toNat) := by
  have h := t1_a32 a b af of
  rw [CondCode.interp_a] at h
  rw [CondCode.interp_be]
  have : ∀ x y : Bool, (!x && !y) = decide (b.toNat < a.toNat) →
      (x || y) = decide (a.toNat ≤ b.toNat) := by
    intro x y hxy; cases x <;> cases y <;> simp at hxy ⊢ <;> omega
  exact this _ _ h

theorem t1_nc64 (a b : BitVec 64) (af of : Bool) :
    CondCode.nc.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  rw [CondCode.interp_nc, StatusFlags.cf_from_result]
  grind [BitVec.unsigned_eq]

theorem t1_a64 (a b : BitVec 64) (af of : Bool) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat < a.toNat) := by
  rw [CondCode.interp_a, StatusFlags.cf_from_result, t1_zf]
  have h1 : ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
    grind [BitVec.unsigned_eq]
  have h2 : (a - b == 0#64) = decide (a.toNat = b.toNat) := by
    by_cases h : a.toNat = b.toNat
    · have : a = b := BitVec.eq_of_toNat_eq h
      subst this; simp
    · have : a - b ≠ 0#64 := by
        intro h'; apply h; have := congrArg (· + b) h'
        simp only [BitVec.sub_add_cancel, BitVec.zero_add] at this; rw [this]
      simp [this, h]
  rw [h1, h2]
  by_cases hl : a.toNat < b.toNat <;> by_cases he : a.toNat = b.toNat <;> simp [hl, he] <;> omega

theorem t1_be64 (a b : BitVec 64) (af of : Bool) :
    CondCode.be.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat ≤ b.toNat) := by
  have h := t1_a64 a b af of
  rw [CondCode.interp_a] at h
  rw [CondCode.interp_be]
  have : ∀ x y : Bool, (!x && !y) = decide (b.toNat < a.toNat) →
      (x || y) = decide (a.toNat ≤ b.toNat) := by
    intro x y hxy; cases x <;> cases y <;> simp at hxy ⊢ <;> omega
  exact this _ _ h

end Kraken.Examples.Sbr.Ps



namespace Kraken.Examples.Sbr.Ps

/-- A load of the locals at `rbp - d` (the displacement as `vcgen` leaves it). -/
theorem t1_B_fload [CodeEnv] {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N)
    (a : BitVec 64) (d n : Nat) (ha : a.toNat = 2 ^ 64 - d) (h1 : 8 < d) (h2 : d ≤ 0xa0)
    (hn : 0xa0 - d + n ≤ 0x78) :
    s.dmem.loadInt (s.regs.get64 .rbp + a) n = some (rd f (0xa0 - d) n) := by
  obtain ⟨⟨_, ⟨_, hbp, hfl, _⟩, hm⟩, _⟩ := h
  have e : s.regs.get64 .rbp + a = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 (0xa0 - d) := by
    rw [hbp, show a = BitVec.ofNat 64 (2 ^ 64 - d) from BitVec.eq_of_toNat_eq (by simp [ha]; omega)]
    exact fr_addr _ d h1 h2
  rw [e]; exact Fr_f_load hm hfl _ n hn

theorem t1_B_inv [CodeEnv] {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s : MachineData} {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) : PsInv c := by
  obtain ⟨⟨_, ⟨_, _, _, hP, _⟩, _⟩, _⟩ := h
  exact hP

theorem t1_sw_ofInt (m : Int) (h0 : 0 ≤ m) (h1 : m < 2 ^ 31) :
    BitVec.setWidth 32 (BitVec.ofInt 64 m) = BitVec.ofNat 32 m.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem t1_toInt_ofNat32 (n : Nat) (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- The low byte of a small 8-byte slot. -/
theorem t1_rd1 (f : List UInt8) (o : Nat) (v : Int) (hl : o + 8 ≤ f.length) (h : rd f o 8 = v)
    (hv : v < 2 ^ 8) : rd f o 1 = v := by
  have e : (f.drop o).take 8 = (f.drop o).take 1 ++ ((f.drop o).drop 1).take 7 :=
    by rw [show (8 : Nat) = 1 + 7 from rfl, List.take_add]
  have hl1 : ((f.drop o).take 1).length = 1 := by simp only [List.length_take, List.length_drop]; omega
  simp only [rd] at h ⊢
  rw [e, Int.ofBytes_append, hl1] at h
  have a1 := Int.ofBytes_ge_zero ((f.drop o).take 1)
  have a2 := Int.ofBytes_ge_zero (((f.drop o).drop 1).take 7)
  have a3 := Int.ofBytes_lt ((f.drop o).take 1)
  rw [hl1] at a3
  omega

/-- `test %ecx, %ecx; jle`. -/
theorem t1_le_test (a : BitVec 32) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result (a &&& a) { cf := false, af := af, of := false })
      = decide (a.toInt ≤ 0) := by
  rw [CondCode.interp_le, StatusFlags.sf_from_result, StatusFlags.of_from_result, t1_zf,
    BitVec.and_self]
  by_cases h0 : a = 0#32
  · subst h0; rfl
  · have : (a == 0#32) = false := by simpa using h0
    rw [this, Bool.or_false]
    have h1 : a.toInt ≠ 0 := fun h => h0 (by
      apply BitVec.eq_of_toInt_eq; rw [h]; rfl)
    by_cases hm : a.msb = true
    · rw [hm]; have := (BitVec.msb_eq_toInt (x := a)); simp_all; omega
    · simp only [Bool.not_eq_true] at hm
      rw [hm]; have := (BitVec.msb_eq_toInt (x := a)); simp_all; omega

/-- `test %r, %r; je/jne` with `r` the low half of a register. -/
theorem t1_z_test (a : BitVec 32) (af : Bool) :
    CondCode.z.interp (StatusFlags.from_result (a &&& a) { cf := false, af := af, of := false })
      = decide (a = 0#32) := by
  rw [t1_z, t1_zf, BitVec.and_self]; by_cases h : a = 0#32 <;> simp [h]

/-! ## The `iid` row of the fake envelope -/

section
variable {c f : List UInt8} {N : Nat}

theorem t1_W1_of (h : T1W0 c f N) (hN : N ≤ 4)
    (hr : ∀ b : Nat, b < 34 → (i32 c 4 = 0 ∨ (b : Int) < i32 c 12) →
      -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * N + b) ∧ i8 c (76 + 34 * N + b) ≤ 7 + 8 * i32 c 8) :
    T1W1 c f N := by
  obtain ⟨hR, hH, hI, hB, -⟩ := h
  refine ⟨hR, hH, hI, fun e he b hb hc => ?_⟩
  by_cases heN : e = N
  · subst heN; exact hr b hb hc
  · exact hB e (by push_cast at he ⊢; omega) b hb hc

theorem t1_W1_iid0 (h : T1W0 c f N) (hN : N ≤ 4) (h4 : i32 c 4 = 0) : T1W1 c f N :=
  t1_W1_of h hN fun b hb hc => h.2.2.2.2 h4 N (by push_cast; omega) b hb hc

theorem t1_W1_nr0 (h : T1W0 c f N) (hN : N ≤ 4) (h4 : i32 c 4 ≠ 0) (hnr : i32 c 12 ≤ 0) :
    T1W1 c f N :=
  t1_W1_of h hN fun b _ hc => by
    rcases hc with hc | hc
    · exact absurd hc h4
    · omega

theorem t1_W1_row {m : Nat} (h : T1W0 c f N) (hN : N ≤ 4) (hr : T1Row c N m)
    (hm : i32 c 12 ≤ m) : T1W1 c f N :=
  t1_W1_of h hN fun b _ hc => by
    by_cases h4 : i32 c 4 = 0
    · exact h.2.2.2.2 h4 N (by push_cast; omega) b (by omega) (Or.inl h4)
    · rcases hc with hc | hc
      · exact absurd hc h4
      · exact hr b (by omega)

end

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

theorem t1_toInt_i32 (c : List UInt8) (o : Nat) : (BitVec.ofInt 32 (i32 c o)).toInt = i32 c o := by
  simp only [i32, BitVec.ofInt_toInt]

theorem t1_i32_eq0 (c : List UInt8) (o : Nat) : BitVec.ofInt 32 (i32 c o) = 0#32 ↔ i32 c o = 0 := by
  constructor
  · intro h; rw [← t1_toInt_i32, h]; rfl
  · intro h; rw [h]; rfl

theorem t1_zx_i32 (c : List UInt8) (o : Nat) (h : 0 < i32 c o) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (i32 c o)) = BitVec.ofNat 64 (i32 c o).toNat := by
  simp only [i32, BitVec.ofInt_toInt] at h ⊢
  generalize BitVec.ofNat 32 (Nat.ofBytes (List.take 4 (List.drop o c))) = b at h ⊢
  apply BitVec.eq_of_toNat_eq
  have := BitVec.toInt_eq_toNat_cond b
  have hb := b.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  split at this <;> omega

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

section
variable [CodeEnv]

/-- `num_env := b` (offset 44) with `0 ≤ b ≤ 5` keeps `PsInv`. -/
theorem t1_PsInv_wr44 {c : List UInt8} (h : PsInv c) (b : BitVec 32) (h0 : 0 ≤ b.toInt)
    (h5 : b.toInt ≤ 5) : PsInv (wr c 44 4 b.toInt) := by
  obtain ⟨hl, h1, h2, h3, h4, -, h6⟩ := h
  have hL : 44 + 4 ≤ c.length := by omega
  refine ⟨by rw [wr_length _ _ _ _ hL, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [i32_wr]; exact h1
  · simp (disch := omega) only [i32_wr]; exact h2
  · simp (disch := omega) only [i32_wr]; exact h3
  · simp (disch := omega) only [i32_wr]; exact h4
  · rw [i32_wr_same _ _ _ hL]; exact ⟨h0, h5⟩
  · simp (disch := omega) only [i32_wr]; exact h6

theorem t1_B_st44 {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {N : Nat} (h : T1B k Ext x ra t₀ s c f N) (b : BitVec 32)
    (h0 : 0 ≤ b.toInt) (h5 : b.toInt ≤ 5)
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 44) 4 b.toInt)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15) :
    T1B k Ext x ra t₀ s' (wr c 44 4 b.toInt) f N := by
  obtain ⟨⟨hC, ⟨a1, a2, a3, a4, a5, a6, a7⟩, hM⟩, hI, hr, hN, h40, h68⟩ := h
  refine ⟨⟨hC, ⟨by rw [hsp]; exact a1, by rw [hbp]; exact a2, a3,
    t1_PsInv_wr44 a4 b h0 h5, a5, a6, a7⟩, by rw [hm]; exact Fr_c_store hM a4.1 44 4 (by omega) _⟩,
    by rw [h8]; exact hI, by rw [h15]; exact hr, hN, h40, h68⟩

end

section
variable {c f : List UInt8} {N : Nat}

theorem t1_W1_wr44 (h : T1W1 c f N) (hl : c.length = 764) (hN : N ≤ 4) (v : Int) :
    T1W1 (wr c 44 4 v) f N := by
  obtain ⟨hR, hH, hI, hB⟩ := h
  have hB' : IidB c ((N + 1 : Nat) : Int) := by push_cast; exact hB
  have := t1_IidB_wr 44 4 v hB' hl (by omega) (by omega) (by omega) (by omega)
  push_cast at this
  exact ⟨t1_Rng_wr _ _ _ hR hl (by omega) (by omega) (by omega),
    t1_H_wr _ _ _ hH hl (by omega) (by omega) (by omega),
    t1_IidS_wr _ _ _ hI hl (by omega) (by omega), this⟩

/-- `border_position[N + 1] = 31` and `is34bands_old = v` after `num_env = N + 1`: the borders
are fixed. -/
theorem t1_W2_of135 (h : T1W1 c f N) (hl : c.length = 764) (hN : N ≤ 4) (hne : ne c = N + 1)
    (v : Int) : T1W2 (wr (wr c (52 + 4 * (N + 1)) 4 31) 760 4 v) f := by
  obtain ⟨hR, ⟨h0, hm, h31⟩, hI, hB⟩ := h
  have hL : 52 + 4 * (N + 1) + 4 ≤ c.length := by omega
  have hl1 : (wr c (52 + 4 * (N + 1)) 4 31).length = 764 := by rw [wr_length _ _ _ _ hL, hl]
  have hL1 : 760 + 4 ≤ (wr c (52 + 4 * (N + 1)) 4 31).length := by omega
  -- the 32-bit fields after the two stores
  have E : ∀ o, o + 4 ≤ 52 + 4 * (N + 1) ∨ 52 + 4 * (N + 1) + 4 ≤ o → o + 4 ≤ 760 →
      i32 (wr (wr c (52 + 4 * (N + 1)) 4 31) 760 4 v) o = i32 c o := fun o h1 h2 => by
    rw [i32_wr _ _ _ _ _ hL1 (by omega), i32_wr _ _ _ _ _ hL h1]
  have e31 : i32 (wr (wr c (52 + 4 * (N + 1)) 4 31) 760 4 v) (52 + 4 * (N + 1)) = 31 := by
    rw [i32_wr _ _ _ _ _ hL1 (by omega)]
    simp only [i32]
    rw [wr_drop_take_same _ _ _ _ hL]; decide
  have e8 : ∀ j, j < 246 → i8 (wr (wr c (52 + 4 * (N + 1)) 4 31) 760 4 v) j = i8 c j ∨
      j < 76 := fun j hj => by
    by_cases hj' : j < 76
    · exact Or.inr hj'
    · left; rw [i8_wr _ _ _ _ _ hL1 (by omega), i8_wr _ _ _ _ _ hL (by omega)]
  have hne' : ne (wr (wr c (52 + 4 * (N + 1)) 4 31) 760 4 v) = N + 1 := by
    simp only [ne]; rw [E 44 (by omega) (by omega)]; exact hne
  refine ⟨t1_Rng_wr _ _ _ (t1_Rng_wr _ _ _ hR hl (by omega) (by omega) (by omega)) hl1
      (by omega) (by omega) (by omega),
    t1_IidS_wr _ _ _ (t1_IidS_wr _ _ _ hI hl (by omega) (by omega)) hl1 (by omega) (by omega),
    ⟨by rw [hne']; omega, by rw [hne']; omega, ?_, fun e he => ?_, ?_, ?_⟩⟩
  · simp only [bord]; rw [E 52 (by omega) (by omega)]; exact h0
  · rw [hne'] at he
    simp only [bord]
    by_cases heN : e = N
    · subst heN
      rw [E (52 + 4 * e) (by omega) (by omega), show 52 + 4 * (e + 1) = 52 + 4 * (e + 1) from rfl, e31]
      exact h31 e (by omega)
    · rw [E (52 + 4 * e) (by omega) (by omega), E (52 + 4 * (e + 1)) (by omega) (by omega)]
      exact hm e (by omega)
  · rw [hne']; simp only [bord]
    rw [show (((N : Int) + 1).toNat) = N + 1 by omega, e31]
  · rw [hne']
    intro e he b hb hc
    rw [E 4 (by omega) (by omega), E 12 (by omega) (by omega)] at hc
    rw [E 8 (by omega) (by omega)]
    rcases e8 (76 + 34 * e + b) (by omega) with h8 | h8
    · rw [h8]; exact hB e he b hb hc
    · omega

end

end Kraken.Examples.Sbr.Ps

/-- The condition-code hypotheses as propositions. -/
syntax "t1cc" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| t1cc $[$loc]?) => `(tactic| simp only [Kraken.Examples.Sbr.Ps.t1_nc8,
      Kraken.Examples.Sbr.Ps.t1_nc32, Kraken.Examples.Sbr.Ps.t1_nc64, Kraken.Examples.Sbr.Ps.t1_a8,
      Kraken.Examples.Sbr.Ps.t1_a32, Kraken.Examples.Sbr.Ps.t1_a64, Kraken.Examples.Sbr.Ps.t1_be8,
      Kraken.Examples.Sbr.Ps.t1_be32, Kraken.Examples.Sbr.Ps.t1_be64,
      CondCode.interp_l_cmp_toInt32, CondCode.interp_ge_cmp_toInt32, CondCode.interp_g_cmp_toInt32,
      CondCode.interp_le_cmp_toInt32, Kraken.Examples.Sbr.Ps.t1_z, CondCode.interp_nz,
      Kraken.Examples.Sbr.Ps.t1_le_test, Kraken.Examples.Sbr.Ps.t1_zf, decide_eq_true_eq, decide_eq_false_iff_not, beq_iff_eq,
      Bool.not_eq_true', Bool.not_eq_false', beq_eq_false_iff_ne, ne_eq] $[$loc]?)

namespace Kraken.Examples.Sbr.Ps

theorem t1_ofBytes_nat (bs : List UInt8) : Int.ofBytes bs = ((Nat.ofBytes bs : Nat) : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Int.ofBytes bs * 256 + ((b.toNat : Nat) : Int) = ((Nat.ofBytes bs * 256 + b.toNat : Nat) : Int)
    rw [ih]; omega

/-- A 4-byte field as loaded is the signed field as a bit vector (as `PsBlkLLib.rd_i32`). -/
theorem t1_rd_i32 (c : List UInt8) (o : Nat) :
    BitVec.ofInt 32 (rd c o 4) = BitVec.ofInt 32 (i32 c o) := by
  simp only [rd, i32, BitVec.ofInt_toInt, t1_ofBytes_nat]
  rfl

end Kraken.Examples.Sbr.Ps
/-! ## `incl %r` -/

section IncSpec
variable [CodeEnv]

/-- `incl %r` (32-bit; the upper half is zeroed). -/
@[spec low] theorem MachineWP.t1_inc_reg_w32_spec {p : Program} {Q : Unit → MachineData → Prop}
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
      MachineData.set, MachineData.setReg, Effects.All]
    (try simp only [Reg64s.get_low32, Reg64s.set_low32])
    exact hP)

end IncSpec
namespace Kraken.Examples.Sbr.Ps

/-- `&border_position[N + 1]` from `r12d = N + 1`. -/
theorem t1_a135 (a r : BitVec 64) (N : Nat) (h : r.setWidth 32 = BitVec.ofNat 32 (N + 1))
    (hN : N ≤ 4) :
    a + BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 + 52#64
      = a + BitVec.ofNat 64 (52 + 4 * (N + 1)) := by
  rw [h, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem t1_zx32 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Kraken.Examples.Sbr.Ps
namespace Kraken.Examples.Sbr.Ps

/-- No fix-up needed (`border_position[N] ≥ 31`), then `is34bands_old` stored at 760. -/
theorem t1_W2_ofW0 {c f : List UInt8} {N : Nat} (h : T1W0 c f N) (hl : c.length = 764)
    (hne : ne c = N) (h1 : 1 ≤ N) (hN : N ≤ 4) (h31 : 31 ≤ bord c N) (v : Int) :
    T1W2 (wr c 760 4 v) f := by
  have hF : T1Fix c := by
    obtain ⟨_, ⟨h0, hm, h31'⟩, _, hB, _⟩ := h
    refine ⟨by rw [hne]; omega, by rw [hne]; omega, h0, fun e he => hm e (by rw [hne] at he; omega),
      ?_, by rw [hne]; exact hB⟩
    rw [hne, Int.toNat_natCast]; have := h31' N (Nat.le_refl _); omega
  obtain ⟨hR, _, hI, _, _⟩ := t1_W0_760 (v := v) h hl (by omega)
  exact ⟨hR, hI, t1_Fix_wr _ _ _ hF hl (by omega) (by omega)⟩

end Kraken.Examples.Sbr.Ps

namespace Kraken.Examples.Sbr.Ps

/-- `&border_position[e]` from `r12d = e`. -/
theorem t1_aB (a r : BitVec 64) (e : Nat) (h : r.setWidth 32 = BitVec.ofNat 32 e) (he : e ≤ 5) :
    a + BitVec.setWidth 64 (BitVec.setWidth 32 r) * 4#64 + 52#64
      = a + BitVec.ofNat 64 (52 + 4 * e) := by
  rw [h, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem t1_sw32 (N : Nat) :
    BitVec.setWidth 32 (BitVec.ofNat 64 N) = BitVec.ofNat 32 N := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Kraken.Examples.Sbr.Ps
namespace Kraken.Examples.Sbr.Ps

/-- `lea 0x7(,%rdx,8),%edx` of a zero-extended 32-bit load. -/
theorem t1_edx (v : Int) :
    BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 v) * 8#64 + 7#64)))
      = BitVec.ofInt 32 (7 + 8 * (BitVec.ofInt 32 v).toInt) := by
  rw [BitVec.setWidth_32_64_32]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt]
  have e : BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 v) * 8#64 + 7#64)
      = BitVec.ofInt 32 v * 8#32 + 7#32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toInt_add, BitVec.toInt_mul]
  simp only [Int.bmod_add_bmod]
  have : (8#32).toInt = 8 := by decide
  have : (7#32).toInt = 7 := by decide
  simp only [*]
  rw [Int.add_comm, Int.mul_comm]

/-- `rdi = ps + 34 N + 0x4f` (`&iid_par[N][3]`). -/
theorem t1_rdi (a : BitVec 64) (N : Nat) :
    BitVec.setWidth 64 79#64 + (a + (BitVec.ofNat 64 N <<< 5 + BitVec.ofNat 64 N * 2#64))
      = a + BitVec.ofNat 64 (34 * N + 0x4f) := by
  rw [t1_r34]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end Kraken.Examples.Sbr.Ps
namespace Kraken.Examples.Sbr.Ps

/-- A `movzbl` of a byte of `c`, as the signed byte. -/
theorem t1_i8_rd (c : List UInt8) (o : Nat) (h : o < c.length) :
    BitVec.ofInt 8 (rd c o 1) = BitVec.ofNat 8 (c.getD o 0).toNat := by
  have e : (c.drop o).take 1 = [c[o]] := by rw [List.drop_eq_getElem_cons h]; rfl
  simp only [rd, e, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  simp only [Int.ofBytes, List.foldr, Int.zero_mul, Int.zero_add]
  exact BitVec.ofInt_natCast _ _

theorem t1_sw8 (y : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 y)) = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]; omega

theorem t1_sw8b (y : BitVec 8) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 (BitVec.setWidth 32 y)))) = y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]; omega

/-- `sar $7; xor; sub`: the absolute value of a signed byte (`128` for `-128`). -/
theorem t1_abs8 : ∀ y : BitVec 8,
    -(BitVec.setWidth 32 ((y ^^^ y.sshiftRight 7) - y.sshiftRight 7)).toInt ≤ y.toInt
      ∧ y.toInt ≤ (BitVec.setWidth 32 ((y ^^^ y.sshiftRight 7) - y.sshiftRight 7)).toInt := by
  decide

/-- One band of the `iid` check passed. -/
theorem t1_band (c : List UInt8) (o : Nat) (d : BitVec 32) (y : BitVec 8)
    (hd : d = BitVec.ofInt 32 (7 + 8 * i32 c 8)) (hq : i32 c 8 = 0 ∨ i32 c 8 = 1)
    (h : ¬ d.toInt < (BitVec.setWidth 32 ((y ^^^ y.sshiftRight 7) - y.sshiftRight 7)).toInt)
    (hy : y = BitVec.ofNat 8 (c.getD o 0).toNat) :
    -(7 + 8 * i32 c 8) ≤ i8 c o ∧ i8 c o ≤ 7 + 8 * i32 c 8 := by
  subst hd hy
  have := t1_abs8 (BitVec.ofNat 8 (c.getD o 0).toNat)
  have hd' : (BitVec.ofInt 32 (7 + 8 * i32 c 8)).toInt = 7 + 8 * i32 c 8 := by
    rcases hq with h | h <;> rw [h] <;> decide
  simp only [i8]; omega

theorem t1_row_succ {c : List UInt8} {N m : Nat} (hr : T1Row c N m)
    (h : -(7 + 8 * i32 c 8) ≤ i8 c (76 + 34 * N + m) ∧ i8 c (76 + 34 * N + m) ≤ 7 + 8 * i32 c 8) :
    T1Row c N (m + 1) := fun b hb => by
  by_cases hbm : b < m
  · exact hr b hbm
  · have : b = m := by omega
    subst this; exact h

end Kraken.Examples.Sbr.Ps
namespace Kraken.Examples.Sbr.Ps

/-- `cmp %r11, %r10` (`r10 = nr_iid_par - k`, `r11 = b`): the last band. -/
theorem t1_d0 (M k b : Nat) (hM : M < 2 ^ 32) (hk : k < 2 ^ 32) (hb : b < 2 ^ 32) :
    (BitVec.ofNat 64 M - BitVec.ofNat 64 k - BitVec.ofNat 64 b = 0#64) ↔ M = k + b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

end Kraken.Examples.Sbr.Ps
namespace Kraken.Examples.Sbr.Ps

/-- `num_env = N + 1` stored at `ps + 44` (`0x1349` and the next region's `0x14f1`): `q135c`. -/
theorem t1_q135c_of [CodeEnv] {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ s s' : MachineData} {c f : List UInt8} {N : Nat} (hA : T1A k Ext x ra t₀ s c f N)
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 44) 4 (BitVec.ofNat 32 (N + 1)).toInt)
    (h12 : (s'.regs.get64 .r12).setWidth 32 = BitVec.ofNat 32 (N + 1))
    (hbx : s'.regs.get64 .rbx = arg2 t₀)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h8 : s'.regs.get64 .r8 = s.regs.get64 .r8) (h15 : s'.regs.get64 .r15 = s.regs.get64 .r15) :
    q135c k Ext x ra t₀ s' := by
  obtain ⟨hB, hW⟩ := hA
  have hN4 : N ≤ 4 := hB.2.2.2.1
  have hl := t1_B_len hB
  have hbi : (BitVec.ofNat 32 (N + 1)).toInt = (N : Int) + 1 := by
    rw [t1_toInt_ofNat32 _ (by omega)]; omega
  exact ⟨wr c 44 4 (BitVec.ofNat 32 (N + 1)).toInt, f, N,
    ⟨t1_B_st44 hB _ (by omega) (by omega) hm hsp hbp h8 h15, fun hp => t1_W1_wr44 (hW hp) hl hN4 _⟩,
    by show i32 _ 44 = _; rw [i32_wr_same _ _ _ (by omega), hbi], h12, hbx⟩

end Kraken.Examples.Sbr.Ps
namespace Kraken.Examples.Sbr.Ps

/-- `-3(%rdi,%r11,1)` … `(%rdi,%r11,1)`: band `b + j` of row `N` of `iid` (`j = 0..3`). -/
theorem t1_aI (a : BitVec 64) (N b j : Nat) :
    a + BitVec.ofNat 64 (34 * N + 0x4f) + BitVec.ofNat 64 b + BitVec.ofNat 64 (2 ^ 64 - 3 + j)
      = a + BitVec.ofNat 64 (76 + 34 * N + (b + j)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

end Kraken.Examples.Sbr.Ps
