import Kraken.X64.Examples.Sbr.Parse.GridBase

/-!
# `read_sbr_grid`: the tail's invariants (shard D)

The border chain (`Mono`), the live grid (`Live`), and the steps from the border check to the
return: `TInv` (the `DWF` clauses with `bs_num_noise` and `t_q` not yet written), back to
`DWF` once `bs_num_noise` and `t_q[0..bs_num_noise]` are written.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Grid

theorem shD_mono_step {st : GSt} {j : Nat} (h : Mono st j) (h' : u8 st.te j < u8 st.te (j + 1)) :
    Mono st (j + 1) := by
  intro e he
  by_cases hj : e = j
  · subst hj; exact h'
  · exact h e (by omega)

theorem shD_mono_le {st : GSt} {j : Nat} (h : Mono st j) : ∀ e, e ≤ j → u8 st.te e ≤ u8 st.te j := by
  induction j with
  | zero => intro e he; rw [Nat.le_zero.mp he]; exact Nat.le_refl _
  | succ j ih =>
    intro e he
    have hj : Mono st j := fun e' he' => h e' (by omega)
    have h1 := h j (by omega)
    by_cases hej : e = j + 1
    · subst hej; exact Nat.le_refl _
    · have := ih hj e (by omega); omega

theorem shD_live_of {st : GSt} (h1 : 1 ≤ st.n.toNat) (hm : Mono st st.n.toNat)
    (hb : u8 st.te st.n.toNat ≤ 19) : Live st :=
  ⟨h1, fun e he => Nat.le_trans (shD_mono_le hm e he) hb, hm⟩

/-- `bs_num_noise` and `t_q[0] = t_env[0]` written (`L4efc`). -/
theorem shD_tinv_nq {x : GArgs} {st : GSt} (hS : SInv x st) (hL : Live st) (nn : BitVec 32) :
    TInv x ((st.withNn nn).setTq 0 (bv st.te 0)) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, -, hinv, hy, hte9, -, hidx1, hidx2, hv1, hv2, -⟩, -, hi⟩ := hS
  refine ⟨⟨hfl, hil, htl, ?_, hn8, hfr, Nat.zero_le _, hinv, hy, hte9, ?_, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, hL, hi⟩
  · simp only [GSt.dv, List.length_set] at hql ⊢; exact hql
  · intro q hq
    have hq0 : q = 0 := by simpa using hq
    subst hq0
    simp only [GSt.dv] at hql
    show ((st.tq.set 0 (UInt8.ofBitVec (bv st.te 0))).getD 0 0).toNat ≤ 19
    rw [getD_set_eq st.tq 0 _ (by omega)]
    exact hL.2.1 0 (Nat.zero_le _)

/-- A store to `t_q[j]`, `j ≠ 0`, keeps `TInv`. -/
theorem shD_tinv_setTq {x : GArgs} {st : GSt} (hT : TInv x st) (j : Nat) (hj : j ≠ 0)
    (v : BitVec 8) : TInv x (st.setTq j v) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, -, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2, -⟩, hL, hi⟩ := hT
  refine ⟨⟨hfl, hil, htl, ?_, hn8, hfr, Nat.zero_le _, hinv, hy, hte9, ?_, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, hL, hi⟩
  · simp only [GSt.dv, List.length_set] at hql ⊢; exact hql
  · intro q hq
    have hq0 : q = 0 := by simpa using hq
    subst hq0
    simp only [GSt.dv] at htq
    show ((st.tq.set j (UInt8.ofBitVec v)).getD 0 0).toNat ≤ 19
    rw [getD_set_ne st.tq j 0 _ (Ne.symm hj)]
    exact htq 0 (Nat.le_refl _)

/-- Back to `DWF` once `bs_num_noise` and `t_q[0..bs_num_noise]` are written. -/
theorem shD_dwf_of_tinv {x : GArgs} {st : GSt} (hT : TInv x st) (hnn : st.nn.toNat ≤ 2)
    (hq : ∀ q, q ≤ st.nn.toNat → u8 st.tq q ≤ 19) : DWF False (st.dv x) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, -, hinv, hy, hte9, -, hidx1, hidx2, hv1, hv2, -⟩, -, -⟩ := hT
  exact ⟨hfl, hil, htl, hql, hn8, hfr, hnn, hinv, hy, hte9, hq, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩

/-- `setne` after `cmp b, a` (32-bit). -/
theorem shD_nz_sub (a b : BitVec 32) (cf af of : Bool) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) { cf := cf, af := af, of := of })
      = !(a == b) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ BitVec.zero 32 := by rw [BitVec.zero_eq]; bv_omega
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

/-- `sete` after `cmp b, a` (32-bit). -/
theorem shD_z_sub (a b : BitVec 32) (cf af of : Bool) :
    CondCode.z.interp (StatusFlags.from_result (a - b) { cf := cf, af := af, of := of })
      = (a == b) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ BitVec.zero 32 := by rw [BitVec.zero_eq]; bv_omega
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

/-- A byte flag written into a zeroed register. -/
theorem shD_rl0 (b : Bool) :
    (0#64).replaceLow (BitVec.ofNat 8 b.toNat) = if b then 1#64 else 0#64 := by
  cases b <;> rfl

theorem shD_sw32_64 (n : BitVec 32) : (n.setWidth 64).setWidth 32 = n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem shD_tinv_tq0 {x : GArgs} {st : GSt} (hT : TInv x st) : u8 st.tq 0 ≤ 19 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, htq, -⟩, -, -⟩ := hT
  exact htq 0 (Nat.le_refl _)

/-- `bs_num_noise ∈ {1, 2}` with `t_q[0..bs_num_noise]` bounded: `DWF`. -/
theorem shD_dwf_nq {x : GArgs} {st : GSt} (hT : TInv x st) (hnn : st.nn.toNat ≤ 2)
    (h1 : u8 st.tq 1 ≤ 19) (h2 : st.nn.toNat = 2 → u8 st.tq 2 ≤ 19) : DWF False (st.dv x) := by
  refine shD_dwf_of_tinv hT hnn fun q hq => ?_
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2) with rfl | rfl | rfl
  · exact shD_tinv_tq0 hT
  · exact h1
  · exact h2 (by omega)

theorem shD_sw64_ofNat (n : BitVec 32) : n.setWidth 64 = BitVec.ofNat 64 n.toNat := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `t_q[1] = t_env[c]`, `c ≤ n`, with `bs_num_noise = 2`: back to `DWF`. -/
theorem shD_tq2_fin {x : GArgs} {st : GSt} (h : TQ2 x st) (c : Nat) (hc : c ≤ st.n.toNat) :
    DWF False ((st.setTq 1 (bv st.te c)).dv x) ∧ Live (st.setTq 1 (bv st.te c))
      ∧ (st.setTq 1 (bv st.te c)).i.toNat ≤ x.p8.toNat := by
  obtain ⟨hT, hnn, hq2, -⟩ := h
  have hql : st.tq.length = 3 := hT.1.2.2.2.1
  refine ⟨shD_dwf_nq (shD_tinv_setTq hT 1 (by decide) _) (by simp [hnn]) ?_ ?_, hT.2.1, hT.2.2⟩
  · show ((st.tq.set 1 _).getD 1 0).toNat ≤ 19
    rw [getD_set_eq _ _ _ (by omega)]
    exact hT.2.1.2.1 c hc
  · intro _
    show ((st.tq.set 1 _).getD 2 0).toNat ≤ 19
    rw [getD_set_ne _ _ _ _ (by decide)]
    exact hq2

/-- `test a, a` then `je`/`jne` (32-bit). -/
theorem shD_z_test (a : BitVec 32) (af : Bool) :
    CondCode.z.interp (StatusFlags.from_result a { cf := false, af := af, of := false })
      = (a == 0#32) := by
  simp only [CondCode.interp, StatusFlags.from_result]
  rfl

/-- `cmp b, a` then `jb` (32-bit, unsigned). -/
theorem shD_c_sub (a b : BitVec 32) (af of : Bool) :
    CondCode.c.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (a.toNat < b.toNat) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    rw [BitVec.toNat_sub]; have := a.isLt; have := b.isLt; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    rw [BitVec.toNat_sub]; have := a.isLt; have := b.isLt; omega

/-- `cmp b, a` then `jae`/`cmovae` (32-bit, unsigned). -/
theorem shD_ae_sub (a b : BitVec 32) (af of : Bool) :
    CondCode.ae.interp (StatusFlags.from_result (a - b)
      { cf := (a - b).unsigned != a.unsigned - b.unsigned, af := af, of := of })
      = decide (b.toNat ≤ a.toNat) := by
  have := shD_c_sub a b af of
  simp only [CondCode.interp] at this ⊢
  rw [this]; by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega

end Kraken.Examples.Sbr.Grid
