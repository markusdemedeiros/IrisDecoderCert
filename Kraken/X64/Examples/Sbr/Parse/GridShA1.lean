import Kraken.X64.Examples.Sbr.Parse.GridMem

/-!
# `read_sbr_grid`: VARFIX (class 2), the register-only blocks and the paired loop's back edge
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem shA_nz {w : Nat} (d : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result d f) = true ↔ d ≠ 0#w := by
  simp [CondCode.interp, StatusFlags.from_result]

omit [CodeEnv] in
theorem shA_nz_f {w : Nat} (d : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result d f) = false ↔ d = 0#w := by
  simp [CondCode.interp, StatusFlags.from_result]

omit [CodeEnv] in
theorem shA_add2 {x : GArgs} {st : GSt} {a r rsi : BitVec 64} {j : Nat}
    (h : FrLoop x st a r rsi j) : (2#64 + a).toNat = a.toNat + 2 := by
  obtain ⟨hP, -, -, hr, -, hlt, -⟩ := h
  have hn8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
/-- The back edge of the paired loop. -/
theorem shA_loop_next {x : GArgs} {st : GSt} {a r rsi : BitVec 64}
    (h : FrLoop x st a r rsi 2) (hne : r - (2#64 + a) ≠ 0#64) :
    FrLoop x st (2#64 + a) r rsi 0 ∧ a.toNat + 2 < r.toNat := by
  have e := shA_add2 h
  obtain ⟨hP, h2, hsi, hr, hev, hlt, hok⟩ := h
  have hne' : r.toNat ≠ a.toNat + 2 := by
    intro h'; apply hne; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, e, h']; have := a.isLt; simp; omega
  have hlt' : a.toNat + 2 < r.toNat := by omega
  refine ⟨⟨hP, h2, hsi, hr, by omega, by omega, ?_⟩, hlt'⟩
  rw [e]; simpa using hok

omit [CodeEnv] in
/-- The exit of the paired loop. -/
theorem shA_loop_exit {x : GArgs} {st : GSt} {a r rsi : BitVec 64}
    (h : FrLoop x st a r rsi 2) (heq : r - (2#64 + a) = 0#64) :
    FrPre x st ∧ rsi = st.n.setWidth 64 ∧ (2#64 + a).toNat = st.n.toNat / 2 * 2
      ∧ FrOk st (2#64 + a).toNat ∧ a.toNat < r.toNat := by
  have e := shA_add2 h
  obtain ⟨hP, h2, hsi, hr, hev, hlt, hok⟩ := h
  have he : r = 2#64 + a := by bv_omega
  refine ⟨hP, hsi, by rw [← he]; exact hr, by rw [e]; exact hok, hlt⟩

/-- `add $2,%rax; cmp %rax,%r9; jne L4630; jmp L4e6d`: the paired loop's step. -/
theorem blk_L4694 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4694" := by
  cfg_block
  measure_hb "L4694"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hL, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at *
    all_goals have e2 : BitVec.setWidth 64 (Int64.toBitVec 2) = 2#64 := rfl
    all_goals simp only [e2] at *
    · obtain ⟨h1, h2⟩ := shA_loop_next hL ((shA_nz _ _).mp ‹_›)
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      have e := shA_add2 hL
      refine ⟨by decide, ⟨hC, hRB, hdx, hdi, st, h1, hmT⟩, Or.inl ?_⟩
      simp only [Nat.add_eq]; omega
    · obtain ⟨h1, h2, h3, h4, h5⟩ := shA_loop_exit hL ((shA_nz_f _ _).mp ‹_›)
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      refine ⟨by decide, ⟨hC, hRB, hdx, hdi, st, ⟨h1, h2, h3, h4⟩, hmT⟩, Or.inl ?_⟩
      simp only [Nat.add_eq]; omega

omit [CodeEnv] in
/-- `test $0x1,%sil` on `bs_num_env`. -/
theorem shA_par (n : BitVec 32) (hn : n.toNat ≤ 8) (b : Bool) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.setWidth 8 (BitVec.setWidth 64 n) &&& BitVec.setWidth 8 (Int64.toBitVec 1))
      { cf := false, af := b, of := false }) = decide (n.toNat % 2 = 0) := by
  have : n = 0#32 ∨ n = 1#32 ∨ n = 2#32 ∨ n = 3#32 ∨ n = 4#32 ∨ n = 5#32 ∨ n = 6#32
      ∨ n = 7#32 ∨ n = 8#32 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- After the `bs_freq_res` fill: `FrPre` and all flags `bs_freq_res[0..n]` give `SInv`. -/
theorem shA_frPre_sinv {x : GArgs} {st : GSt} (hC : GridC x) (hP : FrPre x st)
    (hF : FrOk st st.n.toNat) : SInv x st :=
  frPre_sinv hC hP hF

/-- `test $0x1,%sil; je L4ea2`: `bs_num_env` even (the fill is complete) or odd (one more). -/
theorem blk_L4e6d (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4e6d" := by
  cfg_block
  measure_hb "L4e6d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, hsi, hax, hok⟩, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at *
    all_goals have hn8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    all_goals have hz := ‹CondCode.z.interp _ = _›
    all_goals rw [hsi, shA_par _ hn8] at hz
    · have hev : st.n.toNat % 2 = 0 := by simpa using hz
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, hRB, st, ⟨shA_frPre_sinv hC hP ?_, hP.2.1⟩, hmT⟩, hdi⟩, by edge_lt⟩
      rw [hax] at hok; intro e he; exact hok e (by omega)
    · have hod : ¬ st.n.toNat % 2 = 0 := by simpa using hz
      refine ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, by omega, hok⟩, hmT⟩, Nat.le_refl _⟩

omit [CodeEnv] in
theorem shA_and (n : BitVec 32) (h : n.toNat ≤ 8) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.setWidth 64 n))) &&& BitVec.setWidth 32 (Int64.toBitVec 2147483646))).toNat
      = n.toNat / 2 * 2 := by
  have : n = 0#32 ∨ n = 1#32 ∨ n = 2#32 ∨ n = 3#32 ∨ n = 4#32 ∨ n = 5#32 ∨ n = 6#32
      ∨ n = 7#32 ∨ n = 8#32 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `r9 = n & ~1`, `rax = 0`: the head of the paired loop. -/
theorem blk_L4621 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4621" := by
  cfg_block
  measure_hb "L4621"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h2, hsi⟩, hm⟩, hn⟩ := hs₀
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at *
    have hn8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have hr9 := shA_and st.n hn8
    simp only [hsi, BitVec.xor_self, BitVec.setWidth_zero] at hr9 ⊢
    refine ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h2, rfl, hr9, rfl, by rw [hr9]; simp; omega, ?_⟩, hmT⟩,
      by rw [hr9]; simp; omega⟩
    intro e he
    simp only [BitVec.toNat_zero, Nat.add_zero, Nat.le_zero] at he
    subst he; exact hP.1.2.2.2.2.2.2.2.2

omit [CodeEnv] in
theorem shA_sext (n : BitVec 32) (h : n.toNat ≤ 8) : n.signExtend 64 = n.setWidth 64 := by
  have : n = 0#32 ∨ n = 1#32 ∨ n = 2#32 ∨ n = 3#32 ∨ n = 4#32 ∨ n = 5#32 ∨ n = 6#32
      ∨ n = 7#32 ∨ n = 8#32 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
/-- `test %rsi,%rsi; jle` on a positive `bs_num_env`: not taken. -/
theorem shA_le_pos (n : BitVec 32) (h1 : 1 ≤ n.toNat) (h : n.toNat ≤ 8) (b : Bool) :
    CondCode.le.interp (StatusFlags.from_result (n.setWidth 64 &&& n.setWidth 64)
      { cf := false, af := b, of := false }) = false := by
  have : n = 1#32 ∨ n = 2#32 ∨ n = 3#32 ∨ n = 4#32 ∨ n = 5#32 ∨ n = 6#32
      ∨ n = 7#32 ∨ n = 8#32 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

omit [CodeEnv] in
/-- `cmp $0x1,%esi` on `bs_num_env`. -/
theorem shA_z1 (n : BitVec 32) (h : n.toNat ≤ 8) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.setWidth 32 (BitVec.setWidth 64 n) - BitVec.setWidth 32 1#64) f)
      = decide (n.toNat = 1) := by
  have : n = 0#32 ∨ n = 1#32 ∨ n = 2#32 ∨ n = 3#32 ∨ n = 4#32 ∨ n = 5#32 ∨ n = 6#32
      ∨ n = 7#32 ∨ n = 8#32 := by bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- `movslq 0x8(%rbx),%rsi`: `bs_num_env`, the cases `n ≤ 0` (not reached), `n = 1`, `n ≥ 2`. -/
theorem blk_L460b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L460b" := by
  cfg_block
  measure_hb "L460b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h4⟩, hm⟩, hn⟩ := hs₀
    have hld := T_loadN hm
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx] at *
    all_goals have hRB := pRB.down
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt] at *
    all_goals have hn8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    all_goals have h1 : 1 ≤ st.n.toNat := hP.2.1
    all_goals simp only [shA_sext _ hn8] at *
    · exfalso
      have hle := ‹CondCode.le.interp _ = true›
      rw [shA_le_pos _ h1 hn8] at hle; exact absurd hle (by decide)
    · have hz := ‹CondCode.z.interp _ = true›
      rw [shA_z1 _ hn8] at hz
      have hz' : st.n.toNat = 1 := by simpa using hz
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, hRB, hdx, hdi, st, ⟨hP, by bv_omega⟩, hmT⟩, by edge_lt⟩
    · have hz := ‹CondCode.z.interp _ = false›
      rw [shA_z1 _ hn8] at hz
      have hz' : st.n.toNat ≠ 1 := by simpa using hz
      refine ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, by omega, rfl⟩, hmT⟩, Nat.le_refl _⟩

end Kraken.Examples.Sbr.Grid
