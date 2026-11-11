/-! ### MapB / MapA helper lemmas (apply-mapb) -/

theorem mapb_j_lt8 {x : Args} {t₀ : MachineData} {ch j : Nat} (hC : ApplyC x t₀) (hch : ch < 2)
    (hj : j < (if ch = 0 then x.d0 else x.d1).nenv) : j < 8 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, h0, -⟩ := h0
  obtain ⟨-, -, -, -, h1, -⟩ := h1
  split at hj <;> omega

theorem mapb_nenv_le8 {x : Args} {t₀ : MachineData} {ch : Nat} (hC : ApplyC x t₀) (hch : ch < 2) :
    (if ch = 0 then x.d0 else x.d1).nenv ≤ 8 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, h0, -⟩ := h0
  obtain ⟨-, -, -, -, h1, -⟩ := h1
  split <;> omega

theorem mapb_add192 (X : BitVec 64) (j : Nat) :
    192#64 + (X + BitVec.ofNat 64 (192 * j)) = X + BitVec.ofNat 64 (192 * (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapb_bounds {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) :
    x.m1 ≤ 48 ∧ x.nq ≤ 5 ∧ x.n1 ≤ 48 ∧ x.kx1 ≤ 32 := by
  obtain ⟨⟨-, h1, -, -, h5, -, -, -, h9, h10, -⟩, -⟩ := hC
  exact ⟨h5, h10, h9, h1⟩

/-- A band of `f_tablenoise`: `kx1 ≤ fN i ≤ fN (i+1) ≤ kx1 + 48`. -/
theorem mapb_noise {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) (i : Nat)
    (hi : i + 1 ≤ x.nq) :
    x.kx1 ≤ u16 x.ftNoise i ∧ u16 x.ftNoise i ≤ u16 x.ftNoise (i + 1) ∧ u16 x.ftNoise (i + 1) ≤ x.kx1 + 48 := by
  obtain ⟨⟨-, -, -, -, h5, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨-, -, hl, -, -, -, -, -, -, hN, -, -, -, hNm, -⟩ := ht hst
  have a := hN i (by omega)
  have b := hN (i + 1) hi
  have c := hNm i (by omega)
  exact ⟨a.1, c, by omega⟩

theorem mapb_nc_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.nc.interp (StatusFlags.from_result (a - b) f) = decide (b.toNat ≤ a.toNat) := by
  have h := CondCode.interp_a_sub a b f hf
  have h' := CondCode.interp_be_sub a b f hf
  rw [CondCode.interp_a] at h
  rw [CondCode.interp_be] at h'
  rw [CondCode.interp_nc, StatusFlags.cf_from_result, hf]
  rw [StatusFlags.cf_from_result, hf] at h h'
  have ⟨h₁, h₂⟩ := BitVec.toNat_sub_cases a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.unsigned_eq]
  by_cases hc : b.toNat ≤ a.toNat
  · rw [h₁ hc]; simp [hc]; omega
  · rw [h₂ (by omega)]; simp [hc]; omega

theorem mapb_c_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.c.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat < b.toNat) := by
  have h := mapb_nc_sub a b f hf
  rw [CondCode.interp_nc] at h
  rw [CondCode.interp_c]
  revert h
  cases (StatusFlags.from_result (a - b) f).cf <;> simp <;> omega

theorem mapb_and3 (c : Nat) : BitVec.ofNat 64 c &&& 3#64 = BitVec.ofNat 64 (c % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem mapb_lens {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) :
    x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨h1, h2, h3, -⟩ := ht hst
  exact ⟨h1, h2, h3⟩

set_option maxRecDepth 20000 in
theorem mapb_take2 (bs : List UInt8) (k : Nat) (h : k + 2 ≤ bs.length) :
    Int.ofBytes ((bs.drop k).take 2) = (((bs.getD k 0).toNat + 256 * (bs.getD (k + 1) 0).toNat : Nat) : Int) := by
  have e : (bs.drop k).take 2 = [bs.getD k 0, bs.getD (k + 1) 0] := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]; omega
    · intro n h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      simp only [List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD]
      rcases n with _ | _ | n
      · simp [List.getElem?_eq_getElem (show k < bs.length by omega)]
      · simp [List.getElem?_eq_getElem (show k + 1 < bs.length by omega)]
      · omega
  rw [e]
  simp only [Int.ofBytes, List.foldr]; push_cast; omega

theorem mapb_ld16 (bs : List UInt8) (i : Nat) (h : 2 * i + 2 ≤ bs.length) (h2 : i < 2 ^ 32) :
    Int.ofBytes (List.take 2 (List.drop (BitVec.ofNat 64 i * 2#64).toNat bs)) =
      (((bs.getD (2 * i) 0).toNat + 256 * (bs.getD (2 * i + 1) 0).toNat : Nat) : Int) := by
  have e : (BitVec.ofNat 64 i * 2#64).toNat = 2 * i := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  rw [e, mapb_take2 bs (2 * i) h]

theorem mapb_ld16' (bs : List UInt8) (i : Nat) (h : 2 * (i + 1) + 2 ≤ bs.length) (h2 : i < 2 ^ 32) :
    Int.ofBytes (List.take 2 (List.drop (((BitVec.ofNat 64 i * 2#64).toNat + 2) % 18446744073709551616) bs)) =
      (((bs.getD (2 * (i + 1)) 0).toNat + 256 * (bs.getD (2 * (i + 1) + 1) 0).toNat : Nat) : Int) := by
  have e : ((BitVec.ofNat 64 i * 2#64).toNat + 2) % 18446744073709551616 = 2 * (i + 1) := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
  rw [e, mapb_take2 bs (2 * (i + 1)) h]

theorem mapb_zx16 (v : Nat) (h : v < 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (v : Int))) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem mapb_zx32 (v : Nat) (h : v < 4294967296) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 v)) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mapb_ld16g (bs : List UInt8) (i : Nat) (c : BitVec 64) (hc : c.toNat = 2) (h : 2 * i + 2 ≤ bs.length)
    (h2 : i < 4294967296) :
    Int.ofBytes (List.take 2 (List.drop (BitVec.ofNat 64 i * c).toNat bs)) =
      (((bs.getD (2 * i) 0).toNat + 256 * (bs.getD (2 * i + 1) 0).toNat : Nat) : Int) := by
  have e : (BitVec.ofNat 64 i * c).toNat = 2 * i := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, hc]; omega
  rw [e, mapb_take2 bs (2 * i) h]

theorem mapb_ld16g' (bs : List UInt8) (i : Nat) (c : BitVec 64) (hc : c.toNat = 2)
    (h : 2 * (i + 1) + 2 ≤ bs.length) (h2 : i < 4294967296) :
    Int.ofBytes (List.take 2 (List.drop (((BitVec.ofNat 64 i * c).toNat + 2) % 18446744073709551616) bs)) =
      (((bs.getD (2 * (i + 1)) 0).toNat + 256 * (bs.getD (2 * (i + 1) + 1) 0).toNat : Nat) : Int) := by
  have e : ((BitVec.ofNat 64 i * c).toNat + 2) % 18446744073709551616 = 2 * (i + 1) := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, hc]; omega
  rw [e, mapb_take2 bs (2 * (i + 1)) h]

theorem mapb_ld16n (bs : List UInt8) (i : Nat) (h : 2 * i + 2 ≤ bs.length) (h2 : i < 4294967296) :
    Int.ofBytes (List.take 2 (List.drop (i % 18446744073709551616 * 2 % 18446744073709551616) bs)) =
      (((bs.getD (2 * i) 0).toNat + 256 * (bs.getD (2 * i + 1) 0).toNat : Nat) : Int) := by
  have e : i % 18446744073709551616 * 2 % 18446744073709551616 = 2 * i := by omega
  rw [e, mapb_take2 bs (2 * i) h]

theorem mapb_ld16n' (bs : List UInt8) (i : Nat) (h : 2 * (i + 1) + 2 ≤ bs.length) (h2 : i < 4294967296) :
    Int.ofBytes (List.take 2 (List.drop ((i % 18446744073709551616 * 2 % 18446744073709551616 + 2) % 18446744073709551616) bs)) =
      (((bs.getD (2 * (i + 1)) 0).toNat + 256 * (bs.getD (2 * (i + 1) + 1) 0).toNat : Nat) : Int) := by
  have e : (i % 18446744073709551616 * 2 % 18446744073709551616 + 2) % 18446744073709551616 = 2 * (i + 1) := by omega
  rw [e, mapb_take2 bs (2 * (i + 1)) h]

theorem mapb_ofInt16 (v : Nat) (h : v < 65536) : (BitVec.ofInt 16 (v : Int)).toNat = v := by
  simp only [BitVec.toNat_ofInt]; omega

theorem mapb_carve (A : BitVec 64) (N o n : Nat) (h : o + n ≤ N) (hN : N ≤ 2 ^ 64) :
    (N ?@ A : Mem 64 → Prop) = o ?@ A ⋆ (n ?@ (A + BitVec.ofNat 64 o) ⋆
      (N - o - n) ?@ (A + BitVec.ofNat 64 o + BitVec.ofNat 64 n)) := by
  obtain ⟨r, rfl⟩ : ∃ r, N = o + n + r := ⟨N - o - n, by omega⟩
  rw [show o + n + r - o - n = r by omega, Nat.add_assoc, Block.split A o (n + r) (by omega),
    Block.split (A + BitVec.ofNat 64 o) n r (by omega)]

theorem mapb_cnt {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (c : Prop) [Decidable c] :
    (if c then x.n0 else x.n1) ≤ 48 := by
  obtain ⟨⟨-, -, -, -, -, -, -, h7, h8, -⟩, -⟩ := hC
  split <;> omega

set_option maxRecDepth 20000 in
theorem mapb_take1 (bs : List UInt8) (k : Nat) (h : k + 1 ≤ bs.length) :
    Int.ofBytes ((bs.drop k).take 1) = (((bs.getD k 0).toNat : Nat) : Int) := by
  have e : (bs.drop k).take 1 = [bs.getD k 0] := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]; omega
    · intro n h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      rcases n with _ | n
      · simp [List.getElem?_eq_getElem (show k < bs.length by omega)]
      · omega
  rw [e]
  simp only [Int.ofBytes, List.foldr]; push_cast; omega

section
open MachineWP in
/-- `inc %r32`: the low half plus one, zero-extended (mapb). -/
@[spec] theorem mapb_inc_reg_w32_spec {p : Program} {Q : Unit → MachineData → Prop}
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
      MachineData.set, MachineData.setReg, Reg64s.get_low32, Reg64s.set_low32, Effects.All]
    exact hP)
end

open Lean Elab Tactic Meta in
/-- Name the anonymous load hyps `ld1, ld2, …` and condition hyps `cc1, …` that `vcgen` leaves. -/
elab "mapb_name" : tactic => do
  let g ← getMainGoal
  let g' ← g.withContext do
    let mut g := g
    let mut nl := 0
    let mut nc := 0
    for d in (← getLCtx) do
      if d.isImplementationDetail then continue
      unless d.userName.hasMacroScopes do continue
      let ty ← instantiateMVars d.type
      if ty.isAppOfArity ``Eq 3 then
        let lhs := ty.getArg! 1
        if lhs.isAppOfArity ``Mem.loadInt 4 then
          nl := nl + 1
          g ← g.rename d.fvarId (Name.mkSimple s!"ld{nl}")
        else if lhs.isAppOfArity ``CondCode.interp 2 then
          nc := nc + 1
          g ← g.rename d.fvarId (Name.mkSimple s!"cc{nc}")
    return g
  replaceMainGoal [g']

open Lean Elab Tactic Meta in
/-- Fail unless the goal's head constant is `n` (syntactically, no unfolding). -/
elab "mapb_head " n:ident : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.consumeMData
  let some c := ty.getAppFn.constName? | throwError "mapb_head: no const head"
  unless c == n.getId || c.toString.endsWith n.getId.toString do throwError "mapb_head: {c}"

set_option maxRecDepth 100000 in
theorem mapb_rsi_off (t : MachineData) (c : Nat) (h : 166176 < c) :
    t.regs.get64 .rsi + BitVec.ofNat 64 c = t.regs.get64 .rsi + 166176#64 + BitVec.ofNat 64 (c - 166176) := by
  have e : (166176#64 + BitVec.ofNat 64 (c - 166176)) = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, e]

set_option maxRecDepth 100000 in
/-- Split an access `rsi + c` inside the table at `sbr + base` (length `len`) as `base`-relative. -/
theorem mapb_off (t : MachineData) (base len c : Nat) (h1 : 166176 + base ≤ c) (h2 : c < 166176 + base + len) :
    t.regs.get64 .rsi + BitVec.ofNat 64 c
      = t.regs.get64 .rsi + 166176#64 + BitVec.ofNat 64 base + BitVec.ofNat 64 (c - 166176 - base) := by
  have e : (166176#64 + BitVec.ofNat 64 base + BitVec.ofNat 64 (c - 166176 - base)) = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc 166176#64, e]

theorem mapb_and3v (v : BitVec 64) : v &&& 3#64 = BitVec.ofNat 64 (v.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem mapb_and3w (v : BitVec 64) : v &&& BitVec.setWidth 64 3#64 = BitVec.ofNat 64 (v.toNat % 4) := by
  rw [show BitVec.setWidth 64 3#64 = 3#64 by rfl, mapb_and3v]


theorem mapb_mul4 (c : BitVec 64) (n : Nat) : (c + BitVec.ofNat 64 n) * 4#64 = c * 4#64 + BitVec.ofNat 64 (4 * n) := by
  rw [BitVec.add_mul]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_mul_mod]; simp only [Nat.mul_comm]

theorem mapb_x48 (n : Nat) : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) <<< 4 = BitVec.ofNat 64 (48 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem mapb_x48' (n : Nat) : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64 + 0#64) <<< 4 = BitVec.ofNat 64 (48 * n) := by
  rw [BitVec.add_zero]; exact mapb_x48 n

section
open MachineWP Lean.Order in
/-- `shrl $i, %r32` for a nonzero masked count (no `if n = 0` over the state) (mapb). -/
theorem mapb_shr32_spec {p : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (asz : Width) (r : Reg64) (i : Int64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let n := i.toBitVec.toNat % 256 % 32
        (n ≠ 0) ⊓ (∀ cf af of : Bool, WP.wp p Q E
          { s with
              regs := s.regs.set64 r ((a.ushiftRight n).setWidth 64),
              status := StatusFlags.from_result (a.ushiftRight n) { s.status with cf, af, of } }) ⦄
      (Directive.instr (.regular asz .W32 (.shr (.reg (.low r .W32)) (.imm8 (.int64 i)))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    refine (MachineWP.shr_reg_imm_w32_spec (p := p) (Q := Q) (E := E) asz r i).le_wp s ?_
    simp only [meet_prop_eq_and] at h
    obtain ⟨hn, hk⟩ := h
    dsimp only at hn hk ⊢
    intro cf af of
    simp only [hn, ite_false]
    exact hk cf af of
end

theorem mapb_foldn (a x : BitVec 64) (c d : Nat) (_h : 2 ^ 63 ≤ d) :
    a + BitVec.ofNat 64 c + x + BitVec.ofNat 64 d = a + BitVec.ofNat 64 ((c + d) % 2 ^ 64) + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapb_h2 (a x : BitVec 64) : a + 311942#64 + x = a + 311940#64 + x + 2#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem mapb_h4 (a x : BitVec 64) : a + 311944#64 + x = a + 311940#64 + x + 4#64 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem mapb_foldr (x : BitVec 64) (c d : Nat) (_h : 2 ^ 63 ≤ d) :
    BitVec.ofNat 64 c + (x + BitVec.ofNat 64 d) = BitVec.ofNat 64 ((c + d) % 2 ^ 64) + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapb_tab {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) (c : Prop) [Decidable c]
    (i : Nat) (hi : i < (if c then x.n0 else x.n1)) :
    x.kx1 ≤ u16 (if c then x.ftLow else x.ftHigh) i ∧
      u16 (if c then x.ftLow else x.ftHigh) i ≤ u16 (if c then x.ftLow else x.ftHigh) (i + 1) ∧
      u16 (if c then x.ftLow else x.ftHigh) (i + 1) ≤ x.kx1 + 48 ∧
      2 * (i + 1) + 2 ≤ (if c then x.ftLow else x.ftHigh).length := by
  obtain ⟨⟨-, -, -, -, h5, -, -, h7, h8, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨l0, l1, -, -, -, -, -, hH, hL, -, -, hHm, hLm, -⟩ := ht hst
  by_cases hc : c
  · simp only [hc, ite_true] at hi ⊢
    have a := hL i (by omega)
    have b := hL (i + 1) (by omega)
    exact ⟨a.1, hLm i hi, by omega, by omega⟩
  · simp only [hc, ite_false] at hi ⊢
    have a := hH i (by omega)
    have b := hH (i + 1) (by omega)
    exact ⟨a.1, Nat.le_of_lt (hHm i hi), by omega, by omega⟩

theorem mapb_high {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) (i : Nat)
    (hi : i < x.n1) :
    x.kx1 ≤ u16 x.ftHigh i ∧ u16 x.ftHigh i < u16 x.ftHigh (i + 1) ∧ u16 x.ftHigh (i + 1) ≤ x.kx1 + 48 := by
  obtain ⟨⟨-, -, -, -, h5, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, hH, -, -, -, hHm, -⟩ := ht hst
  have a := hH i (by omega)
  have b := hH (i + 1) (by omega)
  have c := hHm i hi
  exact ⟨a.1, c, by omega⟩

theorem mapb_sub2 (a c x : BitVec 64) : a + (c + x) - (a + c) = x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add]; omega

theorem mapb_sext (v : Nat) (h : v < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

theorem mapb_sub32 (a b : Nat) (h : a ≤ b) (h2 : b < 2 ^ 32) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 b) - BitVec.setWidth 32 (BitVec.ofNat 64 a))) = BitVec.ofNat 32 (b - a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem mapb_asc (a b : BitVec 64) : a + b - a = b := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_add]; omega

theorem mapb_subk (r x : BitVec 64) (a b c : Nat) (_h : a + b ≤ c) (_h2 : c < 2 ^ 64) :
    r + (BitVec.ofNat 64 c + x) - (r + BitVec.ofNat 64 a + BitVec.ofNat 64 b) = x + BitVec.ofNat 64 (c - a - b) := by
  have e : BitVec.ofNat 64 c = BitVec.ofNat 64 a + BitVec.ofNat 64 b + BitVec.ofNat 64 (c - a - b) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e, show r + (BitVec.ofNat 64 a + BitVec.ofNat 64 b + BitVec.ofNat 64 (c - a - b) + x) = (r + BitVec.ofNat 64 a + BitVec.ofNat 64 b) + (x + BitVec.ofNat 64 (c - a - b)) by ac_rfl]
  exact mapb_asc _ _

theorem mapb_lit2 (x : BitVec 64) (c d : Nat) (_h : c + d < 2 ^ 64) :
    BitVec.ofNat 64 c + (BitVec.ofNat 64 d + x) = BitVec.ofNat 64 (c + d) + x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem mapb_neg32 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (-BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 n))) = BitVec.ofNat 64 ((2 ^ 32 - n) % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_neg, BitVec.toNat_ofNat]
  omega
