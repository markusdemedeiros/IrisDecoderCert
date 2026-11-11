
/-! ### MapA helper lemmas (copied from apply-mapb LemHead, renamed mapa_) -/

theorem mapa_j_lt8 {x : Args} {t₀ : MachineData} {ch j : Nat} (hC : ApplyC x t₀) (hch : ch < 2)
    (hj : j < (if ch = 0 then x.d0 else x.d1).nenv) : j < 8 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, h0, -⟩ := h0
  obtain ⟨-, -, -, -, h1, -⟩ := h1
  split at hj <;> omega

theorem mapa_nenv_le8 {x : Args} {t₀ : MachineData} {ch : Nat} (hC : ApplyC x t₀) (hch : ch < 2) :
    (if ch = 0 then x.d0 else x.d1).nenv ≤ 8 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, h0, -⟩ := h0
  obtain ⟨-, -, -, -, h1, -⟩ := h1
  split <;> omega

theorem mapa_add192 (X : BitVec 64) (j : Nat) :
    192#64 + (X + BitVec.ofNat 64 (192 * j)) = X + BitVec.ofNat 64 (192 * (j + 1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapa_bounds {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) :
    x.m1 ≤ 48 ∧ x.nq ≤ 5 ∧ x.n1 ≤ 48 ∧ x.kx1 ≤ 32 := by
  obtain ⟨⟨-, h1, -, -, h5, -, -, -, h9, h10, -⟩, -⟩ := hC
  exact ⟨h5, h10, h9, h1⟩

theorem mapa_n0 {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) : x.n0 ≤ 24 := by
  obtain ⟨⟨-, -, -, -, -, -, -, h8, -⟩, -⟩ := hC
  exact h8

/-- A band of `f_tablenoise`: `kx1 ≤ fN i ≤ fN (i+1) ≤ kx1 + 48`. -/
theorem mapa_noise {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) (i : Nat)
    (hi : i + 1 ≤ x.nq) :
    x.kx1 ≤ u16 x.ftNoise i ∧ u16 x.ftNoise i ≤ u16 x.ftNoise (i + 1) ∧ u16 x.ftNoise (i + 1) ≤ x.kx1 + 48 := by
  obtain ⟨⟨-, -, -, -, h5, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨-, -, hl, -, -, -, -, -, -, hN, -, -, -, hNm, -⟩ := ht hst
  have a := hN i (by omega)
  have b := hN (i + 1) hi
  have c := hNm i (by omega)
  exact ⟨a.1, c, by omega⟩

theorem mapa_tabL {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) (i : Nat)
    (hi : i < x.n0) :
    x.kx1 ≤ u16 x.ftLow i ∧ u16 x.ftLow (i + 1) ≤ x.kx1 + 48 := by
  obtain ⟨⟨-, -, -, -, h5, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, -, hL, -⟩ := ht hst
  have a := hL i (by omega)
  have b := hL (i + 1) hi
  exact ⟨a.1, by omega⟩

theorem mapa_tabH {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) (i : Nat)
    (hi : i < x.n1) :
    x.kx1 ≤ u16 x.ftHigh i ∧ u16 x.ftHigh (i + 1) ≤ x.kx1 + 48 := by
  obtain ⟨⟨-, -, -, -, h5, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, -, hH, -⟩ := ht hst
  have a := hH i (by omega)
  have b := hH (i + 1) hi
  exact ⟨a.1, by omega⟩

theorem mapa_nc_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
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

theorem mapa_c_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.c.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat < b.toNat) := by
  have h := mapa_nc_sub a b f hf
  rw [CondCode.interp_nc] at h
  rw [CondCode.interp_c]
  revert h
  cases (StatusFlags.from_result (a - b) f).cf <;> simp <;> omega

theorem mapa_cf_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    (StatusFlags.from_result (a - b) f).cf = decide (a.toNat < b.toNat) := by
  have h := mapa_c_sub a b f hf
  rwa [CondCode.interp_c] at h

theorem mapa_sbb (b c : UInt8) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 b.toNat))) -
        BitVec.ofNat 8 c.toNat).unsigned !=
      (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 b.toNat)))).unsigned -
        (BitVec.ofNat 8 c.toNat).unsigned)) :
    BitVec.setWidth 64 (BitVec.setWidth 32 2#64) - BitVec.setWidth 64 0#64 -
      BitVec.ofNat 64 (StatusFlags.from_result
        (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 b.toNat))) -
          BitVec.ofNat 8 c.toNat) f).cf.toNat =
    BitVec.ofNat 64 (if b.toNat < c.toNat then 1 else 2) := by
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have ha : (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 b.toNat)))).toNat = b.toNat := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hc' : (BitVec.ofNat 8 c.toNat).toNat = c.toNat := by
    simp only [BitVec.toNat_ofNat]; omega
  rw [mapa_cf_sub _ _ f hf, ha, hc']
  apply BitVec.eq_of_toNat_eq
  by_cases h : b.toNat < c.toNat
  · simp only [h, decide_true, Bool.toNat_true, ite_true, BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat]
  · simp only [h, decide_false, Bool.toNat_false, ite_false, BitVec.toNat_sub, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat]

theorem mapa_x20 (k : Nat) : (BitVec.ofNat 64 k + BitVec.ofNat 64 k * 4#64) * 4#64 = BitVec.ofNat 64 (20 * k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem mapa_and3 (c : Nat) : BitVec.ofNat 64 c &&& 3#64 = BitVec.ofNat 64 (c % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem mapa_lens {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : ¬x.start = 0) :
    x.ftLow.length = 50 ∧ x.ftHigh.length = 98 ∧ x.ftNoise.length = 12 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨h1, h2, h3, -⟩ := ht hst
  exact ⟨h1, h2, h3⟩

set_option maxRecDepth 20000 in
theorem mapa_take2 (bs : List UInt8) (k : Nat) (h : k + 2 ≤ bs.length) :
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

set_option maxRecDepth 20000 in
theorem mapa_take1 (bs : List UInt8) (k : Nat) (h : k + 1 ≤ bs.length) :
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
@[spec] theorem mapa_inc_reg_w32_spec {p : Program} {Q : Unit → MachineData → Prop}
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

theorem mapa_ob2 (b c : UInt8) : Int.ofBytes [b, c] = ((b.toNat + 256 * c.toNat : Nat) : Int) := by
  have := mapa_take2 [b, c] 0 (by simp)
  simpa using this

omit [CodeEnv] in
theorem mapa_u16lt (b c : UInt8) : b.toNat + 256 * c.toNat < 65536 := by
  have := b.toNat_lt; have := c.toNat_lt; omega

omit [CodeEnv] in
theorem mapa_zx32 (v : Nat) (h : v < 4294967296) :
    BitVec.setWidth 64 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem mapa_zx16 (v : Nat) (h : v < 65536) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 v)) = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

open Lean Elab Tactic Meta in
/-- Name the anonymous load hyps `ld1, ld2, …` and condition hyps `cc1, …` that `vcgen` leaves. -/
elab "mapa_name" : tactic => do
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
elab "mapa_head " n:ident : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.consumeMData
  let some c := ty.getAppFn.constName? | throwError "mapa_head: no const head"
  unless c == n.getId || c.toString.endsWith n.getId.toString do throwError "mapa_head: {c}"

set_option maxRecDepth 100000 in
theorem mapa_rsi_off (t : MachineData) (c : Nat) (h : 166176 < c) :
    t.regs.get64 .rsi + BitVec.ofNat 64 c = t.regs.get64 .rsi + 166176#64 + BitVec.ofNat 64 (c - 166176) := by
  have e : (166176#64 + BitVec.ofNat 64 (c - 166176)) = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, e]

set_option maxRecDepth 100000 in
/-- Split an access `rsi + c` inside the table at `sbr + base` (length `len`) as `base`-relative. -/
theorem mapa_off (t : MachineData) (base len c : Nat) (h1 : 166176 + base ≤ c) (h2 : c < 166176 + base + len) :
    t.regs.get64 .rsi + BitVec.ofNat 64 c
      = t.regs.get64 .rsi + 166176#64 + BitVec.ofNat 64 base + BitVec.ofNat 64 (c - 166176 - base) := by
  have e : (166176#64 + BitVec.ofNat 64 base + BitVec.ofNat 64 (c - 166176 - base)) = BitVec.ofNat 64 c := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.add_assoc 166176#64, e]

theorem mapa_and3v (v : BitVec 64) : v &&& 3#64 = BitVec.ofNat 64 (v.toNat % 4) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (3 : Nat) % 2 ^ 64 = 2 ^ 2 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem mapa_and3w (v : BitVec 64) : v &&& BitVec.setWidth 64 3#64 = BitVec.ofNat 64 (v.toNat % 4) := by
  rw [show BitVec.setWidth 64 3#64 = 3#64 by rfl, mapa_and3v]


theorem mapa_mul4 (c : BitVec 64) (n : Nat) : (c + BitVec.ofNat 64 n) * 4#64 = c * 4#64 + BitVec.ofNat 64 (4 * n) := by
  rw [BitVec.add_mul]; congr 1; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_mul_mod]; simp only [Nat.mul_comm]

theorem mapa_x48 (n : Nat) : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) <<< 4 = BitVec.ofNat 64 (48 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem mapa_x192 (n : Nat) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) <<< 6 = BitVec.ofNat 64 (192 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem mapa_x48' (n : Nat) : (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64 + 0#64) <<< 4 = BitVec.ofNat 64 (48 * n) := by
  rw [BitVec.add_zero]; exact mapa_x48 n

omit [CodeEnv] in
theorem mapa_al32 (a : BitVec 64) (c d f : Nat) (ha : isAligned 32 a = true) (hc : c % 32 = 0)
    (hd : d % 32 = 0) (hf : f % 32 = 0) :
    isAligned 32 (a + BitVec.ofNat 64 c + BitVec.ofNat 64 d + BitVec.ofNat 64 f) = true :=
  isAligned_add (by decide) (isAligned_add (by decide) (isAligned_add (by decide) ha
    (by simp only [BitVec.toNat_ofNat]; omega)) (by simp only [BitVec.toNat_ofNat]; omega))
    (by simp only [BitVec.toNat_ofNat]; omega)

theorem mapa_fr0 {x : Args} {t₀ : MachineData} {j : Nat} (hC : ApplyC x t₀) (hj : j < x.d0.nenv) :
    x.d0.freqRes.length = 9 ∧ u8 x.d0.freqRes (j + 1) ≤ 1 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, -, -⟩, -⟩ := hC
  obtain ⟨hl, -, -, -, -, hf, -⟩ := h0
  exact ⟨hl, hf _ (by omega)⟩

theorem mapa_fr1 {x : Args} {t₀ : MachineData} {j : Nat} (hC : ApplyC x t₀) (hj : j < x.d1.nenv) :
    x.d1.freqRes.length = 9 ∧ u8 x.d1.freqRes (j + 1) ≤ 1 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩, -⟩ := hC
  obtain ⟨hl, -, -, -, -, hf, -⟩ := h1
  exact ⟨hl, hf _ (by omega)⟩

theorem mapa_te0 {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) :
    x.d0.te.length = 10 ∧ x.d0.tq.length = 3 ∧ x.d0.nnoise ≤ 2 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, -, -⟩, -⟩ := hC
  obtain ⟨-, -, hl, hq, -, -, hn, -⟩ := h0
  exact ⟨hl, hq, hn⟩

theorem mapa_te1 {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) :
    x.d1.te.length = 10 ∧ x.d1.tq.length = 3 ∧ x.d1.nnoise ≤ 2 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩, -⟩ := hC
  obtain ⟨-, -, hl, hq, -, -, hn, -⟩ := h1
  exact ⟨hl, hq, hn⟩

theorem mapa_cswap (a : BitVec 64) (n c : Nat) :
    a + BitVec.ofNat 64 n + BitVec.ofNat 64 c = a + BitVec.ofNat 64 c + BitVec.ofNat 64 n := by
  rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 n), ← BitVec.add_assoc]

theorem mapa_cz (n : Nat) (h : n < 256) (f : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 n)) &&&
      BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 n))) f) = decide (n = 0) := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self]
  rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 n)) = BitVec.ofNat 64 n by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega]
  by_cases hn : n = 0
  · subst hn; rfl
  · rw [decide_eq_false hn, beq_eq_false_iff_ne]
    intro hc; apply hn
    have := congrArg BitVec.toNat hc
    simp only [BitVec.zero_eq, BitVec.toNat_ofNat, BitVec.toNat_zero] at this
    omega

theorem mapa_in1 (t m : Nat) (h : t < m) (hm : m < 2 ^ 64) :
    (0#64 - BitVec.ofNat 64 t - 1 - (0#64 - BitVec.ofNat 64 m)).toNat = m - t - 1 := by
  simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem mapa_in0 (t m : Nat) (h : t < m) (hm : m < 2 ^ 64) :
    (0#64 - BitVec.ofNat 64 t - (0#64 - BitVec.ofNat 64 m)).toNat = m - t := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega


theorem mapa_dsub (a : BitVec 64) (c c1 c2 c3 n : Nat) (h : c = c1 + c2 + c3) :
    a + (BitVec.ofNat 64 c + BitVec.ofNat 64 n) - (a + BitVec.ofNat 64 c1 + BitVec.ofNat 64 c2 + BitVec.ofNat 64 c3)
      = BitVec.ofNat 64 n := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapa_beq0 (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0#64) = decide (n = 0) := by
  by_cases hn : n = 0
  · subst hn; rfl
  · rw [decide_eq_false hn, beq_eq_false_iff_ne]
    intro hc; apply hn
    have := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat] at this
    omega


theorem mapa_ra (a : BitVec 64) (c c1 c2 c3 n : Nat) (h : c = c1 + c2 + c3) :
    a + (BitVec.ofNat 64 c + BitVec.ofNat 64 n)
      = a + BitVec.ofNat 64 c1 + BitVec.ofNat 64 c2 + BitVec.ofNat 64 c3 + BitVec.ofNat 64 n := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega
theorem mapa_bsplit (l : List UInt8) (a : BitVec 64) (j : Nat) (hj : j < l.length) (hw : l.length ≤ 2 ^ 64) :
    l =@ a = l.take j =@ a ⋆ ([l.getD j 0] =@ (a + BitVec.ofNat 64 j) ⋆
      l.drop (j + 1) =@ (a + BitVec.ofNat 64 j + 1#64)) := by
  have e : l = l.take j ++ ([l.getD j 0] ++ l.drop (j + 1)) := by
    have h1 := (List.take_append_drop j l).symm
    rw [List.drop_eq_getElem_cons hj] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]; exact h1
  have hl : (l.take j).length = j := by simp only [List.length_take]; omega
  rw [show (l =@ a) = ((l.take j ++ ([l.getD j 0] ++ l.drop (j + 1))) =@ a) from by rw [← e]]
  rw [Mem.Val.append_eq (l.take j) _ a (a + BitVec.ofNat 64 j) (by rw [hl])
      (by simp only [List.length_append, List.length_take, List.length_cons, List.length_nil, List.length_drop]; omega),
    Mem.Val.append_eq [l.getD j 0] _ (a + BitVec.ofNat 64 j) (a + BitVec.ofNat 64 j + 1#64) (by simp)
      (by simp only [List.length_cons, List.length_nil, List.length_drop]; omega)]


omit [CodeEnv] in
theorem mapa_ob1 (b : UInt8) : Int.ofBytes [b] = ((b.toNat : Nat) : Int) := by
  simp only [Int.ofBytes, List.foldr]; push_cast; omega

theorem mapa_split2 (l : List UInt8) (a : BitVec 64) (h : 2 ≤ l.length) (hw : l.length ≤ 2 ^ 64) :
    l =@ a = [l.getD 0 0, l.getD 1 0] =@ a ⋆ l.drop 2 =@ (a + 2#64) := by
  have e : l = [l.getD 0 0, l.getD 1 0] ++ l.drop 2 := by
    match l, h with
    | x :: y :: r, _ => rfl
  conv => lhs; rw [e]
  exact Mem.Val.append_eq [l.getD 0 0, l.getD 1 0] (l.drop 2) a (a + 2#64) rfl
    (by simp only [List.length_cons, List.length_nil, List.length_drop]; omega)

theorem mapa_take2z (l : List UInt8) (h : 2 ≤ l.length) :
    Int.ofBytes (l.take 2) = (((l.getD 0 0).toNat + 256 * (l.getD 1 0).toNat : Nat) : Int) := by
  have := mapa_take2 l 0 (by omega)
  simpa using this

theorem mapa_dsub2 (a x : BitVec 64) (c c1 c2 : Nat) (h : c = c1 + c2) :
    a + (BitVec.ofNat 64 c + x) - (a + BitVec.ofNat 64 c1 + BitVec.ofNat 64 c2) = x := by
  subst h
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mapa_idx2 (i : Nat) (h : i < 1000) : (BitVec.ofNat 64 i * 2#64 + 2#64).toNat = 2 * (i + 1) := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem mapa_idx2' (i : Nat) (h : i < 1000) : (BitVec.ofNat 64 i * 2#64).toNat = 2 * i := by
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem mapa_u16ld (l : List UInt8) (k : Nat) (h : k + 2 ≤ l.length) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (Int.ofBytes (List.take 2 (List.drop k l))))) =
      BitVec.ofNat 64 ((l.getD k 0).toNat + 256 * (l.getD (k + 1) 0).toNat) := by
  rw [mapa_take2 l k h, BitVec.ofInt_natCast]
  have := mapa_u16lt (l.getD k 0) (l.getD (k + 1) 0)
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mapa_u16ld' (l : List UInt8) (k : Nat) (h : k + 2 ≤ l.length) :
    BitVec.ofInt 16 (Int.ofBytes (List.take 2 (List.drop k l))) =
      BitVec.ofNat 16 ((l.getD k 0).toNat + 256 * (l.getD (k + 1) 0).toNat) := by
  rw [mapa_take2 l k h, BitVec.ofInt_natCast]

omit [CodeEnv] in
theorem mapa_sw16u (b c : UInt8) :
    BitVec.setWidth 16 (BitVec.ofNat 64 (b.toNat + 256 * c.toNat)) = BitVec.ofNat 16 (b.toNat + 256 * c.toNat) := by
  have := mapa_u16lt b c
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem mapa_zx16u (b c : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 16 (b.toNat + 256 * c.toNat))) =
      BitVec.ofNat 64 (b.toNat + 256 * c.toNat) :=
  mapa_zx16 _ (mapa_u16lt b c)

omit [CodeEnv] in
theorem mapa_zx64u (b c : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 (b.toNat + 256 * c.toNat))) =
      BitVec.ofNat 64 (b.toNat + 256 * c.toNat) := by
  have := mapa_u16lt b c
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem mapa_lex_eq {a b : Nat} {xs ys : List Nat} (hab : a = b) (hl : xs.length = ys.length)
    (h : Kraken.lex xs < Kraken.lex ys) : Kraken.lex (a :: xs) < Kraken.lex (b :: ys) := by
  subst hab; exact Kraken.lex_cons_lt_cons hl h

theorem mapa_lex_le_eq {a b : Nat} {xs ys : List Nat} (hab : a = b) (hl : xs.length = ys.length)
    (h : Kraken.lex xs ≤ Kraken.lex ys) : Kraken.lex (a :: xs) ≤ Kraken.lex (b :: ys) := by
  subst hab; exact Kraken.lex_cons_le_cons hl h

theorem mapa_zf4 (A B : Nat) (hA : A < 2 ^ 64) (hB : B ≤ A) (f : StatusFlags.from_result.Remaining) :
    (StatusFlags.from_result (BitVec.ofNat 64 A - BitVec.ofNat 64 B &&& BitVec.setWidth 64 3#64) f).zf =
      decide ((A - B) % 4 = 0) := by
  rw [StatusFlags.zf_from_result, mapa_and3w, BitVec.zero_eq]
  have h : (BitVec.ofNat 64 A - BitVec.ofNat 64 B).toNat = A - B := by
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  rw [h, mapa_beq0 _ (by omega)]

/-- Channel-generic `mapa_fr0`/`mapa_fr1` (no-split MapA blocks). -/
theorem mapa_frc {x : Args} {t₀ : MachineData} {j ch : Nat} (hC : ApplyC x t₀) (hch : ch < 2) (hj : j < (x.d ch).nenv) :
    (x.d ch).freqRes.length = 9 ∧ u8 (x.d ch).freqRes (j + 1) ≤ 1 := by
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  · exact mapa_fr0 hC hj
  · exact mapa_fr1 hC hj

/-- Channel-generic `mapa_te0`/`mapa_te1` (no-split MapA blocks). -/
theorem mapa_tec {x : Args} {t₀ : MachineData} {ch : Nat} (hC : ApplyC x t₀) (hch : ch < 2) :
    (x.d ch).te.length = 10 ∧ (x.d ch).tq.length = 3 ∧ (x.d ch).nnoise ≤ 2 := by
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  · exact mapa_te0 hC
  · exact mapa_te1 hC
