import Kraken.X64.Examples.Sbr.ApplyTable

/-! # `ff_aac_sbr_apply`: helper lemmas of shard `EnvB` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]

theorem envb_host_anchor : True := trivial

namespace EnvBL

/-! ### Env helper lemmas (apply-env): the `SbrWF` facts of `sbr_env_estimate` -/

/-- The decoder facts the envelope estimation uses, for a started decoder. -/
theorem env_wf {x : Args} {t₀ : MachineData} {ch : Nat} (hC : ApplyC x t₀) (hst : x.start ≠ 0)
    (hch : ch < 2) (hlive : ch ≠ 0 → x.idAac = 1) :
    1 ≤ (x.d ch).nenv ∧ (x.d ch).nenv ≤ 8 ∧ 1 ≤ x.m1 ∧ x.m1 ≤ 48 ∧ x.kx1 ≤ 32 ∧ x.kx1 + x.m1 ≤ 64
    ∧ (∀ j, j ≤ (x.d ch).nenv → u8 (x.d ch).te j ≤ 19)
    ∧ (∀ j, j < (x.d ch).nenv → u8 (x.d ch).te j < u8 (x.d ch).te (j + 1))
    ∧ (∀ j, j ≤ (x.d ch).nenv → u8 (x.d ch).freqRes j ≤ 1)
    ∧ (x.d ch).te.length = 10 ∧ (x.d ch).freqRes.length = 9 := by
  obtain ⟨⟨-, h1, -, h3, h4, -, -, -, -, -, -, -, ht, h0, h1', -⟩, -⟩ := hC
  obtain ⟨-, -, -, -, -, -, hm1, -⟩ := ht hst
  have hd : DWF True (x.d ch) := by
    simp only [Args.d]; split
    · exact h0.mono fun _ => hst
    · exact h1'.mono fun _ => ⟨hst, hlive (by omega)⟩
  obtain ⟨hfl, -, htl, -, hn8, hfr, -, -, -, -, -, -, -, -, -, hlv⟩ := hd
  obtain ⟨hn1, hte, hmono⟩ := hlv trivial
  exact ⟨hn1, hn8, hm1, h4, h1, h3, hte, hmono, hfr, htl, hfl⟩

/-- The band table of envelope `j` (`f_tablelow` or `f_tablehigh`): inside the high band. -/
theorem env_tab {x : Args} {t₀ : MachineData} (hC : ApplyC x t₀) (hst : x.start ≠ 0) (b : Prop)
    [Decidable b] (i : Nat) (hi : i ≤ (if b then x.n0 else x.n1)) :
    x.kx1 ≤ u16 (if b then x.ftLow else x.ftHigh) i ∧ u16 (if b then x.ftLow else x.ftHigh) i ≤ x.kx1 + x.m1
      ∧ (if b then x.n0 else x.n1) ≤ 48 ∧ 2 * (if b then x.n0 else x.n1) + 2 ≤ (if b then x.ftLow else x.ftHigh).length := by
  obtain ⟨⟨-, -, -, -, -, -, -, hn0, hn1, -, -, -, ht, -⟩, -⟩ := hC
  obtain ⟨hl0, hl1, -, -, -, -, -, hH, hL, -⟩ := ht hst
  by_cases hb : b
  · simp only [hb, ite_true] at hi ⊢; exact ⟨(hL i hi).1, (hL i hi).2, by omega, by omega⟩
  · simp only [hb, ite_false] at hi ⊢; exact ⟨(hH i hi).1, (hH i hi).2, by omega, by omega⟩

omit [CodeEnv] in
/-- Carve bound of a `sum_square(X_high[r] + ilb, iub - ilb)` call: row `r < 64`,
`iub = 2 t1 + 2 ≤ 34`. -/
theorem env_carve (r t0 t1 : Nat) (hr : r < 64) (h01 : t0 ≤ t1) (h1 : t1 ≤ 16) :
    16 + 16 * t0 + 320 * r + 8 * (2 * (t1 - t0)) ≤ 20480 := by omega

omit [CodeEnv] in
theorem env_sw {n : Nat} (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem env_lea3_shl4 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 2#64) <<< 4 = BitVec.ofNat 64 (48 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]; omega

omit [CodeEnv] in
theorem env_lea5_shl6 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n + BitVec.ofNat 64 n * 4#64) <<< 6 = BitVec.ofNat 64 (320 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]; omega

omit [CodeEnv] in
set_option maxRecDepth 20000 in
theorem env_take1 (bs : List UInt8) (k : Nat) (h : k + 1 ≤ bs.length) :
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

omit [CodeEnv] in
set_option maxRecDepth 20000 in
theorem env_take2 (bs : List UInt8) (k : Nat) (h : k + 2 ≤ bs.length) :
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

open Lean Elab Tactic Meta in
/-- Name the anonymous load hyps `ld1, ld2, …` and condition hyps `cc1, …` that `vcgen` leaves
(after apply-mapb's `mapb_name`). -/
elab "envb_name" : tactic => do
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
/-- Fail unless the goal's head constant is `n` (after apply-mapb's `mapb_head`). -/
elab "envb_head " n:ident : tactic => do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let ty := ty.consumeMData
  let some c := ty.getAppFn.constName? | throwError "envb_head: no const head"
  unless c == n.getId || c.toString.endsWith n.getId.toString do throwError "envb_head: {c}"

omit [CodeEnv] in
/-- A length-10 byte list as a literal (so `sep_mem` can slice it at literal offsets). -/
theorem env_l10 (l : List UInt8) (h : l.length = 10) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
      l.getD 7 0, l.getD 8 0, l.getD 9 0] := by
  match l, h with
  | [_, _, _, _, _, _, _, _, _, _], _ => rfl

omit [CodeEnv] in
theorem env_l9 (l : List UInt8) (h : l.length = 9) :
    l = [l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0, l.getD 4 0, l.getD 5 0, l.getD 6 0,
      l.getD 7 0, l.getD 8 0] := by
  match l, h with
  | [_, _, _, _, _, _, _, _, _], _ => rfl

omit [CodeEnv] in
theorem env_ob1 (b0 : UInt8) : Int.ofBytes [b0] = ((b0.toNat : Nat) : Int) := by
  simp only [Int.ofBytes, List.foldr]; push_cast; omega

omit [CodeEnv] in
theorem env_u8bv (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 ((b.toNat : Nat) : Int))) = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem env_nc_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
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

omit [CodeEnv] in
theorem env_c_sub {w} (a b : BitVec w) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.c.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat < b.toNat) := by
  have h := env_nc_sub a b f hf
  rw [CondCode.interp_nc] at h
  rw [CondCode.interp_c]
  revert h
  cases (StatusFlags.from_result (a - b) f).cf <;> simp <;> omega

omit [CodeEnv] in
theorem env_sx {n : Nat} (h : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega

omit [CodeEnv] in
theorem env_u8bv' (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 b.toNat)) = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
/-- Peel the first byte off a list cell (so single bytes are exact cells for `sep_mem`). -/
theorem env_vcons2 (b c : UInt8) (cs : List UInt8) (a : BitVec 64) (h : cs.length + 2 ≤ 2 ^ 64) :
    (b :: c :: cs) =@ a = ([b] =@ a ⋆ (c :: cs) =@ (a + 1#64)) :=
  Mem.Val.append_eq [b] (c :: cs) a (a + 1#64) rfl (by simp only [List.length_cons, List.length_nil]; omega)

omit [CodeEnv] in
/-- Re-associate a literal displacement next to the base (`sep_mem` finds regions by base prefix);
used with `(disch := decide)` so that only literal `n` qualify. -/
theorem env_ra (a x : BitVec 64) (n : Nat) (_h : n < 2 ^ 64) :
    a + (x + BitVec.ofNat 64 n) = (a + BitVec.ofNat 64 n) + x := by
  rw [BitVec.add_comm x, BitVec.add_assoc]

omit [CodeEnv] in
theorem env_sub2 (a c x : BitVec 64) : a + (c + x) - (a + c) = x := by
  rw [← BitVec.add_assoc, BitVec.add_comm (a + c) x, BitVec.add_sub_cancel]

omit [CodeEnv] in
theorem env_flag {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 n) == BitVec.zero 32).toNat % 2 ^ 8 = 0 := by
  have : (BitVec.setWidth 32 (BitVec.ofNat 64 n) == BitVec.zero 32) = false := by
    rw [beq_eq_false_iff_ne]
    intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    simp [BitVec.zero] at this
    omega
  rw [this]; rfl

omit [CodeEnv] in
theorem env_flag' {n : Nat} (h1 : 1 ≤ n) (h2 : n < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 n) == BitVec.zero 32).toNat % 256 = 0 := env_flag h1 h2

omit [CodeEnv] in
theorem env_shl4 {n : Nat} (h : n < 2 ^ 28) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) <<< 4) = BitVec.ofNat 64 (16 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

omit [CodeEnv] in
/-- Re-associate a literal displacement that precedes a scaled index. -/
theorem env_ra2 (a x c : BitVec 64) (n : Nat) (_h : n < 2 ^ 64) :
    a + (BitVec.ofNat 64 n + x * c) = (a + BitVec.ofNat 64 n) + x * c := by
  rw [BitVec.add_assoc]

omit [CodeEnv] in
/-- Re-associate `a + (c + x)` (literal `c`) so that `a + c` is a `+`-prefix. -/
theorem env_ra3 (a x : BitVec 64) (n : Nat) (_h : n < 2 ^ 64) :
    a + (BitVec.ofNat 64 n + x) = (a + BitVec.ofNat 64 n) + x := by
  rw [BitVec.add_assoc]

omit [CodeEnv] in
/-- Re-associate `a + (c1 + (x + c2))` (literals) to `(a + (c1 + c2)) + x`. -/
theorem env_ra4 (a x : BitVec 64) (n m : Nat) (_h : n < 2 ^ 64) (_h' : m < 2 ^ 64) :
    a + (BitVec.ofNat 64 n + (x + BitVec.ofNat 64 m)) = (a + BitVec.ofNat 64 (n + m)) + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem env_sub_base (a x : BitVec 64) : (a + x - a).toNat = x.toNat := by
  rw [BitVec.add_comm a x, BitVec.add_sub_cancel]

omit [CodeEnv] in
/-- `test %cl,%cl; cmove`: the zero flag of a byte `b` tested against itself. -/
theorem env_z8 (b : UInt8) (f : StatusFlags.from_result.Remaining) :
    (CondCode.z.interp (StatusFlags.from_result
      (BitVec.setWidth 8 (BitVec.ofNat 64 b.toNat) &&& BitVec.setWidth 8 (BitVec.ofNat 64 b.toNat)) f) = true)
      = (b.toNat = 0) := by
  have h := b.toNat_lt
  rw [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self]
  apply propext
  simp only [beq_iff_eq]
  constructor
  · intro h'
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
    simp [BitVec.zero] at this
    omega
  · intro h'; rw [h']; rfl

omit [CodeEnv] in
/-- Re-base `a + (n + x)` onto a block base `a + b` (`b ≤ n`). -/
theorem env_rb (a x : BitVec 64) (n b : Nat) (hb : b ≤ n) (_hn : n < 2 ^ 64) :
    a + (BitVec.ofNat 64 n + x) = (a + BitVec.ofNat 64 b) + (BitVec.ofNat 64 (n - b) + x) := by
  have : BitVec.ofNat 64 n = BitVec.ofNat 64 b + BitVec.ofNat 64 (n - b) := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [this, BitVec.add_assoc, BitVec.add_assoc]


open Lean Elab Tactic Meta in
/-- Split a `List` literal (`a :: b :: … :: []`). -/
partial def envb_listLit (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.cons 3 then
    (envb_listLit (e.getArg! 2)).map (e.getArg! 1 :: ·)
  else if e.isAppOfArity ``List.nil 1 then some [] else none

open Lean Elab Tactic Meta in
/-- `lex L₁ ≤/< lex L₂` for list literals: skip the syntactically equal prefix with the
`lex_cons_*_cons` lemmas (never unifying differing digits), leave the first differing digit as
`a % 2 ^ 64 < b % 2 ^ 64`; closes `≤` of equal lists. -/
elab "envb_lex_split" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let t := t.consumeMData
  let (isLe, l, r) ←
    if t.isAppOfArity ``LE.le 4 then pure (true, t.getArg! 2, t.getArg! 3)
    else if t.isAppOfArity ``LT.lt 4 then pure (false, t.getArg! 2, t.getArg! 3)
    else throwError "envb_lex_split: not ≤/<"
  unless l.isAppOfArity ``Kraken.lex 1 && r.isAppOfArity ``Kraken.lex 1 do throwError "envb_lex_split: no lex"
  let some L := envb_listLit (l.getArg! 0) | throwError "envb_lex_split: not a literal"
  let some R := envb_listLit (r.getArg! 0) | throwError "envb_lex_split: not a literal"
  let mut i := 0
  for (a, b) in L.zip R do
    if a == b then i := i + 1 else break
  for _ in [0:i] do
    if isLe then
      evalTactic (← `(tactic| refine Kraken.lex_cons_le_cons (by simp only [List.length_cons, List.length_nil]) ?_))
    else
      evalTactic (← `(tactic| refine Kraken.lex_cons_lt_cons (by simp only [List.length_cons, List.length_nil]) ?_))
  if i == L.length then
    if isLe then evalTactic (← `(tactic| exact Kraken.lex_nil_le))
    else throwError "envb_lex_split: equal lists under <"
  else
    if isLe then
      evalTactic (← `(tactic| refine Kraken.lex_cons_le_of_lt (by simp only [List.length_cons, List.length_nil]) ?_))
    else
      evalTactic (← `(tactic| refine Kraken.lex_cons_lt_of_lt (by simp only [List.length_cons, List.length_nil]) ?_))

omit [CodeEnv] in
/-- `add %r15d,%r15d` on a small value (= dqsce's `envb_dbl`). -/
theorem env_dbl (n : Nat) (hn : n < 2 ^ 30) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) + BitVec.setWidth 32 (BitVec.ofNat 64 n))
      = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- The count register of a `sum_square` call, as a byte size (= dqsce's `envb_cnt`). -/
theorem env_cnt (r : BitVec 64) (n : Nat) (hr : r = BitVec.ofNat 64 n) (hn : n < 2 ^ 32) :
    8 * ((BitVec.setWidth 64 (BitVec.setWidth 32 r)).toNat % 2 ^ 32) = 8 * n := by
  subst hr
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega


/-! ### EnvB call-block lemmas (apply-dqsce) -/

omit [CodeEnv] in
/-- `add %r15d,%r15d` on a small value. -/
theorem envb_dbl (n : Nat) (hn : n < 2 ^ 30) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) + BitVec.setWidth 32 (BitVec.ofNat 64 n))
      = BitVec.ofNat 64 (2 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- The count register of a `sum_square` call, as a byte size. -/
theorem envb_cnt (r : BitVec 64) (n : Nat) (hr : r = BitVec.ofNat 64 n) (hn : n < 2 ^ 32) :
    8 * ((BitVec.setWidth 64 (BitVec.setWidth 32 r)).toNat % 2 ^ 32) = 8 * n := by
  subst hr
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem envb_subb (a : BitVec 64) (n : Nat) (h : n < 2 ^ 64) : (a + BitVec.ofNat 64 n - a).toNat = n := by
  rw [BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

omit [CodeEnv] in
/-- A 4-byte unsigned field, zero-extended. -/
theorem envb_zext32 (n : Nat) (h : n < 2 ^ 32) : (BitVec.ofInt 32 (n : Int)).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.ofInt_natCast]
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

end EnvBL
open EnvBL

end Kraken.Examples.Sbr.Apply
