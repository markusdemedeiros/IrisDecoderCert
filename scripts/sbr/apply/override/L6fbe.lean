-- DqSce helpers: the `SbrWF` facts `sbr_dequant` needs, per channel; a normal form

theorem dq_wf {x : Args} {t : MachineData} (h : ApplyC x t) :
    x.n0 ≤ 24 ∧ x.n1 ≤ 48 ∧ x.nq ≤ 5 := by
  obtain ⟨⟨-, -, -, -, -, -, -, h0, h1, hq, -⟩, -⟩ := h
  exact ⟨h0, h1, hq⟩

theorem dq_dwf {x : Args} {t : MachineData} {ch : Nat} (h : ApplyC x t) (hch : ch < 2) :
    (x.d ch).freqRes.length = 9 ∧ (x.d ch).nenv ≤ 8
      ∧ (∀ e, e ≤ (x.d ch).nenv → u8 (x.d ch).freqRes e ≤ 1) ∧ (x.d ch).nnoise ≤ 2 := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h0, h1, -⟩, -⟩ := h
  have hd : ∃ L, DWF L (x.d ch) := by
    rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
    · exact ⟨_, h0⟩
    · exact ⟨_, h1⟩
  obtain ⟨_, hl, -, -, -, hn, hf, hq, -⟩ := hd
  exact ⟨hl, hn, hf, hq⟩

theorem dq_add_zero (a : BitVec 64) : a + 0#64 = a := by simp

theorem dq_add_sub_cancel_left (a b : BitVec 64) : a + b - a = b := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem dq_lit_add (n : Nat) (a b : BitVec 64) :
    BitVec.ofNat 64 n + (a + b) = a + (b + BitVec.ofNat 64 n) := by
  rw [BitVec.add_comm, BitVec.add_assoc]

theorem dq_bvzero (w : Nat) : BitVec.zero w = 0#w := rfl

theorem dq_zext32 (n : Nat) (h : n < 2^32) : (BitVec.ofInt 32 (n:Int)).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.ofInt_natCast]
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem dq_test0 (n : Nat) (h : n < 2^64) :
    (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == BitVec.zero 64) = decide (n = 0) := by
  rw [BitVec.and_self]
  by_cases h0 : n = 0
  · subst h0; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2; apply h0; have := congrArg BitVec.toNat h2; simp at this; omega

theorem dq_test32 (n : Nat) (h : n < 2^32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 n) &&& BitVec.setWidth 32 (BitVec.ofNat 64 n) == BitVec.zero 32)
      = decide (n = 0) := by
  rw [BitVec.and_self]
  by_cases h0 : n = 0
  · subst h0; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2; apply h0; have := congrArg BitVec.toNat h2
    simp [BitVec.toNat_setWidth] at this; omega

theorem dq_add_sub_add (a b c : BitVec 64) : a + b - (a + c) = b - c := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega

theorem dq_ite_get64 {c : Prop} [Decidable c] (a b : Reg64s) (r : Reg64) :
    (if c then a else b).get64 r = if c then a.get64 r else b.get64 r := by split <;> rfl

theorem dq_cf_sub {w : Nat} (a b : BitVec w) :
    ((a - b).unsigned != a.unsigned - b.unsigned) = decide (a.toNat < b.toNat) := by
  simp only [BitVec.unsigned, BitVec.toNat_sub]
  have := a.isLt; have := b.isLt
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]
    intro h2; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]
    have e : 2 ^ w - b.toNat + a.toNat = (a.toNat - b.toNat) + 2 ^ w := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

theorem dq_zf_sub {w : Nat} (a b : BitVec w) : (a - b == BitVec.zero w) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp [BitVec.zero]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2; apply h
    have h3 : a - b = 0#w := by simpa [BitVec.zero] using h2
    rw [← BitVec.sub_add_cancel a b, h3, BitVec.zero_add]

theorem dq_zf_sub' {w : Nat} (a b : BitVec w) : (a - b == 0#w) = decide (a = b) := dq_zf_sub a b

theorem dq_sw32 (n : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp

theorem dq_ofNat_eq {w : Nat} (n c : Nat) :
    (BitVec.ofNat w n = BitVec.ofNat w c) = (n % 2 ^ w = c % 2 ^ w) := by
  apply propext; constructor
  · intro h; simpa using congrArg BitVec.toNat h
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem dq_z32 (n : Nat) :
    (BitVec.ofInt 32 (n : Int) - 0#32 == BitVec.zero 32) = decide (n % 2 ^ 32 = 0) := by
  rw [BitVec.ofInt_natCast, BitVec.sub_zero]
  by_cases h : n % 2 ^ 32 = 0
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2; apply h; have := congrArg BitVec.toNat h2; simpa using this

theorem dq_toNat_succ (x : BitVec 64) (h : x.toNat < 48) : (x + 1).toNat = x.toNat + 1 := by
  rw [BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

theorem dq_toNat_succ' (x : BitVec 64) (h : x.toNat < 48) : (x + 1#64).toNat = x.toNat + 1 :=
  dq_toNat_succ x h

theorem dq_and1_mul8 (x : BitVec 32) : (BitVec.setWidth 64 (x &&& 1#32) * 8#64).toNat ≤ 8 := by
  have h : (x &&& 1#32).toNat ≤ 1 := by
    rw [BitVec.toNat_and]; exact Nat.le_trans Nat.and_le_right (by decide)
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : (x &&& 1#32).toNat < 2 ^ 64)]
  rw [show (8#64 : BitVec 64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

theorem dq_a1 (a j : BitVec 64) (c : Nat) : a + (j + BitVec.ofNat 64 c) = a + BitVec.ofNat 64 c + j := by
  rw [BitVec.add_comm j, BitVec.add_assoc]

theorem dq_a2 (a x y : BitVec 64) (c : Nat) :
    a + (x + (y + BitVec.ofNat 64 c)) = a + BitVec.ofNat 64 c + (x + y) := by
  rw [BitVec.add_assoc a, ← BitVec.add_assoc x, BitVec.add_comm (x + y), ← BitVec.add_assoc]


omit [CodeEnv] in
set_option maxRecDepth 20000 in
theorem dq_take1 (bs : List UInt8) (k : Nat) (h : k + 1 ≤ bs.length) :
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
theorem dq_u8bv (b : UInt8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 ((b.toNat : Nat) : Int))) = BitVec.ofNat 64 b.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := b.toNat_lt
  simp only [BitVec.toNat_setWidth, BitVec.ofInt_natCast, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem dq_sub_base2 (a c j : BitVec 64) : (a + (c + j) - (a + c)).toNat = j.toNat := by
  rw [← BitVec.add_assoc, BitVec.add_comm (a + c) j, BitVec.add_sub_cancel]

omit [CodeEnv] in
/-- `cmp $1,%al; ja` is not taken when the byte is at most 1. -/
theorem dq_ja_false (b : UInt8) (h : b.toNat ≤ 1) :
    ((!(BitVec.setWidth 8 (BitVec.ofNat 64 b.toNat) - 1#8).unsigned !=
          (BitVec.setWidth 8 (BitVec.ofNat 64 b.toNat)).unsigned - (1#8).unsigned &&
      !BitVec.setWidth 8 (BitVec.ofNat 64 b.toNat) - 1#8 == 0#8) = true) → False := by
  have h' : b.toNat = 0 ∨ b.toNat = 1 := by omega
  rcases h' with h' | h' <;> rw [h'] <;> decide

omit [CodeEnv] in
/-- `inc; cmp $9; jne` not taken: the counter was 8. -/
theorem dq_eq9 (j : BitVec 64) (h : (!(j + 1#64 - 9#64 == 0#64)) = false) : j.toNat = 8 := by
  simp only [Bool.not_eq_false', beq_iff_eq] at h
  have h2 := congrArg (· + 9#64) h
  simp only [BitVec.sub_add_cancel, BitVec.zero_add] at h2
  have h3 := congrArg (· - 1#64) h2
  simp only [BitVec.add_sub_cancel] at h3
  subst h3; rfl

omit [CodeEnv] in
/-- `cmp; jae` not taken. -/
theorem dq_ltb (j : BitVec 64) (n : Nat) (hn : n < 2^64)
    (h : (!decide (j.toNat < n % 18446744073709551616)) = false) : j.toNat < n := by
  rw [Nat.mod_eq_of_lt hn] at h
  simpa using h

/-- The block normal form: register reads after writes, index offsets, displacement
literals, constant folding. -/
macro "dq_simp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
      simp only [Reg64s.get64_set64, and_self, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
        BitVec.add_zero, dq_add_zero, Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
        Nat.reduceMul, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceLeDiff, BitVec.reduceSetWidth,
        BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceMul, dq_add_sub_cancel_left, BitVec.reduceEq, dq_lit_add, dq_add_sub_add, dq_ite_get64, ite_self, BitVec.reduceSub, BitVec.toNat_ofNat,
        Option.isSome_some, $ts,*] $[$loc]?)

/-- Close a ground variant comparison (`lex ds ≤/</= lex ds'`, or the edge disjunction). -/
macro "dq_lex" : tactic => `(tactic| first
  | (lex_cmp; all_goals (first | decide | (simp only [Nat.reduceMod]; omega)); done)
  | (left; lex_cmp; all_goals (first | decide | (simp only [Nat.reduceMod]; omega)); done)
  | (right; refine ⟨?_, by decide⟩; lex_cmp; all_goals (first | decide | (simp only [Nat.reduceMod]; omega)); done))

open Lean Elab Tactic Meta in
/-- Succeeds iff the main goal mentions the string literal `l` (guards jump-target tactics:
unifying `label "A"` with `label "B"` evaluates `label` and blows the recursion limit). -/
elab "dq_has_str " l:str : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let s := l.getString
  unless (t.find? fun e => match e with | .lit (.strVal v) => v == s | _ => false).isSome do
    throwError "dq_has_str: no {s}"

open Lean Elab Tactic Meta in
/-- Succeeds iff the main goal mentions `Kraken.lex` (guard for the `lex` closers: their
`exact rfl` on register goals evaluates the machine state and blows the recursion limit). -/
elab "dq_is_lex" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  unless (t.find? fun e => e.isConstOf ``Kraken.lex).isSome do throwError "dq_is_lex: no lex"





open Lean Elab Tactic Meta in
/-- Split a `List` literal (`a :: b :: … :: []`). -/
partial def dq_listLit (e : Expr) : Option (List Expr) :=
  if e.isAppOfArity ``List.cons 3 then
    (dq_listLit (e.getArg! 2)).map (e.getArg! 1 :: ·)
  else if e.isAppOfArity ``List.nil 1 then some [] else none

open Lean Elab Tactic Meta in
/-- `lex L₁ ≤/< lex L₂` for list literals: skip the syntactically equal prefix with the
`lex_cons_*_cons` lemmas (no unification of differing digits), compare the first differing
digit by `omega`. -/
elab "dq_lexE" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let t := t.consumeMData
  let (isLe, l, r) ←
    if t.isAppOfArity ``LE.le 4 then pure (true, t.getArg! 2, t.getArg! 3)
    else if t.isAppOfArity ``LT.lt 4 then pure (false, t.getArg! 2, t.getArg! 3)
    else throwError "dq_lexE: not ≤/<"
  unless l.isAppOfArity ``Kraken.lex 1 && r.isAppOfArity ``Kraken.lex 1 do throwError "dq_lexE: no lex"
  let some L := dq_listLit (l.getArg! 0) | throwError "dq_lexE: not a literal"
  let some R := dq_listLit (r.getArg! 0) | throwError "dq_lexE: not a literal"
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
    else throwError "dq_lexE: equal lists under <"
  else
    if isLe then
      evalTactic (← `(tactic| refine Kraken.lex_cons_le_of_lt (by simp only [List.length_cons, List.length_nil]) ?_))
    else
      evalTactic (← `(tactic| refine Kraken.lex_cons_lt_of_lt (by simp only [List.length_cons, List.length_nil]) ?_))
    evalTactic (← `(tactic| ((try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]); (try rw [Nat.mod_eq_of_lt (a := BitVec.toNat _ + _) (by omega)]); (try rw [Nat.mod_eq_of_lt (a := BitVec.toNat _ + _) (by omega)]); (try rw [Nat.mod_eq_of_lt (by omega)]); (try rw [Nat.mod_eq_of_lt (by omega)]); all_goals omega)))


/-- Variant obligations (`≤`, `<`, or the edge disjunction) by `dq_lexE`. -/
macro "dq_lex2" : tactic => `(tactic| (dq_is_lex; first
  | dq_lexE
  | (left; dq_lexE)
  | (right; exact ⟨rfl, by decide⟩)
  | (right; exact ⟨trivial, by decide⟩)))

theorem blk_L6fbe (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6fbe" ⟨"ff_aac_sbr_apply.L6fbe", B.L6fbe, some "ff_aac_sbr_apply.L6fca"⟩ := by
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hm⟩ := T.L6fbe.mp hs
  clear hs
  simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrD] at hm
  dsimp only
  simp only [B.L6fbe]
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, hrbp]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6fca])
  all_goals try var_step
  refine ⟨hC, ⟨?_, ?_⟩, ?_, 2, Or.inr rfl, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, hrsp, hrbp, h9, arg1, and_self]; done)
  simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrS0, BitVec.reduceSetWidth] at hm ⊢
  try rw [← TabW_push x t₀] at hm
  try rw [← FnW_push e x t₀] at hm
  try rw [← AcW_push x t₀] at hm
  try rw [← OutW_push x t₀] at hm
  sep_close hm
