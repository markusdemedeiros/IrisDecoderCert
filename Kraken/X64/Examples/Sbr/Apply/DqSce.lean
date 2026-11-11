import Kraken.InfoOff
import Kraken.Rules.HbOptApply
import Kraken.X64.Examples.Sbr.ApplyTable

/-! # `ff_aac_sbr_apply`: blocks of shard `DqSce` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
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
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hm⟩ := T.L6fbe.mp hs
  clear hs
  simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrD] at hm
  dsimp only
  simp only [B.L6fbe]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6fca (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6fca" ⟨"ff_aac_sbr_apply.L6fca", B.L6fca, some "ff_aac_sbr_apply.L6ff7"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, nch, hnch, hm⟩ := T.L6fca.mp hs
  clear hs
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, FrS0] at hm
  dsimp only
  simp only [B.L6fca]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, hrbp, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7044") ?_
  refine ⟨isSome_at L.L7044, ?_, ?_⟩; rw [T.L7044]
  all_goals try edge_step
  refine ⟨hC, ⟨?_, ?_⟩, ?_, 0, nch, by omega, by omega, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, arg1, and_self]; done)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self,
      BitVec.reduceSetWidth]
  · simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, FrM, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd]
    sep_close hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L6ffc (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6ffc" ⟨"ff_aac_sbr_apply.L6ffc", B.L6ffc, some "ff_aac_sbr_apply.L7007"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hax, hm⟩ := T.L6ffc.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn hax
    dsimp only
    simp only [B.L6ffc]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax; dq_simp [] at *; intro hrbp h9 hd hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩)
  all_goals try simp only [hrbp, h9, hd, hax] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSub, BitVec.reduceBEq, dq_bvzero, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7007])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7007 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7007" ⟨"ff_aac_sbr_apply.L7007", B.L7007, some "ff_aac_sbr_apply.L700e"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hax, hm⟩ := T.L7007.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn hax
    dsimp only
    simp only [B.L7007]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax; dq_simp [] at *; intro hrbp h9 hd hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩)
  all_goals try simp only [hrbp, h9, hd, hax] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSub, BitVec.reduceBEq, dq_bvzero, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L700e])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L700e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L700e" ⟨"ff_aac_sbr_apply.L700e", B.L700e, some "ff_aac_sbr_apply.L7020"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hax, hm⟩ := T.L700e.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn hax
    dsimp only
    simp only [B.L700e]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax; dq_simp [] at *; intro hrbp h9 hd hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩)
  all_goals try simp only [hrbp, h9, hd, hax] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSub, BitVec.reduceBEq, dq_bvzero, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7020])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7020 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7020" ⟨"ff_aac_sbr_apply.L7020", B.L7020, some "ff_aac_sbr_apply.L7020_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hm⟩ := T.L7020.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn
    dsimp only
    simp only [B.L7020]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd; dq_simp [] at *; intro hrbp h9 hd)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩)
  all_goals try simp only [hrbp, h9, hd] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7020_1])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrL1, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7020_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7020_1" ⟨"ff_aac_sbr_apply.L7020_1", B.L7020_1, some "ff_aac_sbr_apply.L7020_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hm⟩ := T.L7020_1.mp hs
  clear hs
  simp only [lex_var, hd] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrL1, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn
    dsimp only
    simp only [B.L7020_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd; dq_simp [] at *; intro hrbp h9 hd)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩)
  all_goals try simp only [hrbp, h9, hd] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7020_2])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrL2, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7020_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7020_2" ⟨"ff_aac_sbr_apply.L7020_2", B.L7020_2, some "ff_aac_sbr_apply.L7044"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hm⟩ := T.L7020_2.mp hs
  clear hs
  simp only [lex_var, hd] at hn
  have hw := dq_wf hC.1
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (ch = 0 ∧ nch = 1) ∨ (ch = 0 ∧ nch = 2) ∨ (ch = 1 ∧ nch = 2) := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrL2, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn
    dsimp only
    simp only [B.L7020_2]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd; dq_simp [] at *; intro hrbp h9 hd)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩)
  all_goals try simp only [hrbp, h9, hd] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSub, BitVec.reduceBEq, dq_bvzero, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L74de"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74de") ?_; refine ⟨isSome_at L.L74de, ?_, ?_⟩; rw [T.L74de])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7044])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, 1, 2, by decide, by decide, ?_, ?_⟩)
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrM, FrD, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7044 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7044" ⟨"ff_aac_sbr_apply.L7044", B.L7044, some "ff_aac_sbr_apply.L7044_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hax, hm⟩ := T.L7044.mp hs
  clear hs
  simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrM] at hm
  dsimp only
  simp only [B.L7044]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Int64.toBitVec_neg_ofNat_norm,
      Int64.toBitVec_ofNat_norm, hrbp, h9, hax]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7044_1])
  rotate_left
  · simp only [lex_var, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax]
    obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
    · rw [if_pos (by decide), if_pos (by decide)]; exact Nat.le_refl _
    · rw [if_neg (by decide), if_neg (by decide)]; exact Nat.le_refl _
  refine ⟨hC, ⟨?_, ?_⟩, ?_, ch, nch, hch, hnch, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, arg1, and_self]; done)
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax]
    obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
    all_goals rfl
  · simp only [Mm, TabW_push, FnW_push, AcW_push, OutW_push, FrDq]
    sep_close hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L7044_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7044_1" ⟨"ff_aac_sbr_apply.L7044_1", B.L7044_1, some "ff_aac_sbr_apply.L7070"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hax, hm⟩ := T.L7044_1.mp hs
  clear hs
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  simp only [lex_var, hax] at hn
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hax
    dsimp only
    simp only [B.L7044_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hax; dq_simp [] at *; intro hrbp h9 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hax⟩)
  all_goals try simp only [hrbp, h9, hax] at *
  all_goals try dq_simp [Option.isSome_some] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result] at *
  all_goals try sep_mem hm
  all_goals try simp only [dq_z32, Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try (dq_has_str "ff_aac_sbr_apply.L71e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L71e0") ?_; refine ⟨isSome_at L.L71e0, ?_, ?_⟩; rw [T.L71e0])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7070])
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reduceMod]
  all_goals try dq_lex2
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reduceMod, dA, sbrA, arg1, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, ite_true, ite_false, BitVec.toNat_ofNat, Nat.reduceMod, dA, sbrA, arg1, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try (simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7070 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7070" ⟨"ff_aac_sbr_apply.L7070", B.L7070, some "ff_aac_sbr_apply.L7090"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hm⟩ := T.L7070.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn h14 h12 hj2
    dsimp only
    simp only [B.L7070]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12; dq_simp [] at *; intro hrbp h9 hd h14 h12)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨pj.down⟩; have p5 : PLift _ := ⟨h14⟩; have p6 : PLift _ := ⟨h12⟩)
  all_goals try simp only [hrbp, h9, hd, pj.down, h14, h12] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L70ca"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L70ca") ?_; refine ⟨isSome_at L.L70ca, ?_, ?_⟩; rw [T.L70ca]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.le_refl]; done)
  all_goals try omega
  all_goals try (rename_i v hv; revert hv; sep_mem hm; intro hv; simp only [Option.some.injEq] at hv; subst hv)
  all_goals try (rw [dq_sub_base2, dq_take1 _ _ (by omega), dq_u8bv])
  all_goals try (rename_i v; rw [dq_sub_base2, dq_take1 _ _ (by omega), dq_u8bv] at v; exfalso; first | exact dq_ja_false (x.d0.freqRes.getD j.toNat 0) (hfr0 j.toNat hj2) v | exact dq_ja_false (x.d1.freqRes.getD j.toNat 0) (hfr1 j.toNat hj2) v)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7090 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7090" ⟨"ff_aac_sbr_apply.L7090", B.L7090, some "ff_aac_sbr_apply.L7090_1"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hk48, hm⟩ := T.L7090.mp hs
  clear hs
  have pj : PLift _ := ⟨hj⟩
  have pn : PLift _ := ⟨hn⟩
  clear hj hn
  simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, FnW, FrDq, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  dsimp only
  simp only [B.L7090]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  case vc1 =>
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      have h38 : slot64 s' 0x38 = arg1 t₀ := by
        simp only [slot64, hrbp', BitVec.sub_sub_ofNat, Nat.reduceAdd]
        sep_mem hm'
        simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt, arg1]
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, ?_⟩
      · rw [T.L7090_1]
        refine ⟨hC, ⟨hrsp', hrbp'⟩, ch, nch, hch, hnch, ?_, j, ?_, hj1, hj2, ?_, ?_, ?_, ?_⟩
        · rw [h13', hd]
        · rw [h15', pj.down]
        · rw [h14', h14]
        · rw [h12', h12]
        · rw [hbx']; exact hk48
        · simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, FnW, FrDq, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
          rw [call_res k hSt]
          simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
          sep_close hm'
      · have hn := pn.down
        simp only [lex_var, arg1] at hn ⊢
        rw [h38, h13', h15', hbx', ← hn, h9]; try simp only [arg1]
        first | exact le_refl _ | exact Nat.le_refl _ | dq_lexE

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7090_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7090_1" ⟨"ff_aac_sbr_apply.L7090_1", B.L7090_1, some "ff_aac_sbr_apply.L7090_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hk, hm⟩ := T.L7090_1.mp hs
  clear hs
  have h38 : slot64 s₀ 0x38 = arg1 t₀ := by
    simp only [Mm, FrDq] at hm
    simp only [slot64, hrbp, BitVec.sub_sub_ofNat, Nat.reduceAdd]
    sep_mem hm
    simp only [Option.getD_some, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_toInt]
  simp only [lex_var, hd, h38, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp hd h14 h12 hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L7090_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp hd h14 h12; dq_simp [] at *; intro hrbp hd h14 h12)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨hrbp⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩)
  all_goals try simp only [pj.down, hrbp, hd, h14, h12] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7090_2]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7090_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7090_2" ⟨"ff_aac_sbr_apply.L7090_2", B.L7090_2, some "ff_aac_sbr_apply.L70bf"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hk, hm⟩ := T.L7090_2.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L7090_2]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12; dq_simp [] at *; intro hrbp h9 hd h14 h12)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L70bf]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.le_refl]; done)
  all_goals try omega
  all_goals try (rename_i v hv; revert hv; sep_mem hm; intro hv; simp only [Option.some.injEq] at hv; subst hv)
  all_goals try (rw [dq_sub_base2, dq_take1 _ _ (by omega), dq_u8bv])
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L70bf (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L70bf" ⟨"ff_aac_sbr_apply.L70bf", B.L70bf, some "ff_aac_sbr_apply.L70ca"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L70bf.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L70bf]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L70ca]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 700000 in
theorem blk_L70ca (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L70ca" ⟨"ff_aac_sbr_apply.L70ca", B.L70ca, some "ff_aac_sbr_apply.L70ca_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hm⟩ := T.L70ca.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (first | have hv := hfr0 _ hj2 | have hv := hfr1 _ hj2)
  all_goals simp only [u8] at hv hax
  all_goals rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with hfr | hfr
  all_goals have hax' := hax
  all_goals rw [hfr] at hax'
  all_goals (have phm : PLift _ := ⟨hm⟩; clear hm)
  all_goals
    try dsimp only
    simp only [B.L70ca]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals (have hm := phm.down; clear phm)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax hax'; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax hax')
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩; have p7 : PLift _ := ⟨hax'⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax'] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false', dq_zext32 x.n0 (by omega), dq_zext32 x.n1 (by omega)] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L71b0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L71b0") ?_; refine ⟨isSome_at L.L71b0, ?_, ?_⟩; rw [T.L71b0]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7120"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7120") ?_; refine ⟨isSome_at L.L7120, ?_, ?_⟩; rw [T.L7120]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7140"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7140") ?_; refine ⟨isSome_at L.L7140, ?_, ?_⟩; rw [T.L7140]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L70ca_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, p7.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, p7.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, p7.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.le_refl]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L70ca_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L70ca_1" ⟨"ff_aac_sbr_apply.L70ca_1", B.L70ca_1, some "ff_aac_sbr_apply.L7120"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L70ca_1.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L70ca_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L70bf"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L70bf") ?_; refine ⟨isSome_at L.L70bf, ?_, ?_⟩; rw [T.L70bf]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7090"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7090") ?_; refine ⟨isSome_at L.L7090, ?_, ?_⟩; rw [T.L7090]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7120 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7120" ⟨"ff_aac_sbr_apply.L7120", B.L7120, some "ff_aac_sbr_apply.L7140"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L7120.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L7120]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7166"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7166") ?_; refine ⟨isSome_at L.L7166, ?_, ?_⟩; rw [T.L7166]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L717f"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L717f") ?_; refine ⟨isSome_at L.L717f, ?_, ?_⟩; rw [T.L717f]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.le_refl]; done)
  all_goals try omega
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7140 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7140" ⟨"ff_aac_sbr_apply.L7140", B.L7140, some "ff_aac_sbr_apply.L7166"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L7140.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L7140]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7090"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7090") ?_; refine ⟨isSome_at L.L7090, ?_, ?_⟩; rw [T.L7090]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L70bf"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L70bf") ?_; refine ⟨isSome_at L.L70bf, ?_, ?_⟩; rw [T.L70bf]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7166 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7166" ⟨"ff_aac_sbr_apply.L7166", B.L7166, some "ff_aac_sbr_apply.L717f"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L7166.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L7166]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L717f]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L717f (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L717f" ⟨"ff_aac_sbr_apply.L717f", B.L717f, some "ff_aac_sbr_apply.L71b0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hax, hk, hm⟩ := T.L717f.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  have hwf := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain ⟨hn0, hn1, -⟩ := hwf
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hrbp h9 hd h14 h12 hax hn hj2
  all_goals (try have hv := hfr0 _ hj2); (try have hv := hfr1 _ hj2)
  all_goals
    try dsimp only
    simp only [B.L717f]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12 hax; dq_simp [] at *; intro hrbp h9 hd h14 h12 hax)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨h14⟩; have p5 : PLift _ := ⟨h12⟩; have p6 : PLift _ := ⟨hax⟩)
  all_goals try simp only [pj.down, hrbp, h9, hd, h14, h12, hax] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.reducePow, Nat.reduceMod, decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L70bf"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L70bf") ?_; refine ⟨isSome_at L.L70bf, ?_, ?_⟩; rw [T.L70bf]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7090"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7090") ?_; refine ⟨isSome_at L.L7090, ?_, ?_⟩; rw [T.L7090]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; done)
  all_goals try (dq_simp [pj.down, p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, CstW, lab, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L71b0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L71b0" ⟨"ff_aac_sbr_apply.L71b0", B.L71b0, some "ff_aac_sbr_apply.L71e0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, j, hj, hj1, hj2, h14, h12, hm⟩ := T.L71b0.mp hs
  clear hs
  simp only [lex_var, hd, h9, hj] at hn
  have pj : PLift _ := ⟨hj⟩
  clear hj
  have hw0 := dq_dwf (ch := 0) hC.1 (by decide)
  have hw1 := dq_dwf (ch := 1) hC.1 (by decide)
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hw0 hw1
  obtain ⟨hfl0, hne0, hfr0, -⟩ := hw0
  obtain ⟨hfl1, hne1, hfr1, -⟩ := hw1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn h14 h12 hj2
    dsimp only
    simp only [B.L71b0]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd h14 h12; dq_simp [] at *; intro hrbp h9 hd h14 h12)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨pj.down⟩; have p5 : PLift _ := ⟨h14⟩; have p6 : PLift _ := ⟨h12⟩)
  all_goals try simp only [hrbp, h9, hd, pj.down, h14, h12] at *
  all_goals try dq_simp [] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, dq_cf_sub, dq_zext32 x.d0.nenv (by omega), dq_zext32 x.d1.nenv (by omega),
    BitVec.toNat_ofNat, Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not, Nat.not_lt] at *
  all_goals try simp only [dq_a2] at *
  all_goals try simp only [dq_a1] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L71e0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L71e0") ?_; refine ⟨isSome_at L.L71e0, ?_, ?_⟩; rw [T.L71e0]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7070"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7070") ?_; refine ⟨isSome_at L.L7070, ?_, ?_⟩; rw [T.L7070]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, j + 1#64, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat]
  all_goals try (dq_is_lex; rw [dq_toNat_succ _ (by omega)])
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *; omega)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, p6.down, BitVec.mul_add, BitVec.mul_one, dA, sbrA, arg1]; ac_rfl)
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try exact dq_and1_mul8 _
  all_goals try (rw [dq_toNat_succ _ (by omega)]; omega)
  all_goals try (rw [dq_toNat_succ' _ (by omega)]; omega)
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofNat_eq_ofNat] at *
  all_goals try (simp only [BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.le_refl]; done)
  all_goals try omega
  all_goals try (rename_i _ h9' hlt; have hlt' := dq_ltb _ _ (by omega) hlt; exfalso; have := dq_eq9 _ h9'; omega)
  all_goals (rename_i hlt; have hlt' := dq_ltb j _ (by omega) hlt; rw [dq_toNat_succ' j (by omega)]; omega)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L71e0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L71e0" ⟨"ff_aac_sbr_apply.L71e0", B.L71e0, some "ff_aac_sbr_apply.L71e0_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hm⟩ := T.L71e0.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc,
      BitVec.reduceAdd] at hm hd hn
    dsimp only
    simp only [B.L71e0]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd; dq_simp [] at *; intro hrbp h9 hd)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩)
  all_goals try simp only [hrbp, h9, hd] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, dq_zext32 x.d0.nnoise (by omega),
    dq_zext32 x.d1.nnoise (by omega), dq_zext32 x.nq (by omega)] at *
  all_goals try simp only [dq_test0 x.d0.nnoise (by omega), dq_test0 x.d1.nnoise (by omega), dq_test32 x.nq (by omega),
    dq_z32, Nat.reducePow, decide_eq_true_eq, decide_eq_false_iff_not] at *
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7020"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7020") ?_; refine ⟨isSome_at L.L7020, ?_, ?_⟩; rw [T.L7020]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7226"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7226") ?_; refine ⟨isSome_at L.L7226, ?_, ?_⟩; rw [T.L7226]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L71e0_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Args.d,
    BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, Args.d, BitVec.toNat_ofNat, dA, sbrA, arg1,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L71e0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L71e0_1" ⟨"ff_aac_sbr_apply.L71e0_1", B.L71e0_1, some "ff_aac_sbr_apply.L7226"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L71e0_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L71e0_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L723c"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L723c") ?_; refine ⟨isSome_at L.L723c, ?_, ?_⟩; rw [T.L723c]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7226 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7226" ⟨"ff_aac_sbr_apply.L7226", B.L7226, some "ff_aac_sbr_apply.L723c"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7226.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L7226]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L723c"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L723c") ?_; refine ⟨isSome_at L.L723c, ?_, ?_⟩; rw [T.L723c]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L723c]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L723c (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L723c" ⟨"ff_aac_sbr_apply.L723c", B.L723c, some "ff_aac_sbr_apply.L723c_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L723c.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L723c]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7370"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7370") ?_; refine ⟨isSome_at L.L7370, ?_, ?_⟩; rw [T.L7370]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L723c_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L723c_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L723c_1" ⟨"ff_aac_sbr_apply.L723c_1", B.L723c_1, some "ff_aac_sbr_apply.L7270"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L723c_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L723c_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7270"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7270") ?_; refine ⟨isSome_at L.L7270, ?_, ?_⟩; rw [T.L7270]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7286"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7286") ?_; refine ⟨isSome_at L.L7286, ?_, ?_⟩; rw [T.L7286]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7270 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7270" ⟨"ff_aac_sbr_apply.L7270", B.L7270, some "ff_aac_sbr_apply.L7286"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7270.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L7270]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7286"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7286") ?_; refine ⟨isSome_at L.L7286, ?_, ?_⟩; rw [T.L7286]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7286]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7286 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7286" ⟨"ff_aac_sbr_apply.L7286", B.L7286, some "ff_aac_sbr_apply.L7286_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7286.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7286]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7370"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7370") ?_; refine ⟨isSome_at L.L7370, ?_, ?_⟩; rw [T.L7370]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7286_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7286_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7286_1" ⟨"ff_aac_sbr_apply.L7286_1", B.L7286_1, some "ff_aac_sbr_apply.L72ba"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7286_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L7286_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L72ba"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L72ba") ?_; refine ⟨isSome_at L.L72ba, ?_, ?_⟩; rw [T.L72ba]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L72d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L72d0") ?_; refine ⟨isSome_at L.L72d0, ?_, ?_⟩; rw [T.L72d0]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L72ba (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L72ba" ⟨"ff_aac_sbr_apply.L72ba", B.L72ba, some "ff_aac_sbr_apply.L72d0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L72ba.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L72ba]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L72d0"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L72d0") ?_; refine ⟨isSome_at L.L72d0, ?_, ?_⟩; rw [T.L72d0]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L72d0]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L72d0 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L72d0" ⟨"ff_aac_sbr_apply.L72d0", B.L72d0, some "ff_aac_sbr_apply.L72d0_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L72d0.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L72d0]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7370"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7370") ?_; refine ⟨isSome_at L.L7370, ?_, ?_⟩; rw [T.L7370]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L72d0_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L72d0_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L72d0_1" ⟨"ff_aac_sbr_apply.L72d0_1", B.L72d0_1, some "ff_aac_sbr_apply.L7304"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L72d0_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L72d0_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7304"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7304") ?_; refine ⟨isSome_at L.L7304, ?_, ?_⟩; rw [T.L7304]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L731a"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L731a") ?_; refine ⟨isSome_at L.L731a, ?_, ?_⟩; rw [T.L731a]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7304 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7304" ⟨"ff_aac_sbr_apply.L7304", B.L7304, some "ff_aac_sbr_apply.L731a"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7304.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L7304]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L731a"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L731a") ?_; refine ⟨isSome_at L.L731a, ?_, ?_⟩; rw [T.L731a]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L731a]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L731a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L731a" ⟨"ff_aac_sbr_apply.L731a", B.L731a, some "ff_aac_sbr_apply.L731a_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L731a.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L731a]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7370"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7370") ?_; refine ⟨isSome_at L.L7370, ?_, ?_⟩; rw [T.L7370]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L731a_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L731a_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L731a_1" ⟨"ff_aac_sbr_apply.L731a_1", B.L731a_1, some "ff_aac_sbr_apply.L734a"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L731a_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L731a_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L734a"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L734a") ?_; refine ⟨isSome_at L.L734a, ?_, ?_⟩; rw [T.L734a]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7360"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7360") ?_; refine ⟨isSome_at L.L7360, ?_, ?_⟩; rw [T.L7360]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L734a (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L734a" ⟨"ff_aac_sbr_apply.L734a", B.L734a, some "ff_aac_sbr_apply.L7360"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L734a.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    dsimp only
    simp only [B.L734a]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7360"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7360") ?_; refine ⟨isSome_at L.L7360, ?_, ?_⟩; rw [T.L7360]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7360]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7360 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7360" ⟨"ff_aac_sbr_apply.L7360", B.L7360, some "ff_aac_sbr_apply.L7370"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7360.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7360]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false, Bool.not_eq_true', Bool.not_eq_false'] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7370]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7370 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7370" ⟨"ff_aac_sbr_apply.L7370", B.L7370, some "ff_aac_sbr_apply.L73a1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7370.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain hq | hq : (x.d ch).nnoise = 1 ∨ (x.d ch).nnoise = 2 := by
    have := (dq_dwf (ch := ch) hC.1 (by omega)).2.2.2; omega
  all_goals obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hq
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    simp only [hq] at hax
    try dsimp only
    simp only [B.L7370]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7020"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7020") ?_; refine ⟨isSome_at L.L7020, ?_, ?_⟩; rw [T.L7020]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L73a1"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L73a1") ?_; refine ⟨isSome_at L.L73a1, ?_, ?_⟩; rw [T.L73a1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L73b7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L73b7") ?_; refine ⟨isSome_at L.L73b7, ?_, ?_⟩; rw [T.L73b7]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L73a1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L73a1" ⟨"ff_aac_sbr_apply.L73a1", B.L73a1, some "ff_aac_sbr_apply.L73b7"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L73a1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L73a1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L73b7"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L73b7") ?_; refine ⟨isSome_at L.L73b7, ?_, ?_⟩; rw [T.L73b7]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L73b7]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L73b7 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L73b7" ⟨"ff_aac_sbr_apply.L73b7", B.L73b7, some "ff_aac_sbr_apply.L73b7_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L73b7.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L73b7]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L700e"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L700e") ?_; refine ⟨isSome_at L.L700e, ?_, ?_⟩; rw [T.L700e]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L73b7_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L73b7_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L73b7_1" ⟨"ff_aac_sbr_apply.L73b7_1", B.L73b7_1, some "ff_aac_sbr_apply.L73eb"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L73b7_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L73b7_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L73eb"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L73eb") ?_; refine ⟨isSome_at L.L73eb, ?_, ?_⟩; rw [T.L73eb]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7401"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7401") ?_; refine ⟨isSome_at L.L7401, ?_, ?_⟩; rw [T.L7401]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L73eb (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L73eb" ⟨"ff_aac_sbr_apply.L73eb", B.L73eb, some "ff_aac_sbr_apply.L7401"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L73eb.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L73eb]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7401"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7401") ?_; refine ⟨isSome_at L.L7401, ?_, ?_⟩; rw [T.L7401]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7401]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7401 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7401" ⟨"ff_aac_sbr_apply.L7401", B.L7401, some "ff_aac_sbr_apply.L7401_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7401.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7401]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L700e"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L700e") ?_; refine ⟨isSome_at L.L700e, ?_, ?_⟩; rw [T.L700e]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7401_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7401_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7401_1" ⟨"ff_aac_sbr_apply.L7401_1", B.L7401_1, some "ff_aac_sbr_apply.L7435"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7401_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7401_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7435"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7435") ?_; refine ⟨isSome_at L.L7435, ?_, ?_⟩; rw [T.L7435]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L744b"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L744b") ?_; refine ⟨isSome_at L.L744b, ?_, ?_⟩; rw [T.L744b]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7435 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7435" ⟨"ff_aac_sbr_apply.L7435", B.L7435, some "ff_aac_sbr_apply.L744b"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7435.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7435]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L744b"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L744b") ?_; refine ⟨isSome_at L.L744b, ?_, ?_⟩; rw [T.L744b]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L744b]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L744b (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L744b" ⟨"ff_aac_sbr_apply.L744b", B.L744b, some "ff_aac_sbr_apply.L744b_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L744b.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L744b]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L700e"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L700e") ?_; refine ⟨isSome_at L.L700e, ?_, ?_⟩; rw [T.L700e]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L744b_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L744b_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L744b_1" ⟨"ff_aac_sbr_apply.L744b_1", B.L744b_1, some "ff_aac_sbr_apply.L747f"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L744b_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L744b_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L747f"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L747f") ?_; refine ⟨isSome_at L.L747f, ?_, ?_⟩; rw [T.L747f]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7495"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7495") ?_; refine ⟨isSome_at L.L7495, ?_, ?_⟩; rw [T.L7495]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L747f (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L747f" ⟨"ff_aac_sbr_apply.L747f", B.L747f, some "ff_aac_sbr_apply.L7495"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L747f.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L747f]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7495"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7495") ?_; refine ⟨isSome_at L.L7495, ?_, ?_⟩; rw [T.L7495]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7495]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7495 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7495" ⟨"ff_aac_sbr_apply.L7495", B.L7495, some "ff_aac_sbr_apply.L7495_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7495.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7495]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_zf_sub, dq_zf_sub', dq_cf_sub, dq_sw32, dq_ofNat_eq, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L700e"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L700e") ?_; refine ⟨isSome_at L.L700e, ?_, ?_⟩; rw [T.L700e]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7495_1]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
set_option maxRecDepth 8000 in
theorem blk_L7495_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L7495_1" ⟨"ff_aac_sbr_apply.L7495_1", B.L7495_1, some "ff_aac_sbr_apply.L74de"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, ch, nch, hch, hnch, hd, hnn, hax, hdx, hq0, hm⟩ := T.L7495_1.mp hs
  clear hs
  simp only [lex_var, hd, h9] at hn
  obtain ⟨-, -, -, hnn0⟩ := dq_dwf (ch := 0) hC.1 (by decide)
  obtain ⟨-, -, -, hnn1⟩ := dq_dwf (ch := 1) hC.1 (by decide)
  obtain ⟨-, -, hnq⟩ := dq_wf hC.1
  simp only [Args.d, ite_true, ite_false, Nat.reduceEqDiff] at hnn0 hnn1
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  all_goals
    simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1, Args.d, ite_true, ite_false,
      Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd] at hm hd hn hnn hax
    try dsimp only
    simp only [B.L7495_1]
    try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
    try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
    vcgen
    all_goals try (have hm := p_hm.down; clear p_hm)
    all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals (revert hrbp h9 hd hax hdx; dq_simp [] at *; intro hrbp h9 hd hax hdx)
  all_goals (have p1 : PLift _ := ⟨hrbp⟩; have p2 : PLift _ := ⟨h9⟩; have p3 : PLift _ := ⟨hd⟩; have p4 : PLift _ := ⟨hax⟩; have p5 : PLift _ := ⟨hdx⟩)
  all_goals try simp only [hrbp, h9, hd, hax, hdx] at *
  all_goals try dq_simp [] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl,
    CondCode.interp, StatusFlags.from_result, BitVec.reduceSetWidth, BitVec.reduceSub, BitVec.reduceAdd,
    dq_bvzero, BitVec.reduceBEq, beq_self_eq_true, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_true, Bool.not_false] at *
  all_goals try (simp (config := {decide := true}) only [] at *)
  all_goals try sep_mem hm
  all_goals try (dq_has_str "ff_aac_sbr_apply.L6ffc"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6ffc") ?_; refine ⟨isSome_at L.L6ffc, ?_, ?_⟩; rw [T.L6ffc]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try (dq_has_str "ff_aac_sbr_apply.L7007"; left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L7007") ?_; refine ⟨isSome_at L.L7007, ?_, ?_⟩; rw [T.L7007]; refine ⟨hC, ⟨?_, ?_⟩, ?_, _, nch, hch, hnch, ?_, ?_, ?_⟩)
  all_goals try simp only [lex_var]
  all_goals try dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat]
  all_goals try dq_lex2
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; done)
  all_goals try (dq_simp [p1.down, p2.down, p3.down, p4.down, p5.down, Args.d, BitVec.toNat_ofNat, dA,
    sbrA, arg1]; omega)
  all_goals try omega
  all_goals try decide
  all_goals try ((try dq_simp [] at hm ⊢); simp only [Mm, ApplyF, TabW_push, FnW_push, AcW_push, OutW_push, DScW, TabW, DArrW, FrDq, dA, sbrA, arg1,
      Nat.reduceMul, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals done

end Kraken.Examples.Sbr.Apply
