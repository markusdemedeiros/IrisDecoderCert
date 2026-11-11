
/-! ## Frame lemmas -/

omit [CodeEnv] in
/-- The reservation at entry: the callees' area below the frame, the own slot area,
the six saved-register slots (`hW`: the entry's headroom, `CallPre.le`). -/
theorem reserve_frame (k : Nat) {r : BitVec 64} (hW : 0x460 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x460 + k) r ⋆ K
      = Reserve (0x298 + k) (r - 0x1c8#64) ⋆ (0x198 ?@ (r - 0x1c8#64) ⋆ (8 ?@ (r - 0x30#64)
        ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
        ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K))))))) := by
  rw [show 0x460 + k = 0x1c8 + (0x298 + k) by omega, Reserve_split 0x1c8 (0x298 + k) r (by omega)]
  rw [show (0x1c8 ?@ (r - BitVec.ofNat 64 0x1c8) : Mem 64 → Prop) = (0x198 + 0x30) ?@ (r - 0x1c8#64) from rfl,
    Block.split (r - 0x1c8#64) 0x198 0x30 (by decide), show r - 0x1c8#64 + BitVec.ofNat 64 0x198 = r - 0x30#64 by bv_omega]
  rw [show (0x30 ?@ (r - 0x30#64) : Mem 64 → Prop) = (8 + 0x28) ?@ (r - 0x30#64) from rfl,
    Block.split (r - 0x30#64) 8 0x28 (by decide), show r - 0x30#64 + BitVec.ofNat 64 8 = r - 0x28#64 by bv_omega]
  rw [show (0x28 ?@ (r - 0x28#64) : Mem 64 → Prop) = (8 + 0x20) ?@ (r - 0x28#64) from rfl,
    Block.split (r - 0x28#64) 8 0x20 (by decide), show r - 0x28#64 + BitVec.ofNat 64 8 = r - 0x20#64 by bv_omega]
  rw [show (0x20 ?@ (r - 0x20#64) : Mem 64 → Prop) = (8 + 0x18) ?@ (r - 0x20#64) from rfl,
    Block.split (r - 0x20#64) 8 0x18 (by decide), show r - 0x20#64 + BitVec.ofNat 64 8 = r - 0x18#64 by bv_omega]
  rw [show (0x18 ?@ (r - 0x18#64) : Mem 64 → Prop) = (8 + 0x10) ?@ (r - 0x18#64) from rfl,
    Block.split (r - 0x18#64) 8 0x10 (by decide), show r - 0x18#64 + BitVec.ofNat 64 8 = r - 0x10#64 by bv_omega]
  rw [show (0x10 ?@ (r - 0x10#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x10#64) from rfl,
    Block.split (r - 0x10#64) 8 8 (by decide), show r - 0x10#64 + BitVec.ofNat 64 8 = r - 0x8#64 by bv_omega]
  simp only [Std.ExtHashMap.sep_assoc]
  rw [Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x8#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x10#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x18#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x20#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x28#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (8 ?@ (r - 0x30#64)) (Reserve (0x298 + k) (r - 0x1c8#64)),
    Std.ExtHashMap.sep_comm_l (0x198 ?@ (r - 0x1c8#64)) (Reserve (0x298 + k) (r - 0x1c8#64))]

omit [CodeEnv] in
/-- A call's share of the callees' area: the push slot, the callee's `k`, the rest
(`sbr_qmf_synthesis`'s stack arguments and slack) below. -/
theorem call_res (k : Nat) {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat) (K : Mem 64 → Prop) :
    Reserve (0x298 + k) (r₀ - 0x1c8#64) ⋆ K
      = 8 ?@ (r₀ - 0x1c8#64 - 8#64) ⋆ (Reserve k (r₀ - 0x1c8#64 - 8#64)
        ⋆ (0x290 ?@ (r₀ - 0x1c8#64 - BitVec.ofNat 64 (0x298 + k)) ⋆ K)) := by
  have hr : 0x298 + k ≤ (r₀ - 0x1c8#64).toNat := by bv_omega
  generalize r₀ - 0x1c8#64 = r at hr ⊢
  rw [show 0x298 + k = 8 + (k + 0x290) by omega, Reserve_split 8 (k + 0x290) r (by omega),
    Reserve.excess k (k + 0x290) (r - BitVec.ofNat 64 8) (by omega) (by bv_omega),
    Nat.add_sub_cancel_left, BitVec.sub_sub_ofNat]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- A callee's reservation of `k` below the push slot as none and the `k` bytes. -/
theorem res_k0 {k : Nat} {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat) :
    Reserve k (r₀ - 464#64)
      = Reserve 0 (r₀ - 464#64) ⋆ (k - 0) ?@ (r₀ - 464#64 - BitVec.ofNat 64 k) :=
  Reserve.excess 0 k _ (Nat.zero_le _) (by bv_omega)


section OmegaSafeSec
/-! `omega_safe`: `omega`, except that it first refuses, immediately and with a message, any goal
whose target or hypotheses contain `t % m` where `m ≥ 2^32` is a literal (`2^64`,
`18446744073709551616`, …) and `t` is not a literal. That shape (wrap-around facts of 64-bit sums)
is what made omega exhaust memory. Prove such facts as closed lemmas instead, using
`BitVec.toNat_add`/`toNat_ofNat` with explicit `< 2^64` hypotheses. -/

open Lean Meta Elab Tactic

namespace OmegaSafe

/-- A natural/integer literal: `OfNat.ofNat n`, a raw literal, or `a ^ b` of literals. -/
partial def lit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none =>
    match e.int? with
    | some i => if 0 ≤ i then some i.toNat else none
    | none =>
      if let some n := e.rawNatLit? then some n
      else if e.isAppOfArity ``HPow.hPow 6 then
        match lit? (e.getArg! 4), lit? (e.getArg! 5) with
        | some a, some b => if b ≤ 128 then some (a ^ b) else none
        | _, _ => none
      else none

/-- The first subterm `t % m`, `m ≥ 2^32` literal, `t` non-literal. -/
def badMod? (e : Expr) : Option Expr :=
  e.find? fun s =>
    s.isAppOfArity ``HMod.hMod 6 &&
      (match lit? (s.getArg! 5) with
       | some m => decide (2 ^ 32 ≤ m) && (lit? (s.getArg! 4)).isNone
       | none => false)

/-- Throws if the main goal (target or a local hypothesis) contains a bad `%`. -/
def check : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let mut es : Array (Option Name × Expr) := #[(none, ← instantiateMVars (← g.getType))]
  for d in ← getLCtx do
    if !d.isImplementationDetail then
      es := es.push (some d.userName, ← instantiateMVars d.type)
  for (n, e) in es do
    if let some s := badMod? e then
      let w := match n with | some n => m!"hypothesis {n}" | none => m!"the goal"
      throwError "omega_safe: refusing, {w} contains the symbolic big modulus{indentExpr s}\n\
        (risk of omega memory blow-up; prove a closed lemma via BitVec.toNat_add/toNat_ofNat \
        with explicit `< 2^64` facts, or `clear` the hypothesis)"

end OmegaSafe

/-- `omega`, but fails fast on `t % 2^k` (k ≥ 32) with a symbolic `t` in the goal or context. -/
elab "omega_safe" : tactic => do
  OmegaSafe.check
  evalTactic (← `(tactic| omega))

end OmegaSafeSec

/-- The channel pair of `ApplyF` with channel `ch` first, so block proofs can keep `ch` symbolic
(no `ch = 0 ∨ ch = 1` split). Unifies the former `gn_dpair` (GainAsm), `an_dpair` (AnaHf/MapA clean)
and `applyF_dpair` (Env clean). -/
theorem applyF_dpair (y : Args) (t : MachineData) (ch : Nat) (h : ch < 2) (K : Mem 64 → Prop) :
    DScW y.d0 t 0 ⋆ (DScW y.d1 t 1 ⋆ (DArrW t 0 ⋆ (DArrW t 1 ⋆ K)))
      = DScW (y.d ch) t ch ⋆ (DArrW t ch ⋆ (DScW (y.d (1 - ch)) t (1 - ch) ⋆ (DArrW t (1 - ch) ⋆ K))) := by
  obtain rfl | rfl : ch = 0 ∨ ch = 1 := by omega
  · simp only [Args.d, ↓reduceIte, Nat.sub_zero, Nat.one_ne_zero]; ac_rfl
  · simp only [Args.d, ↓reduceIte, Nat.sub_self, Nat.one_ne_zero]; ac_rfl

/-! ## M4b per-object views (D1 layout, synthesis window) -/

omit [CodeEnv] in
/-- D1: the `DArrW` blocks `Y ++ g_temp[0][0..6)` (38936 bytes) and the rest of `g_temp`
(8040) as the objects `Y[0]`, `Y[1]` (19456 bytes each) and `g_temp` (8064). -/
theorem gtemp_rejoin (d : BitVec 64) (K : Mem 64 → Prop) :
    38936 ?@ (d + 0x7930#64) ⋆ (8040 ?@ (d + 0x11148#64) ⋆ K)
      = 19456 ?@ (d + 0x7930#64) ⋆ (19456 ?@ (d + 0xc530#64) ⋆ (8064 ?@ (d + 0x11130#64) ⋆ K)) := by
  have e1 := Block.split (d + 0x7930#64) 19456 19480 (by decide)
  have e2 := Block.split (d + 0xc530#64) 19456 24 (by decide)
  have e3 := Block.split (d + 0x11130#64) 24 8040 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2 e3
  rw [e1, e2, e3]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- `g_temp` and `q_temp` (8064 bytes each, contiguous) as one 16128-byte block. -/
theorem gq_rejoin (d : BitVec 64) (K : Mem 64 → Prop) :
    8064 ?@ (d + 0x11130#64) ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ K) = 16128 ?@ (d + 0x11130#64) ⋆ K := by
  have e1 := Block.split (d + 0x11130#64) 8064 8064 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1
  rw [e1]
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- `synthesis_filterbank_samples` (9216 bytes at `d + 0x80`) and
`analysis_filterbank_samples` (5248 at `d + 0x2480`) as the larger `v0` window of
`sbr_qmf_synthesis` (11264 bytes at `d + 0x80`, see `qmfVSize`) and the rest of the analysis
buffer. -/
theorem a3_overread_carve (d : BitVec 64) (K : Mem 64 → Prop) :
    9216 ?@ (d + 0x80#64) ⋆ (5248 ?@ (d + 0x2480#64) ⋆ K)
      = 11264 ?@ (d + 0x80#64) ⋆ (3200 ?@ (d + 0x2c80#64) ⋆ K) := by
  have e1 := Block.split (d + 0x80#64) 9216 2048 (by decide)
  have e2 := Block.split (d + 0x2480#64) 2048 3200 (by decide)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2
  rw [e1, e2]
  simp only [Std.ExtHashMap.sep_assoc]
