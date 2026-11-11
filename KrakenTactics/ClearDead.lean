/-
Dead-hypothesis elimination.

`clear_dead` keeps the equation hypotheses reachable from the goal through
equation LHS→RHS edges and clears the rest. Symbolic execution emits one
equation per state component per step while a postcondition reads few of
them, and a solver such as `bv_decide` otherwise processes every one.

The analysis is directed, so an equation whose value a later step reads
stays live, and it is closed under rewriting of projection paths, so
components read at different granularities (a whole record field by one
step, a subfield by the next) stay connected.

Nothing here is domain-specific: the input is equation hypotheses and a
goal, the output is the goal with unreachable equations cleared.
-/
import Lean
open Lean Elab Tactic Meta

elab "clear_dead" : tactic => do
  liftMetaTactic1 fun g => g.withContext do
    -- Index the equations by the pointer of their left-hand side.
    let mut eqs : Array (FVarId × Expr × Expr) := #[]
    let mut byLhs : Std.HashMap Expr (FVarId × Expr) := {}
    for d in ← getLCtx do
      if d.isImplementationDetail || d.value?.isSome then continue
      let ty ← instantiateMVars d.type
      if let some (_, l, r) := ty.eq? then
        eqs := eqs.push (d.fvarId, l, r)
        byLhs := byLhs.insert l (d.fvarId, r)
    -- Walk terms reachable from the goal. Each term is visited once; for each
    -- one every prefix of its projection chain is looked up, so an equation
    -- relating a whole component carries a reachable subfield over to the
    -- corresponding subfield of the right-hand side.
    let mut live : Std.HashSet FVarId := {}
    let mut seen : Std.HashSet Expr := {}
    let mut work : Array Expr := #[← instantiateMVars (← g.getType)]
    while work.size > 0 do
      let t := work.back!
      work := work.pop
      if seen.contains t then continue
      seen := seen.insert t
      -- structural children
      match t with
      | .app f a => work := (work.push f).push a
      | .proj _ _ b | .mdata _ b => work := work.push b
      | .lam _ ty b _ | .forallE _ ty b _ => work := (work.push ty).push b
      | .letE _ ty v b _ => work := ((work.push ty).push v).push b
      | _ => pure ()
      -- prefixes of the projection chain rooted at this term
      let mut prefixes : Array Expr := #[t]
      let mut cur := t
      for _ in [0:8] do
        match cur with
        | .app f a => if f.isConst then cur := a; prefixes := prefixes.push cur else break
        | .proj _ _ b => cur := b; prefixes := prefixes.push cur
        | _ => break
      for p in prefixes do
        if let some (fv, rhs) := byLhs[p]? then
          live := live.insert fv
          work := work.push rhs
          -- the same term with this prefix rewritten
          unless p == t do
            work := work.push (t.replace fun e => if e == p then some rhs else none)
    -- Reverse sweep: keep a declaration only if the goal, a live equation, or a
    -- kept later declaration references it. This also drops `let`-bound fold
    -- proofs and stale state variables once nothing reaches them, which is
    -- what keeps the context handed to the solver constant-size.
    let addFVars (used : Std.HashSet FVarId) (e : Expr) : Std.HashSet FVarId := Id.run do
      let mut used := used
      let mut stack := #[e]
      while stack.size > 0 do
        let t := stack.back!; stack := stack.pop
        match t with
        | .fvar id => used := used.insert id
        | .app f a => stack := (stack.push f).push a
        | .proj _ _ b | .mdata _ b => stack := stack.push b
        | .lam _ ty b _ | .forallE _ ty b _ => stack := (stack.push ty).push b
        | .letE _ ty v b _ => stack := ((stack.push ty).push v).push b
        | _ => pure ()
      return used
    let mut used : Std.HashSet FVarId := addFVars {} (← instantiateMVars (← g.getType))
    for (fv, _, _) in eqs do
      if live.contains fv then
        used := addFVars (used.insert fv) (← instantiateMVars (← fv.getType))
    let decls := (← getLCtx).decls.toArray.filterMap id
    let mut dead : Array FVarId := #[]
    for i in [0:decls.size] do
      let d := decls[decls.size - 1 - i]!
      if d.isImplementationDetail then continue
      if used.contains d.fvarId then
        used := addFVars used (← instantiateMVars d.type)
        if let some v := d.value? then used := addFVars used (← instantiateMVars v)
      else
        dead := dead.push d.fvarId
    if dead.isEmpty then return g
    let lctx := dead.foldl (fun (l : LocalContext) fv => l.erase fv) (← getLCtx)
    let ty ← instantiateMVars (← g.getType)
    let g' ← withLCtx lctx (← getLocalInstances) do
      mkFreshExprSyntheticOpaqueMVar ty (← g.getTag)
    g.assign g'
    return g'.mvarId!


