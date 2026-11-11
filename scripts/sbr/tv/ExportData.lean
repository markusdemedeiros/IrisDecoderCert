import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.SessionBin.Top

/-! Translation validation of the data: print every constant byte list that the two top
theorems place at a label.

Walks the trusted closures of `ff_aac_sbr_apply_linked` and `SessionBin.sbr_session_safe` (as
`Tcb.lean`: statements and definition bodies, not proofs) and collects each `bs =@ a`
(`Mem.Val a bs`) whose address `a` is `lab "X"` or `lab "X" + k` (k a closed term), unfolding
the (non-recursive) definitions applied to a label on the way (`cell4`, `c4`, …). A closed `bs` is
evaluated and printed as

  `V <label> <offset> <hex bytes> <declaration>`

and a `bs` that mentions a label or a variable as

  `S <label> <offset> <declaration>` (symbolic contents: a link-time or run-time value such as
  a GOT slot, a jump table entry or a table pointer; offset `?` when not constant).

`tv_data.py` (part D) compares the `V` lines with the objects. Output: `$SBR_TV_DATA`
(set by `tv.sh`). -/

open Lean Meta

namespace SbrTvData

/-- Constants reachable from `root`'s type through types and definition bodies. -/
partial def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let some ci0 := env.find? root | return {}
  let mut todo : Array Name := ci0.type.getUsedConstants
  let mut seen : NameSet := {}
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.defnInfo d) => todo := todo ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | some (.opaqueInfo d) => todo := todo ++ d.type.getUsedConstants ++ d.value.getUsedConstants
    | some (.inductInfo i) =>
        todo := todo ++ i.type.getUsedConstants
        for c in i.ctors do todo := todo.push c
    | some ci => todo := todo ++ ci.type.getUsedConstants
    | none => pure ()
  return seen

def isLab (n : Name) : Bool := n == ``Kraken.Examples.Sbr.lab

/-- Unfold a reducible closed definition at the head of `e`. -/
def unfoldHead? (env : Environment) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.defnInfo d) =>
      if getReducibilityStatusCore env c == .reducible && !d.value.hasLooseBVars then
        some ((d.value.instantiateLevelParams d.levelParams us).beta e.getAppArgs)
      else none
    | _ => none
  | _ => none

/-- `lab "X"` (any instance argument) to `X`, looking through address abbreviations
(`abbrev JT := lab "read_sbr_grid_jt"`). -/
partial def labName? (env : Environment) (e : Expr) (fuel : Nat := 8) : Option String :=
  let e := e.consumeMData
  if isLab e.getAppFn.constName then
    match e.getAppArgs.back? with
    | some (.lit (.strVal s)) => some s
    | _ => none
  else if fuel = 0 then none
  else match unfoldHead? env e with
    | some e' => labName? env e' (fuel - 1)
    | none => none

/-- The reducible definitions that mention `lab`, directly or through each other. -/
def labAbbrevs (env : Environment) (decls : List Name) : NameSet := Id.run do
  let mut s : NameSet := {}
  let mut changed := true
  while changed do
    changed := false
    for c in decls do
      if s.contains c then continue
      if let some (.defnInfo d) := env.find? c then
        if getReducibilityStatusCore env c == .reducible &&
            (d.value.find? fun x => isLab x.constName || s.contains x.constName).isSome then
          s := s.insert c; changed := true
  return s

def mentionsLabIn (la : NameSet) (e : Expr) : Bool :=
  (e.find? fun x => isLab x.constName || la.contains x.constName).isSome

unsafe def evalBytes (bs : Expr) : MetaM (List UInt8) :=
  evalExpr (List UInt8) (mkApp (mkConst ``List [0]) (mkConst ``UInt8)) bs

unsafe def evalBV64 (k : Expr) : MetaM Nat := do
  let v ← evalExpr (BitVec 64) (mkApp (mkConst ``BitVec) (mkNatLit 64)) k
  return v.toNat

def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s)

/-- May an application of `c` to a label be unfolded (so that a constant placed through a
definition taking the address as a parameter is seen)? Any non-recursive definition. -/
def unfoldable (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo d) =>
      !isLab c && !d.value.hasLooseBVars && d.value.approxDepth.toNat < 40 &&
        !(d.value.find? fun x => match x.constName? with
          | some n => n.isStr && (n.getString! == "brecOn" || n == ``WellFounded.fix)
          | none => false).isSome
  | _ => false

structure St where
  la : NameSet := {}
  done : Std.HashSet Expr := {}
  out : Array String := #[]
  seen : Std.HashSet String := {}

unsafe def visit (env : Environment) (decl : Name) (fuel : Nat) (e : Expr) :
    StateT St MetaM Unit := do
  if fuel = 0 then return
  if (← get).done.contains e then return
  modify fun st => { st with done := st.done.insert e }
  let mentionsLab := mentionsLabIn (← get).la
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.constName == ``Mem.Val && args.size ≥ 3 then
      let a := args[1]!.consumeMData
      let bs := args[2]!
      -- the address: `lab "X"` or `lab "X" + k`
      let (lname, off?) : Option String × Option Expr :=
        match labName? env a with
        | some s => (some s, none)
        | none =>
          if a.isAppOfArity ``HAdd.hAdd 6 then
            match labName? env a.getAppArgs[4]! with
            | some s => (some s, some a.getAppArgs[5]!)
            | none => (none, none)
          else (none, none)
      if let some l := lname then
        let off ← match off? with
          | none => pure (some 0)
          | some k =>
            if k.hasLooseBVars || k.hasFVar || mentionsLab k then pure none
            else pure (some (← evalBV64 k))
        let offS := match off with | some o => toString o | none => "?"
        let line ←
          if bs.hasLooseBVars || bs.hasFVar || bs.hasMVar || mentionsLab bs || off.isNone then
            pure s!"S {l} {offS} {decl}"
          else
            pure s!"V {l} {offS} {hex (← evalBytes bs)} {decl}"
        let st ← get
        unless st.seen.contains line do
          set { st with out := st.out.push line, seen := st.seen.insert line }
    -- unfold a cell abbreviation applied to a label
    if let some c := f.constName? then
      if c != ``Mem.Val && unfoldable env c && args.any mentionsLab then
        if let some (.defnInfo d) := env.find? c then
          let v := d.value.instantiateLevelParams d.levelParams f.constLevels!
          visit env decl (fuel - 1) (v.beta args)
    visit env decl (fuel - 1) f
    for x in args do visit env decl (fuel - 1) x
  | .lam _ t b _ | .forallE _ t b _ =>
    visit env decl (fuel - 1) t; visit env decl (fuel - 1) b
  | .letE _ t v b _ =>
    visit env decl (fuel - 1) t; visit env decl (fuel - 1) v; visit env decl (fuel - 1) b
  | .mdata _ b => visit env decl fuel b
  | .proj _ _ b => visit env decl (fuel - 1) b
  | _ => pure ()

unsafe def main : MetaM Unit := do
  let env ← getEnv
  let roots := [``Kraken.Examples.Sbr.ff_aac_sbr_apply_linked,
                ``Kraken.Examples.Sbr.SessionBin.sbr_session_safe]
  let mut st : St := {}
  for r in roots do
    let seen := closure env r
    if seen.isEmpty then throwError "{r} not found"
    st := { st with la := labAbbrevs env seen.toList }
    for n in seen.toList do
      let some idx := env.getModuleIdxFor? n | continue
      let m := env.header.moduleNames[idx.toNat]!
      unless (`Kraken).isPrefixOf m do continue
      let some ci := env.find? n | continue
      -- program texts hold no `=@`; skip them (large)
      if (toString ci.type).endsWith "Program" then continue
      let (_, st') ← (do
        visit env n 64 ci.type
        match ci with
        | .defnInfo d => visit env n 64 d.value
        | .opaqueInfo d => visit env n 64 d.value
        | _ => pure ()).run st
      st := st'
  let txt := "\n".intercalate (st.out.qsort (· < ·)).toList ++ "\n"
  match ← IO.getEnv "SBR_TV_DATA" with
  | some f => IO.FS.writeFile f txt
  | none => IO.print txt
  IO.println s!"data: {st.out.size} placed constants"

end SbrTvData

#eval SbrTvData.main
