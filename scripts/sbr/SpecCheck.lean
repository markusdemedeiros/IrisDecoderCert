import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.SessionBin.Top

/-! Where the trusted closures live (run by ci.sh, step `spec`).

The trusted closures of `ff_aac_sbr_apply_linked` and `SessionBin.sbr_session_safe` (as in
`Tcb.lean`: every declaration reachable from the statement through statements and definition
bodies, not through proofs) consist of three kinds of declarations:

* the machine model and the framework: modules `Kraken.*` outside `Kraken.X64.Examples`, and
  Lean's own;
* program texts (`Program`, `List Directive`, `List (Label × Program)` constants), checked
  against the object by translation validation;
* the specification: everything else, which must be defined in `SessionSpec.lean` or
  `SessionSpecData.lean`, so that a reviewer reads those two files.

Checks, and fails (with the offending names) unless:
1. every closure declaration of a module under `Kraken.X64.Examples` that is not a program
   text is in `SessionSpec` or `SessionSpecData`;
2. every module holding a program text of the closures imports (transitively) only the
   machine model, the parser and other such text modules: no specification, no proof;
3. `SessionSpec` and `SessionSpecData` import (transitively) only the machine model, those
   text modules and `SessionSpecData`: no proof module. -/

open Lean Meta

namespace SbrSpecCheck

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

/-- A program text: a `Program`, a `List Directive`, or a labelled block list. -/
def isProgramText (ci : ConstantInfo) : Bool :=
  let ty := toString ci.type
  ty.endsWith "Program" || ty.endsWith "Directive"
    || ty == "List.{0} (Prod.{0, 0} Label Program)"

/-- The project's examples (specifications, proofs, texts). -/
def isExample (m : Name) : Bool := (`Kraken.X64.Examples).isPrefixOf m

def specMods : List Name :=
  [`Kraken.X64.Examples.Sbr.SessionSpec, `Kraken.X64.Examples.Sbr.SessionSpecData]

/-- The modules `m` imports, transitively (without `m`). -/
partial def importClosure (env : Environment) (m : Name) : NameSet := Id.run do
  let mut todo : Array Name := #[m]
  let mut seen : NameSet := {}
  while todo.size > 0 do
    let n := todo.back!
    todo := todo.pop
    let some idx := env.getModuleIdx? n | continue
    for i in env.header.moduleData[idx.toNat]!.imports do
      unless seen.contains i.module do
        seen := seen.insert i.module
        todo := todo.push i.module
  return seen

def main : MetaM Unit := do
  let env ← getEnv
  let roots := [`Kraken.Examples.Sbr.ff_aac_sbr_apply_linked,
    `Kraken.Examples.Sbr.SessionBin.sbr_session_safe]
  let mut errs : Array String := #[]
  let mut textMods : NameSet := {}
  let mut nSpec := 0
  let mut nText := 0
  let mut all : NameSet := {}
  for root in roots do
    let seen := closure env root
    if seen.isEmpty then throwError "{root} not found"
    all := seen.toList.foldl (fun acc n => acc.insert n) all
  for n in all.toList do
    let some ci := env.find? n | continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless isExample m do continue
    if isProgramText ci then
      textMods := textMods.insert m
      nText := nText + 1
    else if specMods.contains m then
      nSpec := nSpec + 1
    else
      errs := errs.push s!"1. {n} is defined in {m}, not in SessionSpec/SessionSpecData"
  -- 2. text modules import only the machine model and text modules
  for m in textMods.toList do
    for i in (importClosure env m).toList do
      if isExample i && !textMods.contains i then
        errs := errs.push s!"2. text module {m} imports {i}"
  -- 3. the specification imports only the machine model, texts and its data
  for m in specMods do
    if (env.getModuleIdx? m).isNone then
      errs := errs.push s!"3. {m} is not imported"
    for i in (importClosure env m).toList do
      if isExample i && !textMods.contains i && !specMods.contains i then
        errs := errs.push s!"3. {m} imports {i}, neither a text module nor the specification"
  IO.println s!"spec: {nSpec} closure declarations in SessionSpec/SessionSpecData, \
    {nText} program texts in {textMods.size} text modules"
  for m in textMods.toList.toArray.qsort (·.toString < ·.toString) do
    IO.println s!"text module: {m}"
  if errs.isEmpty then
    IO.println "SPECCHECK ok"
  else
    for e in errs do IO.println e
    throwError "SPECCHECK FAIL: {errs.size} problems"

end SbrSpecCheck

#eval SbrSpecCheck.main
