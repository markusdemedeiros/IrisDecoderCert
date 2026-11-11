import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.SessionBin.Top

/-! The trusted closures of the two top theorems (run by ci.sh, step `tcb`).

For each root, `ff_aac_sbr_apply_linked` and then `SessionBin.sbr_session_safe`, collects
every declaration reachable from its statement through statements and definition bodies, but
not through proofs: the definitions whose meaning the theorem depends on. Prints, per project
module (`Kraken*`), the source lines those declarations span and their number; program texts
(`Program`, `List Directive` and `List (Label × Program)` constants, checked by translation
validation) are counted on their own rows.

Each table ends with a fingerprint line, a hash of the closure's names, types and definition
bodies (independent of which module or line a declaration sits in): `FINGERPRINT` for
`ff_aac_sbr_apply_linked`, `FINGERPRINT_SESSION` for `sbr_session_safe`. It changes exactly
when the meaning of the statement can change; ci.sh compares them with
`baseline/tcb_fingerprint.txt` and `baseline/tcb_fingerprint_session.txt`. After an intended
change to the specification, the machine model or a program text, re-record it
(`lake env lean scripts/sbr/Tcb.lean`) and review the change.

Auxiliary constants (`isAux`) are hashed by content, not by name. Lean shares a nested proof
`…._proof_N` or a matcher `…match_N` between the declarations of one file that need the same one
(a per-file cache), so their names, and the names in the bodies that use them, depend on how
declarations are grouped into files. The fingerprint therefore replaces every reference to an
auxiliary constant by the hash of its content (recursively: type, and value for a matcher; a
theorem's proof is irrelevant, as for every theorem of the closure), and counts each distinct
auxiliary content once. Moving definitions between files leaves it unchanged; changing an
auxiliary constant's type, or a matcher, changes it. -/

open Lean Meta

namespace SbrTcb

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

/-- `s` is `p` followed by a decimal number. -/
def isNumbered (p s : String) : Bool :=
  s.startsWith p && s.length > p.length && (s.toList.drop p.length).all Char.isDigit

/-- An auxiliary constant that the elaborator creates and shares through a per-file cache: a
nested proof abstracted as a theorem `…._proof_N`, or a matcher `…match_N` (registered as
one). -/
def isAux (env : Environment) (n : Name) : Bool :=
  match n, env.find? n with
  | .str _ s, some (.thmInfo _) => isNumbered "_proof_" s
  | .str _ s, some (.defnInfo _) => isNumbered "match_" s && isMatcherCore env n
  | _, _ => false

mutual
/-- The hash of a constant's content with auxiliary constants normalized: type and value of a
definition, the type of anything else. -/
partial def contentHash (env : Environment) (ci : ConstantInfo) : UInt64 :=
  match ci with
  | .defnInfo d => mixHash (hash (norm env d.type)) (hash (norm env d.value))
  | .opaqueInfo d => mixHash (hash (norm env d.type)) (hash (norm env d.value))
  | ci => hash (norm env ci.type)

/-- `e` with each auxiliary constant replaced by a name made from its content hash. -/
partial def norm (env : Environment) (e : Expr) : Expr :=
  e.replace fun
    | .const n ls =>
      if isAux env n then
        let h := (env.find? n).map (contentHash env) |>.getD 0
        some (.const (Name.mkSimple s!"aux{h}") ls)
      else none
    | _ => none
end

/-- The table and the fingerprint line (`tag`) of `root`'s closure. -/
def report (root : Name) (tag : String) : MetaM Unit := do
  let env ← getEnv
  let seen := closure env root
  if seen.isEmpty then throwError "{root} not found"
  let mut byMod : Std.HashMap Name (Array (Nat × Nat)) := {}
  let mut cnt : Std.HashMap Name Nat := {}
  let mut fp : UInt64 := 0
  let mut aux : Std.HashSet UInt64 := {}
  for n in seen.toList do
    -- fingerprint over every reachable constant (Lean core included); order-independent
    if let some ci := env.find? n then
      if isAux env n then aux := aux.insert (contentHash env ci)
      else fp := fp + mixHash (hash n) (contentHash env ci)
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`Kraken).isPrefixOf m || (`KrakenTactics).isPrefixOf m do continue
    let isProg := (env.find? n).map isProgramText |>.getD false
    let m := if isProg then m.str "[program text]" else m
    cnt := cnt.insert m (cnt.getD m 0 + 1)
    if let some rg ← findDeclarationRanges? n then
      byMod := byMod.insert m ((byMod.getD m #[]).push (rg.range.pos.line, rg.range.endPos.line))
  let mut total := 0
  let mut decls := 0
  let mut rows : Array (Nat × Name × Nat) := #[]
  for (m, rs) in byMod.toList do
    let rs := rs.qsort (fun a b => a.1 < b.1)
    let mut lines := 0
    let mut cur : Option (Nat × Nat) := none
    for (a, b) in rs do
      match cur with
      | none => cur := some (a, b)
      | some (ca, cb) =>
        if a ≤ cb + 1 then cur := some (ca, max cb b)
        else
          lines := lines + (cb - ca + 1)
          cur := some (a, b)
    if let some (ca, cb) := cur then lines := lines + (cb - ca + 1)
    total := total + lines
    decls := decls + cnt.getD m 0
    rows := rows.push (lines, m, cnt.getD m 0)
  IO.println "lines\tdecls\tmodule"
  for (l, m, c) in rows.qsort (fun a b => a.1 > b.1 || (a.1 == b.1 && a.2.1.toString < b.2.1.toString)) do
    IO.println s!"{l}\t{c}\t{m}"
  IO.println s!"TOTAL\t{total}\t{decls} project decls ({seen.size} reachable in all modules)"
  for h in aux.toList do fp := fp + mixHash (hash "aux") h
  IO.println s!"{tag} {fp}"

def main : MetaM Unit := do
  report `Kraken.Examples.Sbr.ff_aac_sbr_apply_linked "FINGERPRINT"
  IO.println "== sbr_session_safe"
  report `Kraken.Examples.Sbr.SessionBin.sbr_session_safe "FINGERPRINT_SESSION"

end SbrTcb

#eval SbrTcb.main
