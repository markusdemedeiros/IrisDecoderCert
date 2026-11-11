/-
The kernel checks a linear-size, linear-depth, maximally shared certificate in
quadratic time when the certificate is a spine of *non-adjacent* binders whose
variables are referenced far below them.

## Measurement (this file, `lake env lean kernel-letchain-superlinear-mwe.lean`)

    variant   n=500   n=1000   n=2000   n=4000   DAG(n=4000)
    all        25ms    107ms    466ms   1892ms         20009
    tele        1ms      2ms      4ms      9ms         16009
    local       1ms      3ms      6ms     13ms         12011
    outer       1ms      2ms      4ms      9ms          8012
    inner       1ms      2ms      4ms      8ms          8012

All five have a linear DAG and a linear spine depth. `all` costs 4.1x per
doubling; the rest cost 2.1x.

## The shape

    spine n = fun x_1 => G (fun x_2 => G (... (fun x_n => bot)))

a chain of `n` lambdas separated by applications, with `bot` a chain of `n`
`H` nodes at the bottom.

    all    bot mentions every x_k
    tele   the same bot, but the binders are one adjacent telescope
           `fun x_1 x_2 ... x_n => bot`
    local  each x_k is mentioned immediately under its own lambda
    outer  bot mentions only x_1
    inner  bot mentions only x_n

## The mechanism

`infer_lambda` (src/kernel/type_checker.cpp) opens a maximal *adjacent* lambda
telescope with one `instantiate_rev` of the body against all its free
variables. An application between two lambdas ends the telescope, so a spine of
`n` non-adjacent binders is opened by `n` separate instantiations.

`instantiate_rev` rebuilds every node whose loose bvar range still reaches out
of the current binder, i.e. every node on a path from that binder to an
occurrence of it, and stops at the first node that is closed relative to the
current depth. So opening binder `k` costs the distance from `x_k` to its
occurrences. In `all`, that distance is the whole spine below `x_k` plus the
prefix of `bot`, hence

    sum over k of Theta(n)  =  Theta(n^2)

and it is quadratic in *allocated nodes*, not just in traversal: each of the
`n` openings produces a fresh copy of everything between the binder and its
uses. `tele` pays the same total for one instantiation of `n` variables at
once; `local` pays O(1) per binder.

## Where it came from

Symbolic execution of machine code. `vcgen` emits a spine of `le_forall _ _ _
(fun x => ...)` steps, and `kfold` puts its whole `let hfold_k := ...` chain at
the bottom of that spine, where the chain mentions the `x` bound at every
level. That is the `all` variant.

Instrumenting the kernel to count `replace` node visits per call site on
`AddChain` (`bench/vcgen_kraken.lean`, `kfold_discharge`) attributes the whole
super-linear part to the body instantiation in `infer_lambda` and nothing else:

    n                       40       80      160      320
    kernel                21ms     59ms    194ms    643ms
    visits, infer_lambda  201k     705k    2624k   10112k     3.5-3.9x
    visits, everything     159k     304k     595k    1176k     1.9-2.0x
    infer_type calls       33k      65k     128k     253k     1.9-2.0x
    is_def_eq calls        17k      33k      66k     131k     1.9-2.0x

and bucketing those instantiations by cost shows both factors of the product
growing with `n`: the number of expensive openings, and the size of each.

    n     openings costing 2^b..2^(b+1)-1 nodes
    40    149 at b=9
    80    333 at b=10
    160   702 at b=11
    320  1444 at b=12

That is 4.5n binders, each rebuilding about 19n nodes, 87n^2 in total: 8.9M of
the 11.3M nodes the kernel rebuilds at n=320.
-/
import Lean
open Lean Meta

opaque G : (Nat → Nat) → Nat
opaque H : Nat → Nat → Nat

def dagSize (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack := #[e]
  while stack.size > 0 do
    let t := stack.back!; stack := stack.pop
    if seen.contains t then continue
    seen := seen.insert t
    match t with
    | .app f a => stack := (stack.push f).push a
    | .lam _ ty b _ | .forallE _ ty b _ => stack := (stack.push ty).push b
    | .letE _ ty v b _ => stack := ((stack.push ty).push v).push b
    | .proj _ _ b | .mdata _ b => stack := stack.push b
    | _ => pure ()
  return seen.size

def nat := mkConst ``Nat
def gg := mkConst ``G
def hh := mkConst ``H

inductive Mode | outer | inner | all | tele | «local»
deriving BEq, Inhabited

def Mode.name : Mode → String
  | .outer => "outer" | .inner => "inner" | .all => "all  "
  | .tele => "tele " | .local => "local"

/-- `H r_1 (H r_2 (... (H r_m 0)))`. -/
def bottom (refs : Array Expr) : Expr := Id.run do
  let mut r := mkNatLit 0
  for i in [0:refs.size] do
    r := mkApp2 hh refs[refs.size - 1 - i]! r
  return r

def spine (n : Nat) (mode : Mode) : Expr := Id.run do
  match mode with
  | .local =>
    -- fun x_1 => H x_1 (G (fun x_2 => H x_2 (G (... (fun x_n => H x_n 0)))))
    let mut r := mkApp2 hh (.bvar 0) (mkNatLit 0)
    for _ in [0:n-1] do
      r := mkApp2 hh (.bvar 0) (mkApp gg (.lam `x nat r .default))
    return .lam `x nat r .default
  | .tele =>
    -- fun x_1 ... x_n => bot, one adjacent telescope
    let mut r := bottom ((Array.range n).map fun i => .bvar (n - 1 - i))
    for _ in [0:n] do
      r := .lam `x nat r .default
    return r
  | _ =>
    -- inside the innermost lambda, bvar 0 is x_n and bvar (n-1) is x_1
    let refs : Array Expr := match mode with
      | .outer => #[.bvar (n-1)]
      | .inner => #[.bvar 0]
      | _      => (Array.range n).map fun i => .bvar (n - 1 - i)
    let mut r := bottom refs
    for _ in [0:n] do
      r := mkApp gg (.lam `x nat r .default)
    -- strip the outermost `G`, leaving the closed term `fun x_1 => ...`
    return r.appArg!

def bench (tag : String) (e : Expr) : MetaM Unit := do
  let e := Lean.ShareCommon.shareCommon e
  let t0 ← IO.monoNanosNow
  let ok := (Lean.Kernel.check (← getEnv) {} e).toOption.isSome
  let t1 ← IO.monoNanosNow
  IO.println s!"{tag}  DAG={dagSize e}  kernel={(t1-t0)/1000000}ms  ok={ok}"

set_option maxRecDepth 100000 in
#eval show MetaM Unit from do
  for m in [Mode.all, Mode.tele, Mode.local, Mode.outer, Mode.inner] do
    for n in [500, 1000, 2000, 4000] do
      bench s!"{m.name} n={n}" (spine n m)
