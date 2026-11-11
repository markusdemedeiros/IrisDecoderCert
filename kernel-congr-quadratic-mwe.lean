/-
MWE: the kernel takes super-quadratic time to check a maximally-shared proof
term whose *size* grows linearly.

## Measurement (this file)

    n      shared DAG    kernel
    200    1206          15ms
    400    2406          62ms      (DAG 2.0x, kernel 4.1x)
    800    4806          379ms     (DAG 2.0x, kernel 6.1x)
    1600   9606          3594ms    (DAG 2.0x, kernel 9.5x)

## What triggers it

Not spine length, not certificate size, not loss of sharing. Holding the
number of proof nodes and the chain length fixed and varying only whether each
node's *type* grows with its depth:

    variant                              n=400   n=800   n=1600
    types grow  (node k : f^k a = f^k b)   63ms   374ms   3593ms
    types small (node k : a = b)            1ms     2ms      4ms

Same node count, same sharing; one is linear, the other super-quadratic. So
kernel cost tracks the sum of the sizes of the intermediate types, not the
size of the shared term: the kernel infers and compares each node's type, and
sharing the representation does not make those traversals cheaper.

## Further controls (measured separately, worth adding here)

* Interleaved single lambdas with applications, outer variable referenced at
  every depth, constant-size types: LINEAR (2/2/6/12ms at n=400..3200). The
  kernel's per-binder instantiation is not itself the problem.
* A `let`-chain certificate (each proof bound once, used by fvar) with linear
  tree, linear DAG, linear depth still checks in ~n^1.7 in the real pipeline,
  so at least one more super-linear kernel behaviour remains unisolated.

## Where it came from

Symbolic execution of machine code (an x86 semantics verified with `vcgen`).
Stepping emits one equation per state component per instruction, and folding
them builds exactly this shape: nested congruences over a state term that
deepens with each instruction. Kernel time there grows ~3.0-3.4x per doubling
while the certificate grows 1.9-2.0x, identically across three unrelated
program families and two different discharge tactics, which is what led here.

Repro:
    lake env lean kernel-congr-quadratic-mwe.lean
-/
import Lean
open Lean Meta

opaque f : Nat → Nat
opaque a : Nat
opaque b : Nat
axiom base : a = b

/-- `nest k` is `f (f ... (f a))` with `k` applications; shared, so its DAG is O(k). -/
def nest (hd : Expr) : Nat → Expr
  | 0 => hd
  | k+1 => mkApp (mkConst ``f) (nest hd k)

/-- Proof of `f^n a = f^n b` as `congrArg f (congrArg f ... base)`.
Each node's *type* mentions `f^k a`, whose size grows with k, even though the
shared representation stays linear. -/
def mkCongrChain (n : Nat) : Expr := Id.run do
  let mut prf := mkConst ``base
  let A := mkConst ``a
  let B := mkConst ``b
  for k in [0:n] do
    prf := mkApp6 (mkConst ``congrArg [1, 1]) (mkConst ``Nat) (mkConst ``Nat)
             (nest A k) (nest B k) (mkConst ``f) prf
  return prf

def dagSize (e : Expr) : Nat := Id.run do
  let mut seen : Std.HashSet Expr := {}
  let mut stack := #[e]
  while stack.size > 0 do
    let t := stack.back!; stack := stack.pop
    if seen.contains t then continue
    seen := seen.insert t
    match t with
    | .app x y => stack := (stack.push x).push y
    | .lam _ ty x _ | .forallE _ ty x _ => stack := (stack.push ty).push x
    | .letE _ ty v x _ => stack := ((stack.push ty).push v).push x
    | .proj _ _ x | .mdata _ x => stack := stack.push x
    | _ => pure ()
  return seen.size

def bench (n : Nat) : MetaM Unit := do
  let prf := Lean.ShareCommon.shareCommon (mkCongrChain n)
  let t0 ← IO.monoNanosNow
  let ok := (Lean.Kernel.check (← getEnv) {} prf).toOption.isSome
  let t1 ← IO.monoNanosNow
  IO.println s!"n={n}  DAG={dagSize prf}  kernel={(t1-t0)/1000000}ms  ok={ok}"

#eval show MetaM Unit from do
  bench 200
  bench 400
  bench 800
  bench 1600
