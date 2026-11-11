import Kraken.SysV

/-!
# `even`/`odd`: the specifications

Two mutually recursive C functions,

```c
bool odd(unsigned n);
bool even(unsigned n) { if (!n) return true;  return odd(n-1); }
bool odd(unsigned n)  { if (!n) return false; return even(n-1); }
```

compiled by clang at `-O0`, are proved correct in two separate files
(`Even.lean`, `Odd.lean`). Each proof may use the specification of *both*
procedures: the one being proved at smaller arguments, and the partner's at
smaller arguments. `Link.lean` ties the two by strong induction on `n`.

This file holds the specifications and nothing else — each body, and the
frame its proof reads, live with the proof — in the *ghost* style: the caller's
memory `R` is a logical variable of the `ProcSpec`, fixed at the call site
with `call_proc_spec_at R`. The *existential* style is in
`EvenOddExistential/`, on the same conditions.

## What is general and what is this program's

General, in the library and used here unchanged:

* `Kraken.SysV`: the calling convention's share of any procedure's
  specification — `RetCell`, the stack reservation `Reserve` and its
  arithmetic, `SavedRegs`, `CallPre`/`CallPost`, the register conventions
  `ArgU32`/`RetU8`, and the `grind` call `grind_cells`;
* `Kraken.MachineWP`: `ProcSpec.of_cfg_post` (a procedure from its blocks),
  `call_proc_spec_at` (a call through the callee's spec), `call_simp`;
* `Kraken.SepCells`: the cell rules `grind` uses for every load and store.

This program's, below:

* `need n`: how much stack the pair uses at argument `n` — a fact about this
  compiler output, exported next to the specification;
* the specifications `EvenPre`/`EvenPost`, `OddPre`/`OddPost`.

## Calling convention vs. semantics

The specification of a procedure at argument `n` is the convention's
`CallPre (need n)`/`CallPost (need n)` plus one semantic conjunct each side.

Calling convention (SysV x86-64, as the compiler relies on it; `Kraken.SysV`):

* the return address is at `[rsp]` on entry (`RetCell ra rsp`);
* the argument is in `edi` — only the low 32 bits of `rdi` (`ArgU32`);
* on return `rsp` is 8 above its entry value (the return address popped),
  and `rbx`, `rbp`, `r12`–`r15` hold their entry values;
* the stack below the entry `rsp` is the procedure's to use: the caller
  *reserves* `need n` bytes there (`Reserve (need n) rsp`), and gets them
  back as owned bytes;
* the result is in `al` (`RetU8`).

Semantics:

* the argument `n` (as a natural number; `n < 2^32` follows from its being
  the value of `edi`);
* `even` returns `(n+1) % 2`, `odd` returns `n % 2` — as a byte in `al`,
  all 8 bits of it (the `and al, 1` on both paths makes the `bool`
  well-formed, so this is more than C's `bool` promises).

## Stack depth

The reservation follows Bedrock's `reserving` clause (see `Kraken.SysV`).
Bedrock's amount is a compile-time constant; here the two procedures recurse,
so the amount is a function of the argument, `need n`, exported next to the
specification like the result is. It is about clang's `-O0` output (24 own
bytes per frame, 8 for each pushed return address), not about `even`; a
tail-calling or inlined build would export a different `need`, against the
same `EvenPre`/`EvenPost` otherwise.

## Caveats

* Kraken has no faulting model, so stack exhaustion cannot be a runtime
  error: the precondition demands the whole stack the recursion will touch,
  and a run from `CallPre` never leaves it.
* The specification is total: a run from `CallPre` *reaches* the return
  address. That is what the recursion on `n` proves.
-/

open Kraken
open Kraken.SysV
open Mem

namespace Kraken.Examples.EvenOddGhost

/-! ## The stack this output uses -/

/-- What `even` and `odd` reserve at argument `n`: 24 own bytes per frame
(saved `rbp`, 16 bytes of locals), and for each of the `n` nested calls the
pushed return address and the callee's frame. -/
def need (n : Nat) : Nat := 24 + 32 * n

theorem need_le {n : Nat} (hn : n < 2 ^ 32) : need n ≤ 2 ^ 64 := by unfold need; omega

/-! ## The specifications -/

/-- `even` at `n`: the convention with `need n` bytes of stack, the argument
in `edi`. -/
abbrev EvenPre (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (need n) R ra t ∧ ArgU32 t n

/-- `even` at `n` returns: the convention, and `al = (n + 1) % 2`. -/
abbrev EvenPost (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (need n) R ra t s ∧ RetU8 s ((n + 1) % 2)

/-- `odd` at `n`: as `even`. -/
abbrev OddPre (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (need n) R ra t ∧ ArgU32 t n

/-- `odd` at `n` returns: the convention, and `al = n % 2`. -/
abbrev OddPost (n : Nat) (R : Mem 64 → Prop) (ra : Int64) (t s : MachineData) : Prop :=
  CallPost (need n) R ra t s ∧ RetU8 s (n % 2)

/-- The spec of `even` at `n`: a `ProcSpec` whose logical variable is the
caller's memory `R`. -/
abbrev EvenSpec [CodeEnv] (n : Nat) : Prop :=
  cenv.ProcSpec ((_root_.Executable.labels cenv).label "even") (EvenPre n) (EvenPost n)

abbrev OddSpec [CodeEnv] (n : Nat) : Prop :=
  cenv.ProcSpec ((_root_.Executable.labels cenv).label "odd") (OddPre n) (OddPost n)

/-- What a file assumes of its partner: its spec at every smaller argument. -/
abbrev EvenSpecBelow [CodeEnv] (n : Nat) : Prop := ∀ m < n, EvenSpec m

abbrev OddSpecBelow [CodeEnv] (n : Nat) : Prop := ∀ m < n, OddSpec m

end Kraken.Examples.EvenOddGhost
