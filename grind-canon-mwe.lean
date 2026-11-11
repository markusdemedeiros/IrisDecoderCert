/-
MWE: grind fails to canonicalize a locally constructed instance value.

When a goal contains a term whose instance-implicit argument is a locally
constructed value rather than a globally registered instance (here
`@interp (mkLabels 5) s`, where `mkLabels : Int → Labels` is a plain `def` of
class type), grind's internalization tries to canonicalize the instance
argument by re-synthesizing it from the class and reports
`[issue] failed to canonicalize instance mkLabels 5 / failed to synthesize
Labels` when synthesis finds nothing. The goal display also drops the instance
argument entirely, so facts at different `Labels` values print identically.

This pattern arises whenever a semantics parameterizes interpretation
functions by a class deliberately not backed by global instances: the
environment (e.g. a label-to-address map extracted from a concrete executable,
`Executable.labels` in kraken) is threaded through as an explicit instance
value, so every internalized fact carries such a non-synthesizable instance
argument, and canonicalization silently degrades.

The `@[instance_reducible]` annotation on `mkLabels` does not help: the
canonicalizer attempts synthesis only and does not unfold the instance term,
so the issue is identical for a plain `def` (which additionally draws the
"semireducible definition of class type" warning).

Repro: lean grind-canon-mwe.lean   (lean4 master, e.g. stage1 build)
The expected `grind` failure below prints the diagnostics containing
  [issue] failed to canonicalize instance
        mkLabels 5
      failed to synthesize
        Labels
-/

class Labels where
  label : String → Int

@[instance_reducible] def mkLabels (n : Int) : Labels := ⟨fun _ => n⟩

def interp [Labels] (s : String) : Int := Labels.label s

example (h : @interp (mkLabels 5) "a" = 0) : @interp (mkLabels 5) "b" = 1 := by
  grind
