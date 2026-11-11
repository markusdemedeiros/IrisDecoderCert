# Generated rule files

`Kraken/Rules/IntMisc.lean`, `PackedSse.lean` and `ScalarFloat.lean` are
generated. Edit the generator or the header/footer here, then run, from the
repository root:

```
python3 Kraken/Rules/gen/regen.py           # rewrite the three files
python3 Kraken/Rules/gen/regen.py --check   # exit 1 if a file is stale
lake build
```

| Output | Generator | Hand-written parts |
|---|---|---|
| `IntMisc.lean` | `gen_int.py` | `int_header.lean.in` (helper lemmas, proof macros), `int_footer.lean.in` |
| `PackedSse.lean` | `gen_sse.py` | `sse_header.lean.in` (proof macros) |
| `ScalarFloat.lean` | `gen_float.py` | `float_header.lean.in` (flag lemmas, hand-written `vmovss`/`vmovsd` rules, proof macros), `float_footer.lean.in` |

The headers and footers are `.lean.in` so that the library's `Kraken.*` glob
does not compile them. `regen.py` also writes one-line rule lists to `out/`
(not checked in), handy for review.

## What a generator does

Each generator is a table of instruction forms plus a few templates. A row
gives the operation, the operand widths, the constructor term the parser
produces, and the state update the semantics performs. The templates turn a
row into one `@[spec low]` theorem per operand form:

* **register form**: precondition `WP.wp p Q E {s with …}`, proved by the
  shared `reg_rule` macro (`fallthrough_spec` + one `simp only` step);
* **memory form** over the generic operand `⟨some (.reg b), idx, .int64 d⟩`
  (see `GenericMem.lean`): readability (`Mem.loadInt … isSome`), alignment
  where the semantics checks it, then the update with the loaded value bound by
  `∀ v, Mem.loadInt … = some v → …`; proved by the shared `mem_rule` macro;
* **`sym(%rip)` form** where the code loads constants that way.

So every rule's statement is mechanical and its proof is one macro token.

## Why generate

* Several hundred rules that differ only in width, mnemonic and update term.
  Writing them by hand invites copy-paste slips in exactly the parts that
  matter (byte counts, alignment, which bits are kept); a template gets them
  right once.
* A change of convention (e.g. how a sub-register write is spelled, or a new
  side condition) is one template edit and a regeneration, not hundreds of
  edits.
* The cost was measured: importing `IntMisc.lean` (262 rules) did not slow
  existing `vcgen` proofs beyond noise, because `vcgen` picks a rule by the
  instruction's head shape.

## Why not fewer, more general rules

Two generalisations were tried and rejected.

1. **One rule over the operand width `w : Width`.** It states, e.g.,
   `regs := s.regs.set (.low r w) v`. With `w` a variable, `Reg64s.set` and
   `Reg64s.get` do not reduce: whether the write zero-extends (32-bit), keeps
   the upper bits (8/16-bit) or replaces everything (64-bit) depends on `w`.
   The verification conditions then contain stuck `set (.low r w)` terms that
   neither the state simplification nor `grind` can see through, and
   `vcgen … with finish` fails or blows up. Per-width rules spell reads and
   writes on the 64-bit register file (`get64`/`set64`, `setWidth`,
   `replaceLow`), the vocabulary the rest of `MachineWP` and its `grind`
   lemmas use.
2. **One rule over the operation** (a variable `op` with a side condition
   saying what it computes). `vcgen` selects a spec by matching the
   instruction term; a rule whose instruction is `.avx asz w op` matches every
   vector instruction, so it would shadow the specific rules or be tried for
   every step. One rule per constructor keeps the match exact; what is shared
   is the proof, through the macros.

The memory operand, by contrast, generalises well: one rule over
`⟨some (.reg b), idx, .int64 d⟩` covers `d(%b)`, `(%b)`, `(%b,%i,s)` and
`d(%b,%i,s)`, because `AddrIndex.offset64` reduces at each concrete index by
`grind` normalisation.
