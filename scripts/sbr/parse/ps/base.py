#!/usr/bin/env python3
"""Generate the label table skeleton and the variant of `ff_ps_read_data` (Parse/PsBase.lean).

Usage: python3 scripts/sbr/parse/ps/base.py Kraken/X64/Examples/Sbr/Parse/PsText.lean \\
    > Kraken/X64/Examples/Sbr/Parse/PsBase.lean

The control-flow graph is read off the program text (jumps and fall-throughs). The variant of
a label is `lex [g, m1, h, m2, j, m3]`: `g` ranks the strongly connected components of the
graph (longest path to the exit, so it decreases along every edge between components), `m1` is
the measure of the outermost loop containing the label (0 outside loops), `h` ranks the
components of that loop's body once the edges into its header are removed, and so on for the
two inner levels. The measures are Lean terms in the state `s`, given per loop header below
(with per-label overrides where a register is reused).

Each label `ff_ps_read_data.L<off>` is mapped to the predicate `q<off>` (`qEntry` for the
entry) of the region files `PsInvH`, `PsInvL`, `PsInvX`, `PsInvT`.

With `--cfg` it prints `PsCfg.lean` (the label match `tableG` over an assertion family and the
variant `var`), with `--cfg R` (R one of H, L, X, T) `PsCfg<R>.lean`: the equations `tg_L<off>`
and `var_L<off>` at the labels of one region, proved by `rfl` once. These depend on the text
only, not on the assertions, so editing an assertion does not re-check them:

    P=Kraken/X64/Examples/Sbr/Parse
    python3 scripts/sbr/parse/ps/base.py $P/PsText.lean --cfg > $P/PsCfg.lean
    for R in H L X T; do
      python3 scripts/sbr/parse/ps/base.py $P/PsText.lean --cfg $R > $P/PsCfg$R.lean
    done
"""
import re
import sys

PFX = 'ff_ps_read_data'

# The measure of each loop, by header label offset; overrides by label offset.
MEASURE = {
    '6d0': '(s.regs.get64 .rsi - s.regs.get64 .rax).toNat',
    '700': '(s.regs.get64 .rax - s.regs.get64 .rdx).toNat',
    '775': '(slot64 s 0x78 - s.regs.get64 .rbx).toNat',
    '7e0': '(s.regs.get64 .r11 - s.regs.get64 .r10).toNat',
    '910': '(s.regs.get64 .r11 - s.regs.get64 .r10).toNat',
    'aa5': '(slot64 s 0x58 - s.regs.get64 .r9).toNat',
    'b20': '(s.regs.get64 .rsi - s.regs.get64 .r11).toNat',
    'be0': '(s.regs.get64 .rsi - s.regs.get64 .r11).toNat',
    'd7b': '(slot32 s 0x80).toInt.toNat',
    'e15': '(slot64 s 0x58 - s.regs.get64 .r15).toNat',
    'e60': '(s.regs.get64 .rbx - s.regs.get64 .r14).toNat',
    'ee0': '(s.regs.get64 .rbx - s.regs.get64 .r10).toNat',
    'f70': '(s.regs.get64 .rbx - s.regs.get64 .r14).toNat',
    '1000': '(s.regs.get64 .rbx - s.regs.get64 .r10).toNat',
    '1252': '(s.regs.get64 .rcx - s.regs.get64 .r11).toNat',
}
EAX = '((s.regs.get64 .rax).setWidth 32).toInt.toNat'
OVERRIDE = {
    # the `iid` loop with two subtable levels keeps the count in rdi
    ('910', '96f'): '(s.regs.get64 .rdi - s.regs.get64 .r10).toNat',
    ('910', '983'): '(s.regs.get64 .rdi - s.regs.get64 .r10).toNat',
    ('910', '996'): '(s.regs.get64 .rdi - s.regs.get64 .r10).toNat',
    ('910', '9b1'): '(s.regs.get64 .rdi - s.regs.get64 .r10).toNat',
    ('910', '9cd'): '(s.regs.get64 .rdi - s.regs.get64 .r10).toNat',
    # the extension loop: the count in eax until it is stored at `rbp - 0x80`
    ('d7b', 'd7b'): EAX,
    ('d7b', 'd93'): EAX,
    ('d7b', 'da7'): EAX,
    ('d7b', 'dc6'): EAX,
    ('d7b', 'd70'): '(((s.regs.get64 .rax).setWidth 32 + (s.regs.get64 .rcx).setWidth 32)'
                    '.toInt.toNat + 1)',
}


def parse(path):
    text = open(path).read()
    body = text[text.index('parse("') + 7:text.rindex('")')]
    labels, edges, cur, falls = [], {}, None, True
    for raw in body.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.endswith(':'):
            lab = line[:-1]
            if cur is not None and falls:
                edges[cur].add(lab)
            cur = lab
            labels.append(lab)
            edges[lab] = set()
            falls = True
            continue
        op = line.split()[0]
        if op.startswith('j'):
            tgt = line.split()[1]
            if tgt.startswith(PFX):
                edges[cur].add(tgt)
            falls = op != 'jmp'
        elif op.startswith(('ud1', 'ret')):
            falls = False
    if labels[-1] == PFX + '.done':
        edges[labels[-1]] = set()
    return labels, edges


def sccs(nodes, edges):
    """Tarjan; returns the components in reverse topological order (sinks first)."""
    idx, low, st, on, out = {}, {}, [], set(), []
    counter = [0]
    sys.setrecursionlimit(10000)

    def go(v):
        idx[v] = low[v] = counter[0]
        counter[0] += 1
        st.append(v)
        on.add(v)
        for w in edges[v]:
            if w not in nodes:
                continue
            if w not in idx:
                go(w)
                low[v] = min(low[v], low[w])
            elif w in on:
                low[v] = min(low[v], idx[w])
        if low[v] == idx[v]:
            comp = []
            while True:
                w = st.pop()
                on.discard(w)
                comp.append(w)
                if w == v:
                    break
            out.append(comp)
    for v in nodes:
        if v not in idx:
            go(v)
    return out


def off(lab):
    return 'Entry' if lab == PFX else lab.split('.')[-1].lstrip('L')


def ranks(nodes, edges, header=None):
    """Per node: (rank, component); edges into `header` are dropped."""
    es = {v: {w for w in edges[v] if w in nodes and w != header} for v in nodes}
    comps = sccs(nodes, es)
    cid = {v: i for i, c in enumerate(comps) for v in c}
    rank = {}
    for i, c in enumerate(comps):  # sinks first
        r = 0
        for v in c:
            for w in es[v]:
                if cid[w] != i:
                    r = max(r, rank[cid[w]] + 1)
        rank[i] = r
    return {v: (rank[cid[v]], comps[cid[v]], v in es[v]) for v in nodes}


def digits(labels, edges):
    res = {v: [] for v in labels}

    def level(nodes, depth, header):
        rk = ranks(nodes, edges, header)
        for v in nodes:
            res[v].append(str(rk[v][0]))
        done = set()
        for v in sorted(nodes, key=labels.index):
            comp = rk[v][1]
            if not (len(comp) > 1 or rk[v][2]):
                res[v].append('0')
                pad(v, depth + 1)
                continue
            if id(comp) in done:
                continue
            done.add(id(comp))
            ins = [w for w in comp if any(w in edges[u] for u in labels if u not in comp)]
            assert len(ins) == 1, (comp, ins)
            hdr = ins[0]
            for w in comp:
                key = (off(hdr), off(w))
                m = OVERRIDE.get(key, MEASURE.get(off(hdr)))
                assert m, ('no measure for loop', hdr)
                res[w].append(m)
            if depth < 2:
                level(set(comp), depth + 1, hdr)
            else:  # innermost: every back edge goes to the header
                for w in comp:
                    for u in edges[w]:
                        if u in comp and u != hdr:
                            assert labels.index(u) > labels.index(w), ('back edge', w, u)
                    pad(w, depth + 1)

    def pad(v, depth):
        while len(res[v]) < 6:
            res[v].append('0')

    level(set(labels), 0, None)
    for v in labels:
        pad(v, 0)
    return res


HEAD = """open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

"""

CFG = """import Kraken.X64.Examples.Sbr.Parse.PsSpec
import Kraken.Rules.LexVar

/-!
# `ff_ps_read_data`: the label table's shape and the variant

`tableG Q` maps the label `ff_ps_read_data.L<off>` to `Q <off>` (the entry to `Q 0`, `done` to
`Q 0x17d6`); `PsBase` instantiates `Q` with the assertions of the region files. Reducing a
string match at a literal label is slow, so the per-label equations are checked once, in
`PsCfgH`, `PsCfgL`, `PsCfgX`, `PsCfgT`, and none of these files depends on the assertions.

The variant is a tuple compared lexicographically (`Kraken.lex`): the rank of the label's
strongly connected component, then per loop level the loop's measure and the rank inside the
loop body. Generated by `scripts/sbr/parse/ps/base.py --cfg`.
-/

%HEAD%def tableG (Q : Nat → MachineData → Prop) : Label → MachineData → Prop
%TABLE%
  | _, _ => False

def var : Label → MachineData → Nat
%VAR%
  | _, _ => 0

end Kraken.Examples.Sbr.Ps
"""

HEAD0 = """open Kraken Kraken.X64.Parser

namespace Kraken.Examples.Sbr.Ps

"""

CFGR = """import Kraken.X64.Examples.Sbr.Parse.PsCfg

/-!
# `ff_ps_read_data`: `tableG` and `var` at the labels of %DOC%

Generated by `scripts/sbr/parse/ps/base.py --cfg %R%`.
-/

%HEAD%"""

BASE = """import Kraken.X64.Examples.Sbr.Parse.PsInvH
import Kraken.X64.Examples.Sbr.Parse.PsInvL
import Kraken.X64.Examples.Sbr.Parse.PsInvX
import Kraken.X64.Examples.Sbr.Parse.PsInvT
import Kraken.X64.Examples.Sbr.Parse.PsCfgH
import Kraken.X64.Examples.Sbr.Parse.PsCfgL
import Kraken.X64.Examples.Sbr.Parse.PsCfgX
import Kraken.X64.Examples.Sbr.Parse.PsCfgT

/-!
# `ff_ps_read_data`: the block table

The assertion at each label is `q<off>` of the region files (`PsInvH` header and borders,
`PsInvL` the `iid`/`icc` parameters, `PsInvX` the extension, `PsInvT` the fix-ups, the error
path and the return), through `tableG` (`PsCfg`) and the offset match `qs`. `tab_L<off>` is
the table at one label. Generated by `scripts/sbr/parse/ps/base.py`.
-/

%HEAD%variable [CodeEnv]

/-- The assertion at each label offset. -/
def qs (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    Nat → MachineData → Prop
%QS%
  | _, _ => False

abbrev table (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop :=
  tableG (qs k Ext x ra t₀)

%TABS%/-- What a return leaves, before the frame is folded back into the caller's reservation. -/
abbrev Post' (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  ∃ c i f, PsOut x t₀ c i ((s.regs.get64 .rax).setWidth 32) ∧ f.length = 0x78
    ∧ s.regs.get64 .rsp = rsp0 t₀ + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
    ∧ SavedRegs t₀ s ∧ (s.dmem =⋆ Fr k Ext x ra t₀ f c i)

/-- The only exit is the return. -/
abbrev Exit (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (a : Int64) (s : MachineData) : Prop :=
  a = ra ∧ Post' k Ext x ra t₀ s

abbrev BlockOb (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k Ext x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k Ext x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k Ext x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ Exit k Ext x ra t₀ a s ⦄

end Kraken.Examples.Sbr.Ps
"""

REGIONS = {'H': (0, 0x715), 'L': (0x715, 0xcba), 'X': (0xcba, 0x1063), 'T': (0x1063, 1 << 30)}
REGION_DOC = {'H': 'the header, the frame class and the borders', 'L': 'the `iid` and `icc` parameters',
              'X': 'the extension', 'T': 'the fix-ups, the error path and the return'}
DONE = 0x17d6


def num(lab):
    o = off(lab)
    return 0 if o == 'Entry' else DONE if o == 'done' else int(o, 16)


def region(lab):
    v = num(lab)
    return next(r for r, (a, b) in REGIONS.items() if a <= v < b)


def nm(lab):
    o = off(lab)
    return o if o in ('Entry', 'done') else 'L' + o


def qname(lab):
    o = off(lab)
    return 'qEntry' if o == 'Entry' else f'q{o}'


def cfgr(labels, dg, r):
    out = [CFGR.replace('%DOC%', REGION_DOC[r]).replace('%R%', r).replace('%HEAD%', HEAD0)]
    for v in labels:
        if region(v) != r:
            continue
        out.append(f'theorem tg_{nm(v)} (Q : Nat → MachineData → Prop) (s : MachineData) :\n'
                   f'    tableG Q "{v}" s = Q {hex(num(v))} s := rfl\n\n')
        out.append(f'@[lex_var] theorem var_{nm(v)} (s : MachineData) :\n'
                   f'    var "{v}" s = lex [{", ".join(dg[v])}] := rfl\n\n')
    out.append('end Kraken.Examples.Sbr.Ps\n')
    return ''.join(out)


def main():
    labels, edges = parse(sys.argv[1])
    dg = digits(labels, edges)
    if len(sys.argv) > 2 and sys.argv[2] == '--cfg':
        if len(sys.argv) > 3:
            sys.stdout.write(cfgr(labels, dg, sys.argv[3]))
            return
        tab = '\n'.join(f'  | "{v}", s => Q {hex(num(v))} s' for v in labels)
        var = '\n'.join(f'  | "{v}", s => lex [{", ".join(dg[v])}]' for v in labels)
        sys.stdout.write(CFG.replace('%HEAD%', HEAD0).replace('%TABLE%', tab).replace('%VAR%', var))
        return
    qs = '\n'.join(f'  | {hex(num(v))}, s => {qname(v)} k Ext x ra t₀ s' for v in labels)
    tabs = ''.join(f'theorem tab_{nm(v)} (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)\n'
                   f'    (t₀ s : MachineData) :\n'
                   f'    table k Ext x ra t₀ "{v}" s = {qname(v)} k Ext x ra t₀ s :=\n'
                   f'  tg_{nm(v)} _ s\n\n' for v in labels)
    sys.stdout.write(BASE.replace('%HEAD%', HEAD).replace('%QS%', qs).replace('%TABS%', tabs))


if __name__ == '__main__':
    main()
