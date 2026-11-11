#!/usr/bin/env python3
"""Generate TlimProc.lean (run from the repository root): the assembly. argv: list of 'Module:label,label,...' for proved
blocks; every other label becomes an explicit hypothesis."""
import sys, re, os
labs = [l.strip() for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'labels.txt')) if l.strip()]
proved = {}
mods = []
for a in sys.argv[1:]:
    m, ls = a.split(':')
    mods.append(m)
    for l in ls.split(','):
        if l:
            proved[l] = m
def short(l):
    s = l.split('.')[-1] if '.' in l else 'entry'
    return s
def full(s):
    return 'sbr_make_f_tablelim' if s == 'entry' else 'sbr_make_f_tablelim.' + s
missing = [l for l in labs if short(l) not in proved]
out = []
out.append('\n'.join(f'import Kraken.X64.Examples.Sbr.Parse.{m}' for m in dict.fromkeys(mods)))
out.append('import Kraken.X64.Examples.Sbr.Parse.TlimGlue')
out.append('''
/-!
# `sbr_make_f_tablelim`: the procedure

`ProcSpec.of_cfg_post` over the block table (`TlimBase.lean`), the entry glue `pre_glue` and the
exit glue `post_glue` (`TlimGlue.lean`). Blocks not proved are explicit hypotheses of `spec`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Tlim
''')
out.append('/-- The labels of the text, in order. -/')
out.append('abbrev labelList : List Label := [' + ',\n  '.join(f'"{l}"' for l in labs) + ']')
out.append('''
theorem labels_body : Program.labels body = labelList := by decide

theorem body_wf : Program.WF body := by decide

variable [CodeEnv]

/-- The procedure from all block obligations. -/
theorem spec_of (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32)
    (hB : ∀ x ra t₀ l, l ∈ labelList → BlockOb k x ra t₀ l) : TlimSpec k := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) (fun x ra t₀ => table k x ra t₀)
    (fun x ra t₀ s => Post' k x ra t₀ s) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
    (hwf := body_wf)
  · intro x ra t₀ l blk h
    have hs : (Program.blockAt body l).isSome = true := by rw [h]; rfl
    rw [Program.isSome_blockAt, ← Program.labels_eq_view, List.contains_iff_mem,
      labels_body] at hs
    exact hB x ra t₀ l hs blk h
  · rintro x ra t ⟨hc, hC⟩
    obtain ⟨stk, pb, hs, hp, hm⟩ := pre_glue hk hc
    exact ⟨rfl, hC, stk, pb, ⟨hC.2.2.2.2.2.1, hs, hp⟩, hm⟩
  · intro x ra t₀ s h
    exact post_glue hk h
''')
hyps = ''.join(f'\n    (h_{short(l)} : ∀ x ra t₀, BlockOb k x ra t₀ "{l}")' for l in missing)
out.append('''/-- `sbr_make_f_tablelim` meets `TlimSpec k`, with `memcpy` as `MemcpyValSpec k`.''' +
  (' The blocks listed as hypotheses are not proved here.' if missing else '') + ''' -/
theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32)
    (hMc : MemcpyValSpec k)''' + hyps + ''' :
    TlimSpec k := by
  refine spec_of hpl k hk fun x ra t₀ l hl => ?_
  simp only [labelList, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with ''' + ' | '.join('rfl' for _ in labs) + '''
''')
for l in labs:
    s = short(l)
    if s in proved:
        out.append(f'  · exact blk_{s} k hk hMc x ra t₀')
    else:
        out.append(f'  · exact h_{s} x ra t₀')
out.append('\nend Kraken.Examples.Sbr.Tlim\n')
open('Kraken/X64/Examples/Sbr/Parse/TlimProc.lean', 'w').write('\n'.join(out))
print('missing', len(missing))
