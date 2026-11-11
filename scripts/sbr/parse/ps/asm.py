#!/usr/bin/env python3
"""The assembly of `ff_ps_read_data` (`Parse/PsEntry.lean`) from its labels.

Usage: python3 scripts/sbr/parse/ps/asm.py Kraken/X64/Examples/Sbr/Parse/PsText.lean \\
    > Kraken/X64/Examples/Sbr/Parse/PsEntry.lean

Every label of the body gets its block obligation either from a proved theorem or from a field
of the structure `PsOpen` (one per open label). The proved theorems are the `theorem blk_<n>`
of the modules in LANDED (only the names listed there): `blk_Entry` is the entry label,
`blk_L<off>` and `blk_<off>` the label `ff_ps_read_data.L<off>`. Each is applied to its
explicit binders by name (`k`, `hk`, `Ext`, `hAv`, `hMs`, `x`, `ra`, `t₀`). An open block that
calls `av_log` or `memset` gets the contract as a hypothesis of its field. When a block gets
proved, add it to LANDED and regenerate.
"""
import os
import re
import sys

P = 'ff_ps_read_data'
PARSE = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                     '../../../../Kraken/X64/Examples/Sbr/Parse')
# module -> the proved block theorems in it (suffix after `blk_`)
LANDED = {
    'PsBlkH0': ['Entry'],
    'PsBlkH1': ['L11'],
    'PsBlkH2': ['L2c', 'L3c', 'Lb6', 'L5b', 'L70', 'L85'],
    'PsBlkH3': ['Laa', 'L148', 'Lbf', 'Ld7', 'Lf3'],
    'PsBlkH4': ['L10b', 'L11d', 'L135', 'L154', 'L16a', 'L185'],
    'PsBlkH5': ['L197', 'L1b0', 'L1be', 'L1c8', 'L1e1'],
    'PsBlkL1': ['715', '71b', '737', '74a'],
    'PsBlkL2': ['760', '775', '798', '7a8', '7d5'],
    'PsBlkL3': ['8d0', '8ed', 'c7a', 'a4c', 'a6a'],
    'PsBlkL4': ['a90', 'aa5', 'ac5', 'aec', 'b01'],
    'PsBlkL5': ['a1e', 'a32', 'a42'],
    'PsBlkL6': ['8bb', '7e0', '8a4', '880', '7f8', '809', '829', '842', '861'],
    'PsBlkL7': ['938', '9cd', '9da', '9f5', '910', '94d', '96f', '983', '996', '9b1'],
    'PsBlkHN1': ['L36e', 'L3aa', 'L689', 'L26e', 'L1fa', 'L216'],
    'PsBlkHN2': ['L277', 'L2b3', 'L2cd', 'L2ec', 'L300', 'L323'],
    'PsBlkHN3': ['L337', 'L35a', 'L297'],
    'PsBlkHN4': ['L22d', 'L6f5', 'L700', 'L259', 'L69c'],
    'PsBlkHN5': ['L6d0'],
    'PsBlkT1L1': ['L1063'],
    'PsBlkT1_2': ['L1119', 'L1157', 'L11a0', 'L11db'],
    'PsBlkT1_3': ['L1148', 'L1192', 'L1104', 'L10f6', 'L11fd'],
    'PsBlkT1_5': ['L1380', 'L1385', 'L138c', 'L1395', 'L13ad', 'L13bd'],
    'PsBlkT1_6': ['L13cd', 'L13dd', 'L13ed'],
    'PsBlkT1_4': ['L12ef', 'L1349', 'L135c', 'L10b4', 'L1084'],
    'PsBlkT1_7': ['L121f', 'L1238', 'L1252', 'L1275', 'L1298', 'L12c5'],
    'PsBlkT1_1': ['L10cf', 'L12ff'],
    'PsBlkT1_8': ['L10d6', 'L132a'],
    'PsBlkT2_1': ['L1759', 'L175e', 'L1763', 'L1768', 'L176d', 'L1772', 'L1777', 'L177c', 'L1781', 'L1786', 'L178b', 'L1790', 'L1795', 'L179a', 'L179f', 'L17a4', 'L17a9', 'L17ae', 'L17b3', 'L17b8', 'L17bd', 'L17c2', 'L17c7', 'L17cc', 'L17d1'],
    'PsBlkLP1': ['Lc86', 'Lc9a', 'Lcaa'],
    'PsBlkLP2': ['Lb20', 'Lb48', 'Lb59', 'Lb75', 'Lb8f', 'Lba9', 'Lbc3'],
    'PsBlkLE1': ['Lbe0', 'Lbf8', 'Lc09', 'Lc29', 'Lc3a', 'Lc5f'],
    'PsBlkT2L1': ['L1404', 'L1499'],
    'PsBlkT2_7': ['L1479'],
    'PsBlkT2_8': ['L14b7', 'done'],
    'PsBlkT2_9': ['L142f', 'L1449'],
    'PsBlkT2_10': ['L13f5'],
    'PsBlkT2_2': ['L14ec', 'L14fd', 'L152a', 'L1557', 'L158c', 'L15c5'],
    'PsBlkT2_3': ['L15fe', 'L1637', 'L1670', 'L16a9', 'L16e2', 'L171b'],
    'PsBlkT2_4': ['L14f1'],
    'PsBlkT2_5': ['L1475', 'L1459'],
    'PsBlkT2_6': ['L14cc', 'L1464'],
    'PsBlkX1': ['cba', 'cc8'],
    'PsBlkX2': ['ce0', 'cf0', 'd08', 'd16', 'd25', 'd3b'],
    'PsBlkX3': ['d70', '104e', 'd7b', 'd93', 'da7', 'dc6'],
    'PsBlkX4': ['d50', 'dd8'],
    'PsBlkX5': ['e00', 'e15', 'e32'],
    'PsBlkX6': ['e4c', 'f5e', 'f29', 'f46'],
    'PsBlkX7': ['eb0', 'fc0', 'ec9', 'fdd'],
    'PsBlkX8': ['e60', 'f70', 'ee0', '1000'],
    'PsBlkX9': ['e80', 'f90', 'f06', '1026'],
}
# entry/exit conversions proved in a landed module (`ps_pre`/`ps_post`), replacing the field
CONV = {'ps_pre': 'PsConv', 'ps_post': 'PsConv'}
CONTRACT = {'av_log': ('AvLogSpec Ext k', 'hAv'), 'memset': ('MemsetValSpec k', 'hMs')}


def labels(path):
  text = open(path).read()
  body = text[text.index('parse("') + 7:text.rindex('")')]
  labs, calls, cur = [], {}, None
  for raw in body.splitlines():
    line = raw.strip()
    if not line:
      continue
    if line.endswith(':') and not raw.startswith(' '):
      cur = line[:-1]
      labs.append(cur)
    m = re.match(r'call\s+(\w+)', line)
    if m and m.group(1) in CONTRACT:
      calls.setdefault(cur, []).append(m.group(1))
  return labs, calls


def suffix(l):
  return '' if l == P else l[len(P) + 1:]


def proved():
  out = {}
  for mod, names in LANDED.items():
    txt = open(os.path.join(PARSE, mod + '.lean')).read()
    for n in names:
      m = re.search(rf'^theorem blk_{n}\b(.*?)BlockOb', txt, re.M | re.S)
      if not m:
        sys.exit(f'{mod}: no theorem blk_{n}')
      binders = []
      for b in re.finditer(r'\(([^():]+?) :', m.group(1)):
        binders += b.group(1).split()
      lab = '' if n == 'Entry' else (n if n.startswith('L') or n == 'done' else 'L' + n)
      out[lab] = (f'blk_{n}', ' '.join(binders))
  return out


def main():
  labs, calls = labels(sys.argv[1])
  pr = proved()
  o = ['\n'.join(f'import Kraken.X64.Examples.Sbr.Parse.{m}' for m in ['LibCall'] + list(dict.fromkeys(list(LANDED) + list(CONV.values())))), '''
-- Generated by scripts/sbr/parse/ps/asm.py. Do not edit.

/-!
# `ff_ps_read_data`: the assembly

`spec`: `ff_ps_read_data` meets `PsPre`/`PsPost` (`PsReadSpec`), from the block obligations of
`table`/`var` (`PsBase.lean`): each block's obligation is the `blk_` theorem of its module, the
entry and exit conversions are `ps_pre`/`ps_post` (`PsConv.lean`); blocks not yet proved (if
any) are the fields of `PsOpen`. The callee
contracts: `av_log` (`AvLogSpec`), `memset` (`MemsetValSpec`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

/-- The labels of `body`, in order. -/
def psLabels : List Label := [''']
  o[-1] += ',\n'.join(f'  "{l}"' if i else f'"{l}"' for i, l in enumerate(labs)) + ']'
  o.append('''
omit [CodeEnv] in
theorem labels_body : Program.labels body = psLabels := by decide +kernel

/-- A number key of a label (its characters as base-256 digits), for the uniqueness check:
`decide` on the strings themselves exhausts memory at this many labels. -/
def psKey (s : String) : Nat := s.toList.foldl (fun n c => n * 256 + c.toNat) 0

omit [CodeEnv] in
set_option maxRecDepth 200000 in
theorem psLabels_nodup : psLabels.Nodup :=
  (List.pairwise_map.mp (show (psLabels.map psKey).Nodup by decide +kernel)).imp
    fun h e => h (congrArg psKey e)

omit [CodeEnv] in
theorem body_wf : Program.WF body := ⟨labels_body ▸ psLabels_nodup⟩''')
  fields = []
  for l in labs:
    s = suffix(l)
    if s in pr:
      continue
    hs = ''.join(CONTRACT[c][0] + ' → ' for c in dict.fromkeys(calls.get(l, [])))
    fields.append(f'  {s} : {hs}∀ x ra t₀, BlockOb k Ext x ra t₀ "{l}"')
  nopen = len(fields)
  if 'ps_pre' not in CONV:
    fields.append(f'  pre : ∀ x ra t, PsPre k Ext x ra t → table k Ext x ra t "{P}" t')
  if 'ps_post' not in CONV:
    fields.append("  post : ∀ x ra t₀ s, Post' k Ext x ra t₀ s → PsPost k Ext x ra t₀ s")
  if fields:
    o.append('''
/-- The open obligations: the blocks not yet proved, and the conversions between
`PsPre`/`PsPost` and the table's entry/`Post'`. -/
structure PsOpen (k : Nat) (Ext : Mem 64 → Prop) : Prop where''')
    o += fields
  hO = ' (hO : PsOpen k Ext)' if fields else ''
  given = f', given the open obligations\n({len(labs) - nopen} of {len(labs)} blocks proved)' if fields else f'\n(all {len(labs)} blocks proved)'
  pre = '(ps_pre k hk Ext)' if 'ps_pre' in CONV else 'hO.pre'
  post = '(ps_post k hk Ext)' if 'ps_post' in CONV else 'hO.post'
  o.append(f'''
set_option maxRecDepth 200000 in
/-- `ff_ps_read_data` meets its contract{given}. -/
theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (hAv : AvLogSpec Ext k) (hMs : MemsetValSpec k){hO} :
    PsReadSpec k Ext := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := body) (fun x ra t₀ => table k Ext x ra t₀)
    (fun x ra t₀ => Post' k Ext x ra t₀) var ?_ {pre} {post} (hwf := body_wf)
  intro x ra t₀ l blk hblk
  have hl := Program.blockAt_mem_labels hblk
  rw [labels_body] at hl
  simp only [psLabels, List.mem_cons, List.not_mem_nil, or_false] at hl''')
  o.append('  rcases hl with ' + ' | '.join(['rfl'] * len(labs)))
  for l in labs:
    s = suffix(l)
    if s in pr:
      n, a = pr[s]
      o.append(f'  · exact {n} {a} blk hblk')
    else:
      hs = ''.join(CONTRACT[c][1] + ' ' for c in dict.fromkeys(calls.get(l, [])))
      o.append(f'  · exact hO.{s or "Entry"} {hs}x ra t₀ blk hblk')
  o.append('\nend Kraken.Examples.Sbr.Ps')
  print('\n'.join(o))


if __name__ == '__main__':
  main()
