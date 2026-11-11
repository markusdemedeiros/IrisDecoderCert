#!/usr/bin/env python3
"""split.py FULL.lean OUT.lean K: split the generated HfAssemble text into modules.

  OUT                     = .../Sbr/HfAssemble.lean: the module doc, imports of the parts, `spec`
  OUT-dir/Base.lean       = .../Sbr/HfAssemble/Base.lean: the table, the lemmas, macros
                            (the text `body` is in HfAssembleText.lean, written by build.sh)
  OUT-dir/Part<i>.lean    = the `blk_*` theorems, i = 1..K, balanced by measured heartbeats
                            (hb_table.txt; unknown blocks count 100k)
All declarations keep their names (same namespace). K = 0: write FULL to OUT unchanged
(and delete Base/Part*.lean of an earlier split).
"""
import os, re, sys

full_p, out_p, k = sys.argv[1], sys.argv[2], int(sys.argv[3])
txt = open(full_p).read()
d = os.path.splitext(out_p)[0]
if k == 0:
    open(out_p, 'w').write(txt)
    if os.path.isdir(d):  # drop the modules of an earlier split
        for f in os.listdir(d):
            if re.match(r'(Base|Part\d+)\.lean$', f):
                os.remove(os.path.join(d, f))
    sys.exit(0)

NS = 'Kraken.Examples.Sbr.HfAssemble'
MOD = 'Kraken.X64.Examples.Sbr.HfAssemble'
END = f'end {NS}\n'
txt = txt.rstrip('\n') + '\n'  # (the generator leaves a blank line after `end`)
assert txt.endswith(END)

# imports / module doc / preamble (opens, options, namespace)
i_doc = txt.index('/-!')
imports = txt[:i_doc]
i_open = txt.index('\nopen Kraken\n') + 1
doc = txt[i_doc:i_open]
i_ns = txt.index(f'namespace {NS}\n') + len(f'namespace {NS}\n')
preamble = txt[i_open:i_ns]

# block region: from the first block theorem (with its option prefix) to `spec`
blk_re = re.compile(r'^(?:set_option \w+ \d+ in\n)*theorem blk_(\w+) ', re.M)
starts = [(m.start(), m.group(1)) for m in blk_re.finditer(txt)]
i_spec = txt.index('\ntheorem spec (hpl') + 1
# include a comment/blank run directly preceding spec in spec
body_end = i_spec
base = txt[i_ns:starts[0][0]]
blocks = []
for (a, nm), nxt in zip(starts, [s for s, _ in starts[1:]] + [body_end]):
    blocks.append((nm, txt[a:nxt]))
spec = txt[body_end:len(txt) - len(END)]
# nothing but blocks between the first block and spec
assert all(re.match(r'(?:set_option \w+ \d+ in\n)*theorem blk_', b) for _, b in blocks)
assert 'variable [CodeEnv]' in base

here = os.path.dirname(os.path.abspath(__file__))
cost = {}
hbf = os.path.join(here, 'hb_table.txt')
if os.path.exists(hbf):
    for l in open(hbf):
        p = l.split()
        if len(p) >= 2:
            cost[p[0]] = int(p[1])
# longest-processing-time assignment; each part keeps the text order of its blocks
parts = [[] for _ in range(k)]
load = [0] * k
order = {nm: j for j, (nm, _) in enumerate(blocks)}
for nm, _ in sorted(blocks, key=lambda b: -cost.get(b[0], 100000)):
    j = min(range(k), key=lambda j: load[j])
    parts[j].append(nm)
    load[j] += cost.get(nm, 100000)
text = dict(blocks)

d = os.path.splitext(out_p)[0]
os.makedirs(d, exist_ok=True)
for f in os.listdir(d):
    if re.match(r'(Base|Part\d+)\.lean$', f):
        os.remove(os.path.join(d, f))

def write(p, s):
    open(p, 'w').write(s)

write(os.path.join(d, 'Base.lean'), imports
      + '/-! `sbr_hf_assemble`: the label table, the frames and the lemmas of the block proofs.\n'
      + f'The text is in `HfAssembleText.lean`, the block theorems in `HfAssemble/Part*.lean`, `spec`\n'
      + f'in `HfAssemble.lean`. -/\n\n'
      + preamble + base.rstrip('\n') + '\n\n' + END)
for j, ps in enumerate(parts, 1):
    ps.sort(key=lambda nm: order[nm])
    write(os.path.join(d, f'Part{j}.lean'), f'import {MOD}.Base\n\n'
          + f'/-! `sbr_hf_assemble`: block theorems, part {j} of {k} (generated; the split balances\n'
          + 'the measured heartbeats). -/\n\n'
          + preamble + '\nvariable [CodeEnv]\n\n'
          + ''.join(text[nm] for nm in ps).rstrip('\n') + '\n\n' + END)
write(out_p, ''.join(f'import {MOD}.Part{j}\n' for j in range(1, k + 1)) + '\n' + doc
      + preamble + '\nvariable [CodeEnv]\n\n' + spec.lstrip('\n') + END)
print('split:', ' '.join(f'Part{j}={len(ps)} blocks/{load[j-1] // 1000}k' for j, ps in enumerate(parts, 1)))
