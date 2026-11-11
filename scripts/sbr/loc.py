#!/usr/bin/env python3
"""Line counts of the SBR development, classified by purpose.

Usage: python3 scripts/sbr/loc.py [BASE [HEAD]] [--json FILE]
  BASE defaults to 28ca345 (the commit before the SBR work), HEAD to HEAD.

Counts the lines added between BASE and HEAD (`git diff --numstat`). Every line of a new
.lean file is attributed to the top-level declaration it belongs to (a declaration runs
until the next top-level keyword): `blk_*` theorems are block proofs, `spec*` theorems are
procedure compositions, other theorems are lemmas, def/abbrev/structure are definitions,
`parse("...")` strings are program texts, macro/syntax/elab are tactics. Comments, blank
lines, imports and `open`/`namespace`/`section`/`set_option` lines are counted separately.
For .lean files that existed at BASE only the added-line count is reported
("modified(+)"). Files are grouped by purpose (procedure proofs, headline, library,
generated rules, tests, tooling). The numbers in the document's "Development effort"
section come from this script.
"""
import re, subprocess, os, sys, json, collections

args = [a for a in sys.argv[1:]]
json_out = None
if '--json' in args:
    i = args.index('--json'); json_out = args[i + 1]; del args[i:i + 2]
BASE = args[0] if len(args) > 0 else '28ca345'
HEAD = args[1] if len(args) > 1 else 'HEAD'
ROOT = subprocess.run(['git', 'rev-parse', '--show-toplevel'], capture_output=True, text=True,
                      cwd=os.path.dirname(os.path.abspath(__file__))).stdout.strip()
os.chdir(ROOT)

num = subprocess.run(['git', 'diff', '--numstat', BASE, HEAD], capture_output=True, text=True).stdout
files = []
for l in num.splitlines():
    a, d, f = l.split('\t')
    if a == '-':
        continue
    files.append((f, int(a), int(d)))

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |partial |unsafe )*'
                  r'(theorem|lemma|def|abbrev|structure|instance|macro_rules|macro|syntax|elab_rules|elab|'
                  r'example|inductive|class|opaque|axiom)\b\s*(\S*)')
OTHER = re.compile(r'^\s*($|--|import |open |namespace |end\b|section\b|set_option |variable |attribute |#)')


def classify_lean(path):
    """Return Counter over line kinds for a whole (new) file."""
    c = collections.Counter()
    kind = 'other'
    in_doc = False
    in_parse = False
    for l in open(path, encoding='utf-8', errors='replace'):
        s = l.rstrip('\n')
        if in_doc:
            c['comment'] += 1
            if '-/' in s:
                in_doc = False
            continue
        if s.lstrip().startswith('/-'):
            c['comment'] += 1
            if '-/' not in s[s.find('/-') + 2:]:
                in_doc = True
            continue
        if in_parse:
            c['program'] += 1
            if '")' in s:
                in_parse = False
            continue
        m = DECL.match(s)
        if m:
            kw, name = m.group(1), m.group(2)
            if 'parse("' in s:
                c['program'] += 1
                in_parse = '")' not in s
                kind = 'program'
                continue
            if kw in ('theorem', 'lemma', 'example'):
                if re.match(r'(.*\.)?blk_', name):
                    kind = 'block'
                elif name.split('.')[-1] in ('spec', 'does', 'specSse', 'specAvx', 'specFma3', 'specAvx2',
                                             'spec3') or name.startswith('spec'):
                    kind = 'compose'
                else:
                    kind = 'lemma'
            elif kw in ('def', 'abbrev', 'structure', 'inductive', 'class', 'instance', 'opaque'):
                kind = 'defn'
            elif kw in ('macro', 'macro_rules', 'syntax', 'elab', 'elab_rules'):
                kind = 'tactic'
            else:
                kind = 'other'
            c[kind] += 1
            continue
        if OTHER.match(s) and not s.startswith('  '):
            c['other'] += 1
            if s.startswith(('end', 'namespace', 'section', 'open', 'import', 'set_option', '#')):
                kind = 'other'
            continue
        if s.strip() == '' or s.strip().startswith('--'):
            c['other' if s.strip() == '' else 'comment'] += 1
            continue
        c[kind] += 1
    return c


def group(f):
    if f.startswith('Kraken/X64/Examples/Sbr/'):
        r = f[len('Kraken/X64/Examples/Sbr/'):]
        if r in ('Link.lean', 'Witness.lean', 'Linked.lean', 'Placement.lean'):
            return 'headline'
        if r in ('Spec.lean', 'ApplySpec.lean'):
            return 'contracts'
        if r in ('Dsp.lean', 'FloatDsp.lean'):
            return 'headline'
        if r.startswith('Apply') or r == 'Apply.lean':
            return 'proc:ff_aac_sbr_apply'
        if r.startswith('HfAssemble'):
            return 'proc:sbr_hf_assemble'
        if r.startswith('Dsp/'):
            return 'proc:dsp leaves (sbrdsp+float_dsp)'
        return 'proc:' + {'XGen.lean': 'sbr_x_gen', 'QmfSynthesis.lean': 'sbr_qmf_synthesis',
                          'LfGen.lean': 'sbr_lf_gen', 'HfInverseFilter.lean': 'sbr_hf_inverse_filter',
                          'DequantFloat.lean': 'dequant float model (R1)'}.get(r, r)
    if f.startswith('KrakenSbrReal'):
        return 'headline-optional'
    if f.startswith('scripts/sbr/apply/'):
        return 'generator-src (apply; output already counted above)'
    if f.startswith('scripts/sbr/hfasm/'):
        return 'generator-src (hfasm; output already counted above)'
    if f.startswith('scripts/sbr/') and f.endswith('.lean'):
        return 'tooling-lean'
    if f.startswith('Kraken/X64/Examples/') or 'Tests' in f or f.startswith('Kraken/X64/Test/'):
        return 'lib-tests'
    if f.startswith('Kraken/Rules/gen/') or f.endswith('.lean.in'):
        return 'lib-gen-src'
    if f.startswith('Kraken') and f.endswith('.lean'):
        if f in ('Kraken/Rules/IntMisc.lean', 'Kraken/Rules/PackedSse.lean', 'Kraken/Rules/ScalarFloat.lean'):
            return 'lib-generated-rules'
        return 'lib'
    if f.startswith('scripts/'):
        return 'tooling-other'
    return 'misc'


out = collections.defaultdict(collections.Counter)
modified = []
for f, a, d in files:
    g = group(f)
    if f.endswith('.lean'):
        if d == 0 and a == sum(1 for _ in open(f, encoding='utf-8', errors='replace')):
            c = classify_lean(f)
        else:
            c = collections.Counter({'modified(+)': a})
            modified.append((f, a, d))
        out[g].update(c)
        out[g]['total'] += a
    else:
        out[g]['nonlean'] += a
if json_out:
    json.dump({k: dict(v) for k, v in out.items()}, open(json_out, 'w'), indent=1)
for g in sorted(out):
    print(g, dict(out[g]))
print('modified existing lean files:', modified)
