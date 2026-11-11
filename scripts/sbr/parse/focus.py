#!/usr/bin/env python3
"""Footprint focus library for a parser routine, generated from a layout description.

Usage: focus.py LAYOUT.py > Foot.lean

A footprint is a separating conjunction of cells. Automation (`grind`, `simp`) does not scale
with its size, so a block proof never searches it: it rewrites the footprint with an AC
equation that brings the cells it touches to the front, and applies a small access lemma.
This script writes, from a layout (a Python file defining `LAYOUT`, see layouts/grid.py):

  * the byte arrays as opaque groups of 1-byte cells (`arrays`), with the access lemmas at a
    variable index, proved once by a case split inside the lemma (`<A>_loadInt`,
    `<A>_storeInt`);
  * the other opaque groups (`groups`) and the footprint `T` (an `abbrev`);
  * one AC equation per focus target (`focus`): `T_<x> : T … = X ⋆ Tx<X> …` (`eq`) or
    `T_<x> : ∃ F, T … = X ⋆ F` (`exists`) or, from a memory hypothesis,
    `T_<x> : m =⋆ T … → ∃ F, m =⋆ X ⋆ F` (`hyp`); the proof is `simp only [defs]; ac_rfl`;
  * custom equations (`custom`), for example the footprint with the saved registers unfolded;
  * the access lemmas through `T` (`access`): loads and stores of 4-byte and 8-byte cells,
    raw slots, and array bytes at a variable index or a constant offset.

Layout keys (all strings are Lean text):
  namespace, header (imports/opens), doc,
  params (binders of T), args (T's arguments, same order),
  arrays: [{name, base (param name), off, len, list (param name)}]  (def NAME base list)
  groups: [{name, params: [names], binders, body: [item], kind: def|abbrev, emit: bool}]
  T: [item]   (right-nested `⋆`)
  item: "lean text" | {"g": GROUP, "a": [actual, ...]} | {"name": N, "e": "lean text"}
  focus: [{lemma, target: [atom name or "group:args-text"], mode: eq|exists|hyp, tx: NAME}]
  custom: [{lemma, binders, lhs, rhs, unfold: [names]}]
  access: [{kind: cell4|cell8|cell1|slot|array|array_list, ...}]  (see the emitters below)
"""
import re
import runpy
import sys


def subst(text, env):
  """Replace the parameter names in `text` by their actuals."""
  if not env:
    return text
  pat = re.compile(r"(?<![\w.'])(" + "|".join(map(re.escape, env)) + r")(?![\w'])")
  return pat.sub(lambda m: env[m[1]], text)


def wrapped(a):
  """`a` is one parenthesized group."""
  if not (a.startswith("(") and a.endswith(")")):
    return False
  d = 0
  for i, c in enumerate(a):
    d += c == "("
    d -= c == ")"
    if d == 0 and i < len(a) - 1:
      return False
  return True


def paren(a):
  a = a.strip()
  return a if re.fullmatch(r"[\w.'₀-₉]+", a) or wrapped(a) else f"({a})"


def wrap(line, indent="    ", width=100):
  """Break a long line at ` ⋆ ` (Lean ignores the layout inside a term)."""
  if len(line) <= width:
    return line
  parts = line.split(" ⋆ ")
  out, cur = [], parts[0]
  for p in parts[1:]:
    if len(cur) + 3 + len(p) > width:
      out.append(cur)
      cur = indent + "⋆ " + p
    else:
      cur += " ⋆ " + p
  out.append(cur)
  return "\n".join(out)


class Gen:
  def __init__(self, L):
    self.L = L
    self.groups = {g["name"]: g for g in L.get("groups", [])}
    for a in L.get("arrays", []):
      self.groups[a["name"]] = {
          "name": a["name"], "params": ["d", "l"], "kind": "def", "emit": False,
          "body": [{"name": f"{a['name']}[{j}]",
                    "e": f"cell1 (d + {hex(a['off'] + j)}#64) (bv l {j})"} for j in range(a["len"])]}
    self.out = []

  def p(self, s=""):
    self.out.append("\n".join(wrap(l) for l in s.split("\n")))

  # ---- trees
  def item_text(self, it, env):
    if isinstance(it, str):
      return subst(it, env)
    if "g" in it:
      return " ".join([it["g"]] + [paren(subst(a, env)) for a in it["a"]])
    return subst(it["e"], env)

  def sep(self, xs):
    if not xs:
      return "Std.ExtHashMap.emp"
    s = xs[-1]
    for x in reversed(xs[:-1]):
      s = f"{x} ⋆ ({s})" if " ⋆ " in s else f"{x} ⋆ {s}"
    return s

  def flat(self, items, env, path):
    """Flatten: (name, text) per atom; groups whose name is in `path` are inlined, the
    others kept as one atom (named by the group's application text and its name)."""
    res = []
    for it in items:
      if isinstance(it, dict) and "g" in it:
        g = self.groups[it["g"]]
        txt = self.item_text(it, env)
        if it["g"] in path:
          env2 = {p: paren(subst(a, env)) for p, a in zip(g["params"], it["a"])}
          res += self.flat(g["body"], env2, path)
        else:
          res.append((it["g"], txt))
      elif isinstance(it, dict):
        res.append((it["name"], subst(it["e"], env)))
      else:
        res.append((it, subst(it, env)))
    return res

  def path_to(self, name, items, env, seen=()):
    """The groups to inline to expose atom/group `name`."""
    for it in items:
      if isinstance(it, dict) and "g" in it:
        if it["g"] == name:
          return []
        g = self.groups[it["g"]]
        env2 = {p: paren(subst(a, env)) for p, a in zip(g["params"], it["a"])}
        r = self.path_to(name, g["body"], env2)
        if r is not None:
          return [it["g"]] + r
      elif isinstance(it, dict) and it["name"] == name:
        return []
    return None

  # ---- emit
  def emit_groups(self):
    L = self.L
    for a in L.get("arrays", []):
      cells = [f"cell1 (d + {hex(a['off'] + j)}#64) (bv l {j})" for j in range(a["len"])]
      self.p(f"/-- `{a['doc']}`: {a['len']} bytes at offset `{hex(a['off'])}`, one cell per byte. -/"
             if a.get("doc") else f"/-- {a['len']} bytes at offset `{hex(a['off'])}`. -/")
      self.p(f"def {a['name']} (d : BitVec 64) (l : List UInt8) : Mem 64 → Prop :=")
      self.p("  " + self.sep(cells))
      self.p()
    for g in L.get("groups", []):
      if not g.get("emit", True):
        continue
      if g.get("doc"):
        self.p(f"/-- {g['doc']} -/")
      self.p(f"{g.get('kind', 'def')} {g['name']} {g['binders']} : Mem 64 → Prop :=")
      self.p("  " + self.sep([self.item_text(i, {}) for i in g["body"]]))
      self.p()
    self.p(f"/-- {L.get('Tdoc', 'The footprint.')} -/")
    self.p(f"abbrev T {L['params']} : Mem 64 → Prop :=")
    self.p("  " + self.sep([self.item_text(i, {}) for i in L["T"]]))
    self.p()

  def impl_params(self):
    # turn each top-level `(a b : τ)` binder into `{a b : τ}`
    out, depth, cur = [], 0, ""
    for ch in self.L["params"]:
      if ch == "(" and depth == 0:
        cur = ""; depth = 1; continue
      if ch == "(":
        depth += 1
      if ch == ")":
        depth -= 1
        if depth == 0:
          out.append("{" + cur + "}"); continue
      if depth > 0:
        cur += ch
    return " ".join(out)

  def focus_eq(self, f):
    """Emit Tx abbrev + the equation; return the equation lemma's name."""
    L = self.L
    targets = f["target"]
    path = set()
    for t in targets:
      pth = self.path_to(t, L["T"], {})
      if pth is None:
        raise SystemExit(f"focus {f['lemma']}: no atom/group {t}")
      path |= set(pth)
    atoms = self.flat(L["T"], {}, path)
    names = [n for n, _ in atoms]
    front = []
    for t in targets:
      i = names.index(t)
      front.append(atoms[i][1])
    rest = [txt for n, txt in atoms if n not in targets]
    tx = f.get("tx", "Tx_" + f["lemma"])
    unf = ["T"] + sorted(path)
    self.p(f"/-- `T` without {', '.join('`' + t + '`' for t in targets)}. -/")
    self.p(f"abbrev {tx} {L['params']} : Mem 64 → Prop :=")
    self.p("  " + self.sep(rest))
    self.p()
    eqn = f["lemma"] if f.get("mode", "eq") == "eq" else f["lemma"] + "_eq"
    self.p(f"theorem {eqn} {L['params']} :")
    self.p(f"    T {L['args']} = {self.sep(front + [tx + ' ' + L['args']])} := by")
    self.p(f"  simp only [{', '.join(unf + [tx])}]; ac_rfl")
    self.p()
    mode = f.get("mode", "eq")
    lhs_front = self.sep(front + ["F"])
    if mode == "exists":
      self.p(f"theorem {f['lemma']} {L['params']} :")
      self.p(f"    ∃ F, T {L['args']} = {lhs_front} :=")
      self.p(f"  ⟨_, {eqn} {L['args']}⟩")
      self.p()
    elif mode == "hyp":
      self.p(f"theorem {f['lemma']} {{m : Mem 64}} {self.impl_params()}")
      self.p(f"    (h : m =⋆ T {L['args']}) : ∃ F, m =⋆ {lhs_front} :=")
      self.p(f"  ⟨_, focus ({eqn} {L['args']}) h⟩")
      self.p()
    return eqn

  def emit_focus(self):
    self.eqs = {}
    for f in self.L.get("focus", []):
      self.eqs[tuple(f["target"])] = (self.focus_eq(f), f)

  def emit_custom(self):
    for c in self.L.get("custom", []):
      if c.get("doc"):
        self.p(f"/-- {c['doc']} -/")
      self.p(f"theorem {c['lemma']} {c['binders']} :")
      self.p(f"    {c['lhs']} = {c['rhs']} := by")
      self.p(f"  simp only [{', '.join(c['unfold'])}]; ac_rfl")
      self.p()

  def eq_of(self, atom):
    e = self.eqs.get((atom,))
    if not e:
      raise SystemExit(f"access: no single-atom focus for {atom}")
    return e[0]

  def emit_access(self):
    L = self.L
    imp = self.impl_params()
    args = L["args"]
    for a in L.get("access", []):
      k = a["kind"]
      eqn = self.eq_of(a["atom"]) if k != "array_list" else None
      if a.get("doc"):
        self.p(f"/-- {a['doc']} -/")
      if k in ("cell4", "cell8", "cell1"):
        w = {"cell4": 4, "cell8": 8, "cell1": 1}[k]
        bw = {"cell4": 32, "cell8": 64, "cell1": 8}[k]
        if a.get("load"):
          self.p(f"theorem {a['load']} {{m : Mem 64}} {imp}")
          self.p(f"    (h : m =⋆ T {args}) :")
          self.p(f"    m.loadInt {paren(a['addr'])} {w} = some (Int.ofBytes (Int.toBytes {w} {a['val']}.toInt)) :=")
          self.p(f"  {k}_load (focus ({eqn} {args}) h)")
          self.p()
          if a.get("doc") and a.get("store"):
            self.p(f"/-- {a['doc']} -/")
        if a.get("store"):
          args2 = subst(args, {a["stvar"]: paren(a["upd"].format(v="v"))})
          self.p(f"theorem {a['store']} {{m : Mem 64}} {imp}")
          self.p(f"    (h : m =⋆ T {args}) (v : BitVec {bw}) :")
          self.p(f"    m.storeInt {paren(a['addr'])} {w} v.toInt =⋆ T {args2} := by")
          self.p(f"  rw [{eqn}] at h ⊢")
          self.p(f"  exact {k}_store h v")
          self.p()
      elif k == "slot":
        n = a["size"]
        if a.get("load"):
          self.p(f"theorem {a['load']} {{m : Mem 64}} {imp}")
          self.p(f"    (h : m =⋆ T {args}) (k' : Nat) (hk : k' ≤ {n}) :")
          self.p(f"    (m.loadInt {paren(a['addr'])} k').isSome = true :=")
          self.p(f"  slot_load (focus ({eqn} {args}) h) hk")
          self.p()
        if a.get("store"):
          self.p(f"theorem {a['store']} {{m : Mem 64}} {imp}")
          self.p(f"    (h : m =⋆ T {args}) (v : Int) :")
          self.p(f"    m.storeInt {paren(a['addr'])} {a.get('width', n)} v =⋆ T {args} := by")
          self.p(f"  rw [{eqn}] at h ⊢")
          self.p(f"  exact slot_store h (by omega) v")
          self.p()
      elif k == "array_list":
        self.emit_array_list(a)
      elif k == "array":
        self.emit_array(a, eqn, imp, args)
      else:
        raise SystemExit(f"unknown access kind {k}")

  def emit_array_list(self, a):
    arr = next(x for x in self.L["arrays"] if x["name"] == a["array"])
    nm, n, off = arr["name"], arr["len"], arr["off"]
    cases = " ∨ ".join(f"j = {i}" for i in range(n))
    pats = " | ".join("rfl" for _ in range(n))
    self.p(f"/-- Byte `j` of `{nm}`. -/")
    self.p(f"theorem {nm}_loadInt {{m : Mem 64}} {{d : BitVec 64}} {{l : List UInt8}} {{R : Mem 64 → Prop}}")
    self.p(f"    (h : m =⋆ {nm} d l ⋆ R) (j : Nat) (hj : j < {n}) :")
    self.p(f"    m.loadInt (d + BitVec.ofNat 64 j + {hex(off)}#64) 1")
    self.p(f"      = some (Int.ofBytes (Int.toBytes 1 (bv l j).toInt)) := by")
    self.p(f"  simp only [{nm}] at h")
    self.p(f"  rcases (by omega : {cases})")
    self.p(f"    with {pats} <;>")
    self.p(f"    simp only [BitVec.add_assoc, BitVec.reduceAdd] <;> cells_grind")
    self.p()
    self.p(f"/-- Store to byte `j` of `{nm}`. -/")
    self.p(f"theorem {nm}_storeInt {{m : Mem 64}} {{d : BitVec 64}} {{l : List UInt8}} {{R : Mem 64 → Prop}}")
    self.p(f"    (h : m =⋆ {nm} d l ⋆ R) (hl : l.length = {n}) (j : Nat) (hj : j < {n}) (v : BitVec 8) :")
    self.p(f"    m.storeInt (d + BitVec.ofNat 64 j + {hex(off)}#64) 1 v.toInt")
    self.p(f"      =⋆ {nm} d (l.set j (UInt8.ofBitVec v)) ⋆ R := by")
    self.p(f"  simp only [{nm}] at h ⊢")
    self.p(f"  simp only [bv, getD_set_if l j _ _ (by omega)]")
    self.p(f"  rcases (by omega : {cases})")
    self.p(f"    with {pats} <;>")
    self.p(f"    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceEqDiff,")
    self.p(f"      ↓reduceIte, UInt8.toBitVec_ofBitVec] <;> cells_grind")
    self.p()

  def emit_array(self, a, eqn, imp, args):
    arr = next(x for x in self.L["arrays"] if x["name"] == a["atom"])
    nm, n, off = arr["name"], arr["len"], arr["off"]
    base, lst = a["base"], a["list"]
    sv = a["stvar"]
    upd = lambda j, v: subst(args, {sv: paren(a["upd"].format(j=j, v=v))})
    S = a["suffix"]
    # variable index
    self.p(f"/-- Load of byte `j` of `{nm}` through `T`. -/")
    self.p(f"theorem T_load{S} {{m : Mem 64}} {imp}")
    self.p(f"    (h : m =⋆ T {args}) (j : Nat) (hj : j < {n}) :")
    self.p(f"    m.loadInt ({base} + BitVec.ofNat 64 j + {hex(off)}#64) 1")
    self.p(f"      = some (Int.ofBytes (Int.toBytes 1 (bv {lst} j).toInt)) :=")
    self.p(f"  {nm}_loadInt (focus ({eqn} {args}) h) j hj")
    self.p()
    self.p(f"/-- Store to byte `j` of `{nm}` through `T`. -/")
    self.p(f"theorem T_store{S} {{m : Mem 64}} {imp}")
    self.p(f"    (h : m =⋆ T {args}) (hl : {lst}.length = {n}) (j : Nat) (hj : j < {n}) (v : BitVec 8) :")
    self.p(f"    m.storeInt ({base} + BitVec.ofNat 64 j + {hex(off)}#64) 1 v.toInt =⋆ T {upd('j', 'v')} := by")
    self.p(f"  rw [{eqn}] at h ⊢")
    self.p(f"  exact {nm}_storeInt h hl j hj v")
    self.p()
    # constant offset
    self.p(f"theorem {S}O_addr (d o : BitVec 64) (ho : {hex(off)} ≤ o.toNat ∧ o.toNat < {hex(off)} + {n}) :")
    self.p(f"    d + BitVec.ofNat 64 (o.toNat - {hex(off)}) + {hex(off)}#64 = d + o := by")
    self.p(f"  rw [BitVec.add_assoc]; apply congrArg (d + ·)")
    self.p(f"  apply BitVec.eq_of_toNat_eq")
    self.p(f"  rw [BitVec.toNat_add, BitVec.toNat_ofNat]")
    self.p(f"  have : ({hex(off)}#64).toNat = {hex(off)} := rfl")
    self.p(f"  rw [this]")
    self.p(f"  have h2 : o.toNat - {hex(off)} < 2 ^ 64 := by omega")
    self.p(f"  rw [Nat.mod_eq_of_lt h2, Nat.sub_add_cancel ho.1, Nat.mod_eq_of_lt o.isLt]")
    self.p()
    self.p(f"/-- Load of `{nm}` at a constant offset `o` from the base (byte `o - {hex(off)}`). -/")
    self.p(f"theorem T_load{S}O {{m : Mem 64}} {imp} {{o : BitVec 64}}")
    self.p(f"    (ho : {hex(off)} ≤ o.toNat ∧ o.toNat < {hex(off)} + {n}) (h : m =⋆ T {args}) :")
    self.p(f"    m.loadInt ({base} + o) 1")
    self.p(f"      = some (Int.ofBytes (Int.toBytes 1 (bv {lst} (o.toNat - {hex(off)})).toInt)) := by")
    self.p(f"  rw [← {S}O_addr _ _ ho]")
    self.p(f"  exact T_load{S} h _ (by omega)")
    self.p()
    self.p(f"/-- Store to `{nm}` at a constant offset `o` from the base. -/")
    self.p(f"theorem T_store{S}O {{m : Mem 64}} {imp} {{o : BitVec 64}}")
    self.p(f"    (ho : {hex(off)} ≤ o.toNat ∧ o.toNat < {hex(off)} + {n}) (h : m =⋆ T {args})")
    self.p(f"    (hl : {lst}.length = {n}) (v : BitVec 8) :")
    self.p(f"    m.storeInt ({base} + o) 1 v.toInt =⋆ T {upd('(o.toNat - ' + hex(off) + ')', 'v')} := by")
    self.p(f"  rw [← {S}O_addr _ _ ho]")
    self.p(f"  exact T_store{S} h hl _ (by omega) v")
    self.p()

  def run(self):
    L = self.L
    self.p("-- Generated by scripts/sbr/parse/focus.py from " + L["source"] + ". Do not edit.")
    self.p(L["header"].strip())
    self.p()
    self.p("/-!")
    self.p(L["doc"].strip())
    self.p("-/")
    self.p()
    self.p(L.get("opens", "").strip())
    self.p()
    self.p(f"namespace {L['namespace']}")
    self.p()
    self.p(L.get("prelude", "").strip())
    self.p()
    self.emit_groups()
    self.emit_focus()
    self.emit_custom()
    self.emit_access()
    self.p(f"end {L['namespace']}")
    return "\n".join(self.out).replace("\n\n\n", "\n\n") + "\n"


def main():
  L = runpy.run_path(sys.argv[1])["LAYOUT"]
  sys.stdout.write(Gen(L).run())


main()
