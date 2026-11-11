#!/usr/bin/env python3
"""Generate the per-width rules of Kraken/Rules/IntMisc.lean (M0.4c).

Every rule is emitted once per operand width, with sub-register reads and
writes spelled on the 64-bit register file (as the 32- and 8-bit rules of
MachineWP.lean are), so `grind` sees `get64`/`set64` only.

Usage: gen2.py OUT.lean RULES.txt
"""
import sys

MEM = "(.mem ⟨some (.reg rb), idx, .int64 d⟩)"
ADDR = "s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec"
MEMPARAMS = "(rb : Reg64) (idx : Option AddrIndex) (d : Int64)"
WN = {8: ".W8", 16: ".W16", 32: ".W32", 64: ".W64"}
BYTES = {8: 1, 16: 2, 32: 4, 64: 8}

out = []
rules = []


def emit(s):
  out.append(s)


def rget(r, n):
  if n == 64:
    return f"s.regs.get64 {r}"
  return f"(s.regs.get64 {r}).setWidth {n}"


def rset(r, n, v):
  if n == 64:
    return f"s.regs.set64 {r} {v}"
  if n == 32:
    return f"s.regs.set64 {r} (({v}).setWidth 64)"
  return f"s.regs.set64 {r} ((s.regs.get64 {r}).replaceLow {v})"


def syn_first(k, n):
  if k[0] == "reg":
    return f"(.reg (.low {k[1]} {WN[n]}))"
  return MEM


def syn_second(k, n):
  if k[0] == "reg":
    return f"(.regOrMem (.reg (.low {k[1]} {WN[n]})))"
  if k[0] == "mem":
    return f"(.regOrMem {MEM})"
  return "(.imm (.int64 i))"


def val(k, n):
  if k[0] == "reg":
    return rget(k[1], n)
  if k[0] == "mem":
    return f"BitVec.ofInt {n} m"
  return f"i.toBitVec.truncate {n}"


def write(k, n, v="v"):
  if k[0] == "reg":
    return "regs := " + rset(k[1], n, v)
  return f"dmem := Mem.storeInt s.dmem addr {BYTES[n]} {v}.toInt"


ATT = {"reg": "%r", "imm": "$i", "mem": "d(%rb,%idx)"}
SUF = {8: "b", 16: "w", 32: "l", 64: "q"}


def params(kinds):
  ps = []
  for k in kinds:
    if k[0] == "reg" and f"({k[1]} : Reg64)" not in ps:
      ps.append(f"({k[1]} : Reg64)")
  if any(k[0] == "mem" for k in kinds):
    ps.append(MEMPARAMS)
  if any(k[0] == "imm" for k in kinds):
    ps.append("(i : Int64)")
  return " ".join(ps)


def rule(name, doc, binders, lets, nondet, update, instr, mem, load, regasz=True,
         nbytes=None, proof=None, prio="low"):
  rules.append((f"MachineWP.{name}", doc))
  emit(f"/-- {doc} -/")
  asz_b = "(asz : Width) " if (regasz and not mem) else ""
  asz = "asz" if (regasz and not mem) else ".W64"
  emit(f"@[spec {prio}] theorem MachineWP.{name} {asz_b}{binders} :")
  emit("    ⦃ fun s =>")
  if mem:
    ind = " " * 12
    emit(f"        let addr := {ADDR}")
    emit(f"        ((Mem.loadInt s.dmem addr {nbytes}).isSome = true)")
    if load:
      emit(f"          ⊓ (∀ m, Mem.loadInt s.dmem addr {nbytes} = some m →")
    else:
      emit("          ⊓ (")
  else:
    ind = " " * 8
  for l in lets:
    emit(ind + l)
  q = "".join((f"∀ {x}, " if ":" in x else f"∀ {x} : Bool, ") for x in nondet)
  fields = (",\n" + ind + "      ").join(update)
  emit(f"{ind}{q}WP.wp p Q E")
  emit(f"{ind}  {{ s with")
  emit(f"{ind}      {fields} }}" + (") ⦄" if mem else " ⦄"))
  emit(f"      (Directive.instr (.regular {asz} {instr}) :: p)")
  emit("    ⦃ Q; E ⦄ :=")
  if proof:
    emit("  " + proof)
  elif mem:
    emit("  mem_rule")
  elif not nondet:
    emit("  reg_rule")
  elif len(nondet) == 1:
    emit("  reg_nondet_rule")
  else:
    emit("  nondet4_rule")
  emit("")


FORMS = {
    "reg_reg": (("reg", "rd"), ("reg", "rs")),
    "reg_imm": (("reg", "r"), ("imm",)),
    "load_mem": (("reg", "r"), ("mem",)),
    "store_mem": (("mem",), ("reg", "r")),
    "mem_imm": (("mem",), ("imm",)),
}
FORMS_NW = {
    "reg_reg": FORMS["reg_reg"],
    "reg_imm": FORMS["reg_imm"],
    "reg_mem": (("reg", "r"), ("mem",)),
    "mem_reg": (("mem",), ("reg", "r")),
    "mem_imm": (("mem",), ("imm",)),
}


def status_lines(kind, n):
  return {
      "add": ["{ cf := v.unsigned != a.unsigned + b.unsigned,",
              "  af := (v.take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,",
              "  of := v.signed != a.signed + b.signed }"],
      "sub": ["{ cf := v.unsigned != b.unsigned - a.unsigned,",
              "  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned,",
              "  of := v.signed != b.signed - a.signed }"],
      "sbb": ["{ cf := v.unsigned != b.unsigned - a.unsigned - (s.status.cf.toNat : Int),",
              "  af := (v.take 4).unsigned != (b.take 4).unsigned - (a.take 4).unsigned"
              " - (s.status.cf.toNat : Int),",
              "  of := v.signed != b.signed - a.signed - (s.status.cf.toNat : Int) }"],
      "cmp": ["{ cf := v.unsigned != a.unsigned - b.unsigned,",
              "  af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned,",
              "  of := v.signed != a.signed - b.signed }"],
      "logic": ["{ cf := false, of := false, af }"],
      "neg": ["{ cf := b != 0, af := (b.take 4) != 0, of := v.signed != - b.signed }"],
      "dec": ["{ cf := s.status.cf,",
              "  af := (v.take 4).unsigned != (a.take 4).unsigned - 1,",
              "  of := v.signed != a.signed - 1 }"],
  }[kind]


def status_field(kind, ind, n):
  body = ("\n" + ind + "          ").join(status_lines(kind, n))
  return "status := StatusFlags.from_result v\n" + ind + "          " + body


WHAT = {"add": "the sum and its flags", "sub": "the difference and its flags",
        "sbb": "the difference less the carry, and its flags",
        "cmp": "no write; the flags of the difference",
        "and": "the conjunction; `af` left arbitrary",
        "or": "the disjunction; `af` left arbitrary",
        "xor": "the exclusive or; `af` left arbitrary",
        "test": "no write; the flags of the conjunction, `af` left arbitrary"}


def gen_binop(op, kind, widths=(8, 16, 32, 64)):
  forms = FORMS_NW if kind in ("cmp", "test") else FORMS
  for fname, (x, y) in forms.items():
    mem = x[0] == "mem" or y[0] == "mem"
    for n in widths:
      ind = " " * (12 if mem else 8)
      nondet = []
      if kind in ("add", "sub", "sbb"):
        lets = [f"let a := {val(y, n)}", f"let b := {val(x, n)}"]
        lets.append({"add": "let v := a + b", "sub": "let v := b - a",
                     "sbb": f"let v := b - a - BitVec.ofNat {n} s.status.cf.toNat"}[kind])
        upd = [write(x, n), status_field(kind, ind, n)]
      elif kind == "cmp":
        lets = [f"let a := {val(x, n)}", f"let b := {val(y, n)}", "let v := a - b"]
        upd = [status_field("cmp", ind, n)]
      elif kind == "logic":
        sym = {"and": "&&&", "or": "|||", "xor": "^^^"}[op]
        lets = [f"let v := {val(x, n)} {sym} {val(y, n)}"]
        upd = [write(x, n), status_field("logic", ind, n)]
        nondet = ["af"]
      else:  # test
        lets = [f"let v := {val(x, n)} &&& {val(y, n)}"]
        upd = [status_field("logic", ind, n)]
        nondet = ["af"]
      name = f"{op}_{fname}_w{n}_spec"
      doc = f"`{op}{SUF[n]} {ATT[y[0]]}, {ATT[x[0]]}`: {WHAT[op if kind != 'logic' else op]}."
      instr = f"{WN[n]}\n          (.{op} {syn_first(x, n)} {syn_second(y, n)})"
      rule(name, doc, params((x, y)), lets, nondet, upd, instr, mem, mem,
           nbytes=BYTES[n])


def gen_unary(op, widths=(8, 16, 32, 64)):
  for x in (("reg", "r"), ("mem",)):
    mem = x[0] == "mem"
    for n in widths:
      ind = " " * (12 if mem else 8)
      if op == "neg":
        lets = [f"let b := {val(x, n)}", "let v := -b"]
        upd = [write(x, n), status_field("neg", ind, n)]
      elif op == "not":
        lets = [f"let v := ~~~{val(x, n)}"]
        upd = [write(x, n)]
      else:
        lets = [f"let a := {val(x, n)}", "let v := a - 1"]
        upd = [write(x, n), status_field("dec", ind, n)]
      name = f"{op}_{'mem' if mem else 'reg'}_w{n}_spec"
      doc = f"`{op}{SUF[n]} {ATT[x[0]]}`."
      instr = f"{WN[n]} (.{op} {syn_first(x, n)})"
      rule(name, doc, params((x,)), lets, [], upd, instr, mem, mem, nbytes=BYTES[n])


def gen_mov():
  for n in (8, 16):
    rule(f"mov_reg_reg_w{n}_spec", f"`mov{SUF[n]} %rs, %rd`: the low bits replaced.",
         "(rd rs : Reg64)", [], [], ["regs := " + rset("rd", n, f"({rget('rs', n)})")],
         f"{WN[n]}\n          (.mov (.reg (.low rd {WN[n]})) (.regOrMem (.reg (.low rs {WN[n]}))))",
         False, False)
  for n in (8, 16):
    rule(f"mov_reg_imm_w{n}_spec", f"`mov{SUF[n]} $i, %r`: the low bits replaced.",
         "(r : Reg64) (i : Int64)", [], [],
         ["regs := " + rset("r", n, f"(i.toBitVec.truncate {n})")],
         f"{WN[n]} (.mov (.reg (.low r {WN[n]})) (.imm (.int64 i)))", False, False)
  for n in (8, 16):
    rule(f"mov_load_mem_w{n}_spec", f"`mov{SUF[n]} d(%rb,%idx), %r`.",
         "(r : Reg64) " + MEMPARAMS, [], [], ["regs := " + rset("r", n, f"(BitVec.ofInt {n} m)")],
         f"{WN[n]}\n          (.mov (.reg (.low r {WN[n]})) (.regOrMem {MEM}))", True, True,
         nbytes=BYTES[n])
  for n in (8, 16, 64):
    rule(f"mov_store_mem_w{n}_spec", f"`mov{SUF[n]} %r, d(%rb,%idx)`.",
         MEMPARAMS + " (r : Reg64)", [], [],
         [f"dmem := Mem.storeInt s.dmem addr {BYTES[n]} ({rget('r', n)}).toInt"],
         f"{WN[n]}\n          (.mov {MEM} (.regOrMem (.reg (.low r {WN[n]}))))", True, False,
         nbytes=BYTES[n])
  for n in (8, 16, 32, 64):
    rule(f"mov_mem_imm_w{n}_spec", f"`mov{SUF[n]} $i, d(%rb,%idx)`: the immediate truncated.",
         MEMPARAMS + " (i : Int64)", [], [],
         [f"dmem := Mem.storeInt s.dmem addr {BYTES[n]} (i.toBitVec.truncate {n}).toInt"],
         f"{WN[n]}\n          (.mov {MEM} (.imm (.int64 i)))", True, False, nbytes=BYTES[n])


MOVX = [(32, 8), (32, 16), (64, 8), (64, 16), (16, 8)]


def gen_movx():
  for op, ext, desc in (("movzx", "zeroExtend", "zero"), ("movsx", "signExtend", "sign")):
    pairs = MOVX + ([(64, 32)] if op == "movsx" else [])
    for n, k in pairs:
      rule(f"{op}_reg_reg_w{n}_{k}_spec",
           f"`{op}` from `%rs` ({k} bits) into `%rd` ({n} bits), {desc}-extended.",
           "(rd rs : Reg64)", [], [],
           ["regs := " + rset("rd", n, f"(({rget('rs', k)}).{ext} {n})")],
           f"{WN[n]}\n          (.{op} (w' := {WN[k]}) (.reg (.low rd {WN[n]})) (.reg (.low rs {WN[k]})))",
           False, False)
      rule(f"{op}_load_mem_w{n}_{k}_spec",
           f"`{op}` from the {BYTES[k]} bytes at `d(%rb,%idx)` into `%rd` ({n} bits), {desc}-extended.",
           "(rd : Reg64) " + MEMPARAMS, [], [],
           ["regs := " + rset("rd", n, f"((BitVec.ofInt {k} m).{ext} {n})")],
           f"{WN[n]}\n          (.{op} (w' := {WN[k]}) (.reg (.low rd {WN[n]})) {MEM})", True, True,
           nbytes=BYTES[k])


def gen_cmov_setcc():
  for n in (16, 32, 64):
    rule(f"cmovcc_reg_reg_w{n}_spec",
         f"`cmovcc{SUF[n]} %rs, %rd`: the destination is written either way (a 32-bit\n"
         "destination is zero-extended even when the condition fails).",
         "(cc : CondCode) (rd rs : Reg64)", [], [],
         ["regs := " + rset("rd", n, f"(if cc.interp s.status then {rget('rs', n)} else {rget('rd', n)})")],
         f"{WN[n]}\n          (.cmovcc cc (.low rd {WN[n]}) (.reg (.low rs {WN[n]})))", False, False)
    rule(f"cmovcc_load_mem_w{n}_spec",
         f"`cmovcc{SUF[n]} d(%rb,%idx), %rd`: the bytes are read either way.",
         "(cc : CondCode) (rd : Reg64) " + MEMPARAMS, [], [],
         ["regs := " + rset("rd", n, f"(if cc.interp s.status then BitVec.ofInt {n} m else {rget('rd', n)})")],
         f"{WN[n]}\n          (.cmovcc cc (.low rd {WN[n]}) {MEM})", True, True, nbytes=BYTES[n])
  rule("setcc_reg_spec", "`setcc %r8`: the low byte gets the condition as 0 or 1.",
       "(cc : CondCode) (r : Reg64)", [], [],
       ["regs := " + rset("r", 8, "(BitVec.ofNat 8 (cc.interp s.status).toNat)")],
       ".W8 (.setcc cc (.reg (.low r .W8)))", False, False)
  rule("setcc_mem_spec", "`setcc d(%rb,%idx)`: the byte gets the condition as 0 or 1.",
       "(cc : CondCode) " + MEMPARAMS, [], [],
       ["dmem := Mem.storeInt s.dmem addr 1 (BitVec.ofNat 8 (cc.interp s.status).toNat).toInt"],
       f".W8 (.setcc cc {MEM})", True, False, nbytes=1)


def gen_imul():
  st = ("status :=\n"
        "                { cf := v.signed != a.signed * b.signed, pf := pf, af := af, zf := zf,\n"
        "                  sf := sf, of := v.signed != a.signed * b.signed }")
  for n in (16, 32, 64):
    rule(f"imul_reg_reg_imm_w{n}_spec",
         f"`imul{SUF[n]} $i, %rs, %rd`: the truncated product; `cf`/`of` say whether it\n"
         "overflowed, the other flags are left arbitrary.",
         "(rd rs : Reg64) (i : Int64)",
         [f"let a := {rget('rs', n)}", f"let b := i.toBitVec.truncate {n}", "let v := a * b"],
         ["sf", "zf", "af", "pf"], ["regs := " + rset("rd", n, "v"), st],
         f"{WN[n]}\n          (.imul (some (.reg (.low rd {WN[n]}))) (.reg (.low rs {WN[n]})) (.imm (.int64 i)))",
         False, False)
    rule(f"imul_reg_reg_w{n}_spec",
         f"`imul{SUF[n]} %rs, %rd`: the truncated product; `cf`/`of` say whether it\n"
         "overflowed, the other flags are left arbitrary.",
         "(rd rs : Reg64)",
         [f"let a := {rget('rd', n)}", f"let b := {rget('rs', n)}", "let v := a * b"],
         ["sf", "zf", "af", "pf"], ["regs := " + rset("rd", n, "v"), st],
         f"{WN[n]}\n          (.imul none (.reg (.low rd {WN[n]})) (.regOrMem (.reg (.low rs {WN[n]}))))",
         False, False)


def gen_lea():
  for n in (32, 64):
    rule(f"lea_mem_w{n}_spec",
         f"`lea{SUF[n]} d(%rb,%idx), %r`: the address"
         + (", truncated and zero-extended." if n == 32 else "."),
         "(r : Reg64) " + MEMPARAMS, [], [],
         ["regs := " + rset("r", n, f"((s.regs.get64 rb + AddrIndex.offset64 idx s.regs + d.toBitVec)"
                            + (".setWidth 32)" if n == 32 else ")"))],
         f"{WN[n]}\n          (.lea (.low r {WN[n]}) ⟨some (.reg rb), idx, .int64 d⟩)", False, False,
         regasz=False, proof="lea_rule")
    rule(f"lea_index_w{n}_spec",
         f"`lea{SUF[n]} d(,%i,c), %r` (no base, 64-bit address size): the index times the\n"
         "scale plus the displacement" + (", truncated and zero-extended." if n == 32 else "."),
         "(r i : Reg64) (c : Width) (d : Int64)", [], [],
         ["regs := " + rset("r", n, "((AddrIndex.offset64 (some ⟨i, c⟩) s.regs + d.toBitVec)"
                            + (".setWidth 32)" if n == 32 else ")"))],
         f"{WN[n]}\n          (.lea (.low r {WN[n]}) ⟨none, some ⟨i, c⟩, .int64 d⟩)", False, False,
         regasz=False, proof="lea_rule")


def gen_shift():
  ops = {"shl": "a <<< n", "shr": "a.ushiftRight n", "sar": "a.sshiftRight n"}
  for op, expr in ops.items():
    for cnt in ("imm", "cl"):
      for n in (8, 16, 32, 64):
        mod = 64 if n == 64 else 32
        src = "i.toBitVec.toNat" if cnt == "imm" else "(s.regs.get64 .rcx).toNat"
        syn = "(.imm8 (.int64 i))" if cnt == "imm" else ".cl"
        what = {"shl": "shifted left", "shr": "shifted right logically",
                "sar": "shifted right arithmetically"}[op]
        cdesc = "the immediate" if cnt == "imm" else "`%cl`"
        rule(f"{op}_reg_{cnt}_w{n}_spec",
             f"`{op}{SUF[n]} {'$i' if cnt == 'imm' else '%cl'}, %r`: {what} by {cdesc} mod {mod};"
             " `zf`, `sf`, `pf`\nfrom the result (`StatusFlags.from_result`), `cf`, `af`, `of` left"
             f" arbitrary. A count of\nzero mod {mod} changes nothing.",
             "(r : Reg64)" + (" (i : Int64)" if cnt == "imm" else ""),
             [f"let a := {rget('r', n)}", f"let n := {src} % 256 % {mod}"], ["cf af of : Bool"],
             ["regs := if n = 0 then s.regs else " + rset("r", n, f"({expr})"),
              f"status := if n = 0 then s.status\n                else StatusFlags.from_result ({expr}) {{ s.status with cf, af, of }}"],
             f"{WN[n]} (.{op} (.reg (.low r {WN[n]})) {syn})", False, False, proof="shift_rule")


def gen_shift_cl_opaque():
  """`op %cl, %r` with the flags forgotten and the register file behind an opaque
  `<op>Cl<n>`: after k shifts by `%cl` the precise rule's state mentions `s.regs`
  4^k times (both the `regs` and the `status` updates branch on the count). Scoped:
  `open scoped Kraken.Rules.IntMisc.ShiftClOpaque` makes these win over the precise
  `@[spec low]` rules, in code whose flags are dead after the shift."""
  ops = {"shl": "a <<< n", "shr": "a.ushiftRight n", "sar": "a.sshiftRight n"}
  names = []
  for op, expr in ops.items():
    for n in (8, 16, 32, 64):
      mod = 64 if n == 64 else 32
      fn = f"{op}Cl{n}"
      cnt = f"(regs.get64 .rcx).toNat % 256 % {mod}"
      a = rget("r", n).replace("s.regs", "regs")
      e = expr.replace("a", f"({a})", 1).replace(" n", f" ({cnt})")
      upd = rset("r", n, f"({e})").replace("s.regs", "regs")
      emit(f"/-- The register file after `{op}{SUF[n]} %cl, %r` (as `{op}_reg_cl_w{n}_spec`), behind a")
      emit("name: the state after a run of shifts by `%cl` stays linear in their number. -/")
      emit(f"def MachineWP.{fn} (r : Reg64) (regs : Reg64s) : Reg64s :=")
      emit(f"  if {cnt} = 0 then regs")
      emit(f"  else {upd}")
      emit("")
      a_n = rget("r", n).replace("s.regs", "regs")
      e_n = expr.replace("a", f"({a_n})", 1)
      upd_n = rset("r", n, f"({e_n})").replace("s.regs", "regs")
      emit("omit [CodeEnv] in")
      emit(f"/-- `{fn}` at a known nonzero count. -/")
      emit(f"theorem MachineWP.{fn}_of_rcx {{r : Reg64}} {{regs : Reg64s}} {{c : BitVec 64}} (n : Nat)")
      emit(f"    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % {mod} = n) (h0 : n ≠ 0) :")
      emit(f"    {fn} r regs = {upd_n} := by")
      emit(f"  simp only [{fn}, hc, hn, h0, ite_false]")
      emit("")
      emit("omit [CodeEnv] in")
      emit(f"/-- `{fn}` at a count of zero. -/")
      emit(f"theorem MachineWP.{fn}_of_rcx0 {{r : Reg64}} {{regs : Reg64s}} {{c : BitVec 64}}")
      emit(f"    (hc : regs.get64 .rcx = c) (hn : c.toNat % 256 % {mod} = 0) :")
      emit(f"    {fn} r regs = regs := by")
      emit(f"  simp only [{fn}, hc, hn, ite_true]")
      emit("")
      a_s = rget("r", n)
      e_s = expr.replace("a", f"({a_s})", 1).replace(" n", f" ((s.regs.get64 .rcx).toNat % 256 % {mod})")
      name = f"{op}_reg_cl_w{n}_spec'"
      names.append(f"MachineWP.{name}")
      rules.append((f"MachineWP.{name}", f"`{op}{SUF[n]} %cl, %r`, flags forgotten, `{fn}`"))
      emit(f"/-- `{op}{SUF[n]} %cl, %r` with the flags forgotten (any status) and the register file")
      emit(f"behind `{fn}`. Not a `spec` rule unless `Kraken.Rules.IntMisc.ShiftClOpaque` is open. -/")
      emit(f"theorem MachineWP.{name} (asz : Width) (r : Reg64) :")
      emit(f"    ⦃ fun s => ∀ st : StatusFlags, WP.wp p Q E {{ s with regs := {fn} r s.regs, status := st }} ⦄")
      emit(f"      (Directive.instr (.regular asz {WN[n]} (.{op} (.reg (.low r {WN[n]})) .cl)) :: p)")
      emit("    ⦃ Q; E ⦄ :=")
      emit(f"  Triple.intro fun s hs => (MachineWP.{op}_reg_cl_w{n}_spec (p := p) (Q := Q) (E := E) asz r).le_wp s")
      emit("    (fun cf af of => by")
      emit(f"      have h := hs (if (s.regs.get64 .rcx).toNat % 256 % {mod} = 0 then s.status")
      emit(f"        else StatusFlags.from_result ({e_s}) {{ s.status with cf, af, of }})")
      emit(f"      simp only [{fn}] at h")
      emit("      split <;> simp_all)")
      emit("")
  emit("-- `open scoped Kraken.Rules.IntMisc.ShiftClOpaque`: the flags-forgetting shifts by `%cl`.")
  emit("namespace Kraken.Rules.IntMisc.ShiftClOpaque")
  emit("attribute [scoped spec] " + "\n  ".join(names))
  emit("end Kraken.Rules.IntMisc.ShiftClOpaque")
  emit("")


def main():
  gen_binop("add", "add")
  gen_binop("sub", "sub")
  gen_binop("sbb", "sbb")
  gen_binop("cmp", "cmp")
  for op in ("and", "or", "xor"):
    gen_binop(op, "logic")
  gen_binop("test", "test")
  for op in ("neg", "not", "dec"):
    gen_unary(op)
  gen_mov()
  gen_movx()
  gen_cmov_setcc()
  gen_imul()
  gen_lea()
  gen_shift()
  gen_shift_cl_opaque()
  txt = "\n".join(out)
  open(sys.argv[1], "w").write(txt)
  open(sys.argv[2], "w").write("\n".join(f"{n}: {d.splitlines()[0]}" for n, d in rules) + "\n")


main()
