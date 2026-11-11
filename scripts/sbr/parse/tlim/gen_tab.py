#!/usr/bin/env python3
"""`TlimVar.lean` and `TlimTab.lean` from the `table` and `var` definitions of `TlimBase.lean`.

For each label: `var_<short> (s) : var "<label>" s = <rhs> := rfl` and
`tab_<short> (k x ra t₀ s) : table k x ra t₀ "<label>" s ↔ <entry> := Iff.rfl`, where
`<short>` is `entry` for the routine's entry, otherwise the label suffix. The helpers of the
table's `where` clause are written `table.<Name>`.

Usage: gen_tab.py BASE.lean LABELS.txt OUTDIR   (writes OUTDIR/TlimVar.lean, OUTDIR/TlimTab.lean)
"""
import re
import sys

P = "sbr_make_f_tablelim"


def short(lab):
    return "entry" if lab == P else lab.split(".", 1)[1]


def clauses(text, head, stop):
    """The match arms `| "label", s => body` of the definition starting at `head`."""
    i = text.index(head)
    j = text.index(stop, i)
    body = text[i:j]
    arms = {}
    pat = re.compile(r'^  \| "([^"]+)", (\w+) =>(.*)$')
    cur = None
    for line in body.split("\n"):
        m = pat.match(line)
        if m:
            cur = m.group(1)
            arms[cur] = (m.group(2), [m.group(3).strip()])
        elif cur is not None and line.startswith("      "):
            arms[cur][1].append(line.strip())
        elif line.startswith("  | _"):
            cur = None
    return arms


def main():
    base, labels, out = sys.argv[1], sys.argv[2], sys.argv[3]
    text = open(base).read()
    labs = [l.strip() for l in open(labels) if l.strip()]
    helpers = re.findall(r"^  (\w+) \(k : Nat\)|^  (\w+) \(x : TArgs\)", text, re.M)
    helpers = {a or b for a, b in helpers}
    tab = clauses(text, "def table (k : Nat)", "\nwhere")
    var = clauses(text, "noncomputable def var", "  | _, _ => 2 ^ 50")
    v = ["import Kraken.X64.Examples.Sbr.Parse.TlimBase", "", "/-!",
         "# `sbr_make_f_tablelim`: the variant at each label", "",
         "`var` at a literal label, proved once by `rfl` (unfolding `var` with `simp` inside a block is",
         "expensive: the match has one string pattern per label).", "-/", "",
         "open Kraken Kraken.SysV Mem", "", "namespace Kraken.Examples.Sbr.Tlim", ""]
    for lab in labs:
        if lab in var:
            sv, body = var[lab]
            rhs = " ".join(body).replace(f"{sv} ", "s ") if sv != "_" else " ".join(body)
            rhs = re.sub(r"\b" + re.escape(sv) + r"\b", "s", rhs) if sv != "_" else rhs
        else:
            rhs = "2 ^ 50"
        v += [f'theorem var_{short(lab)} (s : MachineData) : var "{lab}" s = {rhs} := rfl', ""]
    v += ["end Kraken.Examples.Sbr.Tlim", ""]
    t = ["import Kraken.X64.Examples.Sbr.Parse.TlimBase", "", "/-!",
         "# `sbr_make_f_tablelim`: the table entry at each label", "",
         "`table` at a literal label, as an `Iff.rfl` lemma (unfolding the string match inside a block is",
         "expensive).", "-/", "",
         "open Kraken Kraken.SysV Mem Kraken.X64.Parser",
         "open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel",
         "open Kraken.Examples.Sbr.Parse.Qsort", "", "namespace Kraken.Examples.Sbr.Tlim", "",
         "variable [CodeEnv]", ""]
    for lab in labs:
        if lab not in tab:
            continue
        _, body = tab[lab]
        lines = [re.sub(r"\b(" + "|".join(sorted(helpers)) + r") k x ra", r"table.\1 k x ra", b)
                 for b in body] if helpers else body
        lines = [re.sub(r"(?<![\w.])(Med0|Med3|Med) x t₀", r"table.\1 x t₀", b) for b in lines]
        t += [f"theorem tab_{short(lab)} (k : Nat) (x : TArgs) (ra : Int64) (t₀ s : MachineData) :",
              f'    table k x ra t₀ "{lab}" s ↔',
              "    " + lines[0] + ("" if len(lines) > 1 else " := Iff.rfl")]
        for b in lines[1:-1]:
            t.append("        " + b)
        if len(lines) > 1:
            t.append("        " + lines[-1] + " := Iff.rfl")
        t.append("")
    t += ["end Kraken.Examples.Sbr.Tlim", ""]
    open(f"{out}/TlimVar.lean", "w").write("\n".join(v))
    open(f"{out}/TlimTab.lean", "w").write("\n".join(t))


if __name__ == "__main__":
    main()
