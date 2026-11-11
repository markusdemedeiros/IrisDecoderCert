#!/usr/bin/env python3
"""Assemble the exported Kraken texts as an OPEN relocatable x86-64 library.

This is a reproducible assembly of the verified instruction texts, not the
unavailable upstream FFmpeg PIE and not a closed executable. Undefined symbols
and relocations are retained and reported, never filled with fake implementations.
Every instruction has boundary symbols, allowing consumers to recover its actual
encoding and size without relying on disassembler line wrapping.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent
os.environ.setdefault("SBR_OBJ_DIR", "/nonexistent")
sys.path.insert(0, str(REPO / "scripts/sbr/tv"))
from tv import Elf, to_mc  # Original cosmetic printer-to-assembler conversion.


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(tool, *args):
    toolroot = ROOT / "toolchain/unpacked/usr"
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = str(toolroot / "lib/aarch64-linux-gnu")
    result = subprocess.run(
        [str(toolroot / "bin" / ("x86_64-linux-gnu-" + tool)), *map(str, args)],
        env=env, text=True, capture_output=True,
    )
    if result.returncode:
        raise RuntimeError(f"{tool} failed: {result.stderr}")
    return result.stdout


def build():
    out = ROOT / "open-library"
    out.mkdir(exist_ok=True)
    files = sorted((ROOT / "texts").glob("*.txt"))
    if len(files) != 39:
        raise ValueError(f"Expected 39 exported programs, found {len(files)}")
    asm = [".intel_syntax noprefix", ".code64"]
    programs = []
    for i, path in enumerate(files):
        entry = path.read_text().splitlines()[0].removesuffix(":")
        section = ".text." + path.stem
        asm += [f'.section {section},"ax",@progbits', f".globl {entry}",
                f".type {entry},@function"]
        cells = []
        insns = 0
        for line in path.read_text().splitlines():
            if not line:
                continue
            if not line.startswith(" "):
                if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9.]*:", line):
                    raise ValueError(f"Unexpected label: {line}")
                asm.append(line)
                cells.append({"label": line[:-1]})
            else:
                text, sep, meta = line.strip().partition(" ;; ")
                if not sep:
                    raise ValueError(f"Unexpected non-instruction: {line}")
                marker = f"__sbr_cell_{i}_{insns}"
                asm += [marker + ":", "    " + to_mc(text), marker + "_end:"]
                cells.append({"instruction": text, "widths": meta, "marker": marker})
                insns += 1
        asm.append(f".size {entry}, .-{entry}")
        programs.append({"name": path.stem, "entry": entry, "section": section, "source_sha256": digest(path),
                         "instructions": insns, "cells": cells})
    asm.append('.section .note.GNU-stack,"",@progbits')
    source = out / "sbr.S"
    obj = out / "sbr.o"
    source.write_text("\n".join(asm) + "\n")
    run("as", "--64", "-o", obj, source)
    elf = Elf(str(obj))
    symbols = {s["name"]: s for s in elf.syms}
    sections = {s["name"]: s for s in elf.secs}
    for program in programs:
        sec = sections[program["section"]]
        program["bytes"] = sec["size"]
        program["text_sha256"] = hashlib.sha256(
            elf.data[sec["off"]:sec["off"] + sec["size"]]).hexdigest()
        previous = 0
        for cell in program["cells"]:
            if "label" in cell:
                cell["offset"] = symbols[cell["label"]]["value"]
                cell["size"] = 0
            else:
                begin = symbols[cell["marker"]]
                end = symbols[cell["marker"] + "_end"]
                assert begin["shndx"] == end["shndx"] == sec["idx"]
                cell["offset"] = begin["value"]
                cell["size"] = end["value"] - begin["value"]
                assert 1 <= cell["size"] <= 15, cell
                pos = sec["off"] + cell["offset"]
                cell["encoding_before_relocation"] = elf.data[pos:pos + cell["size"]].hex()
            assert cell["offset"] == previous, cell
            previous += cell["size"]
        assert previous == sec["size"]
    undefined = sorted(s["name"] for s in elf.syms if s["shndx"] == 0 and s["name"])
    relocations = run("readelf", "--wide", "--relocs", obj)
    (out / "relocations.txt").write_text(relocations)
    report = {
        "artifact": "open relocatable library assembled from exported Kraken instruction texts",
        "upstream_commit": "b60a6f97373dbb537d0576fd40b8b7c2520b4de3",
        "object_sha256": digest(obj), "assembly_sha256": digest(source),
        "assembler": run("as", "--version").splitlines()[0],
        "program_count": len(programs),
        "instruction_count": sum(p["instructions"] for p in programs),
        "text_bytes": sum(p["bytes"] for p in programs),
        "undefined_symbols": undefined,
        "scope": [
            "The original pinned FFmpeg PIE is not available or reproduced by this script.",
            "This object retains unresolved code and data references; it is not runnable.",
            "The original SessPlaced and external callback contracts remain proof obligations.",
            "The source exports must be regenerated from Lean for provenance checking.",
            "Assembler correctness and print/assembly correspondence are outside the Lean kernel.",
        ],
        "programs": programs,
    }
    (out / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in
                      ("program_count", "instruction_count", "text_bytes", "object_sha256")}))
    print(f"Retained {len(undefined)} undefined symbols; details in {out / 'manifest.json'}")


if __name__ == "__main__":
    build()
