#!/usr/bin/env python3
"""Count physical Lean source lines in the reused modules' import closures.

Comments, blank lines, instruction texts and tables count as source lines.
Each file is counted once per closure. These are module-level source counts,
not C LOC, executed instruction counts, or declaration-level proof dependencies.
Lean/Iris dependencies outside this repository are excluded.
"""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "reuse-metrics.json"
README = ROOT / "README.md"
START = "<!-- reuse-metrics:start -->"
END = "<!-- reuse-metrics:end -->"
EXCERPTS = Path("SbrClient/FFmpeg/UpstreamCalls.lean")
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", re.M)


def closure(module):
    seen, paths = set(), set()

    def visit(name):
        if name in seen:
            return
        seen.add(name)
        path = Path(name.replace(".", "/") + ".lean")
        if not (ROOT / path).is_file():
            return
        paths.add(path)
        for dependency in IMPORT.findall((ROOT / path).read_text()):
            visit(dependency)

    visit(module)
    return sorted(paths)


def measure(paths):
    return {"modules": len(paths),
            "lines": sum(len((ROOT / p).read_text().splitlines()) for p in paths)}


def upstream(module):
    paths = closure(module)
    ffmpeg = [p for p in paths if p.as_posix().startswith("Kraken/X64/Examples/Sbr/")]
    kraken = [p for p in paths if p.parts[0] in ("Kraken", "KrakenTactics") and p not in ffmpeg]
    return {"root_module": module, "ffmpeg_verification": measure(ffmpeg),
            "kraken_framework": measure(kraken), "total_upstream": measure(ffmpeg + kraken)}


def report():
    main = "SbrClient.Client.VerifiedReadyService"
    local = [p for p in closure(main) if p.parts[0] == "SbrClient" and p != EXCERPTS]
    groups = {
        "generic_logic_machine_host": [p for p in local if p.parts[1] in ("Logic", "Machine", "Host")],
        "ffmpeg_adapter": [p for p in local if p.parts[1] == "FFmpeg"],
        "iris_application": [p for p in local if p.parts[1] == "Client"],
    }
    return {
        "counting_rule": "Physical Lean source lines including comments, blank lines, instruction texts and tables; unique files per transitive local import closure. Not C LOC or exact proof-term dependencies. External Lean/Iris packages excluded.",
        "ffmpeg_classification": "Kraken/X64/Examples/Sbr/**.lean; all other Kraken/KrakenTactics dependencies are framework.",
        "linked_native_theorem": upstream("Kraken.X64.Examples.Sbr.Link"),
        "session_apply_theorem": upstream("Kraken.X64.Examples.Sbr.SessionBin.SApply"),
        "public_provider": upstream("SbrClient.FFmpeg.UpstreamCalls"),
        "main_example": {"root_module": main, "new_glue_and_client": measure(local),
                         "breakdown": {name: measure(paths) for name, paths in groups.items()},
                         "copied_upstream_excerpts_excluded": measure([EXCERPTS])},
        "whole_sbrclient_tree": measure(sorted(p.relative_to(ROOT) for p in (ROOT / "SbrClient").rglob("*.lean"))),
    }


def markdown(result):
    lines = [START, "The following table separates FFmpeg verification code from Kraken framework code for each reused module closure:", "",
             "| Reused module closure | FFmpeg-specific Lean LOC | Kraken framework LOC | Total LOC |",
             "| --- | ---: | ---: | ---: |"]
    for key, label in [("linked_native_theorem", "Native theorem: `ff_aac_sbr_apply_linked`"),
                       ("session_apply_theorem", "Session theorem: `session_apply`"),
                       ("public_provider", "Imported provider: apply and configuration wrappers")]:
        row = result[key]
        lines.append(f"| {label} | {row['ffmpeg_verification']['lines']:,} | "
                     f"{row['kraken_framework']['lines']:,} | {row['total_upstream']['lines']:,} |")
    lines += ["", "The following table counts the new glue and client code in the main theorem's import closure:", "",
              "| New code needed by `VerifiedReadyService` | Modules | Lean LOC |",
              "| --- | ---: | ---: |"]
    for key, label in [("generic_logic_machine_host", "Certificate logic, machine bridge, and host semantics"),
                       ("ffmpeg_adapter", "FFmpeg-specific resources and call adapter"),
                       ("iris_application", "Iris application and public theorem")]:
        row = result['main_example']['breakdown'][key]
        lines.append(f"| {label} | {row['modules']} | {row['lines']:,} |")
    total = result['main_example']['new_glue_and_client']
    copied = result['main_example']['copied_upstream_excerpts_excluded']
    lines += [f"| Total new glue and client | {total['modules']} | {total['lines']:,} |", "",
              f"The total excludes {copied['lines']:,} lines of copied upstream wrapper excerpts. "
              "The optional startup variant and axiom-audit modules are also outside the main theorem's import closure.", END]
    return "\n".join(lines)


parser = argparse.ArgumentParser(description=__doc__)
mode = parser.add_mutually_exclusive_group()
mode.add_argument("--write", action="store_true", help="refresh reuse-metrics.json")
mode.add_argument("--check", action="store_true", help="require the saved report to match current sources")
args = parser.parse_args()
result = report()
readme = README.read_text()
before, found, rest = readme.partition(START)
if not found or END not in rest:
    sys.exit("README is missing the reuse-metrics markers")
saved, _, after = rest.partition(END)
expected = markdown(result)
if args.write:
    REPORT.write_text(json.dumps(result, indent=2) + "\n")
    README.write_text(before + expected + after)
elif args.check:
    if (not REPORT.is_file() or json.loads(REPORT.read_text()) != result
            or START + saved + END != expected):
        sys.exit("Reuse metrics are stale; run python3 scripts/reuse-metrics.py --write")
    print("Reuse metrics match the current source closures.")
if not args.check:
    print(json.dumps(result, indent=2))
