#!/usr/bin/env python3
"""Extract unchanged public config/apply wrappers, avoiding unused parser imports.

The semantic proof artifacts remain the original SessionBin.SConfig/SApply
modules and their linked machine-code theorem dependencies. Only source
slices from TopDefs/TopCalls are repeated in a new namespace.
"""
from pathlib import Path
import argparse
import subprocess

root = Path(__file__).resolve().parents[1]
pin = "b60a6f97373dbb537d0576fd40b8b7c2520b4de3"
base = "Kraken/X64/Examples/Sbr/SessionBin/"
def original(name):
    return subprocess.check_output(["git", "show", f"{pin}:{base}{name}.lean"], cwd=root, text=True)

d = original("TopDefs")
c = original("TopCalls")
slices = [
    d[d.index("theorem tAt_arg0"):d.index("end Kraken.Examples.Sbr.SessionBin")],
    c[c.index("theorem sep_mono3"):c.index("omit [CodeEnv] in\ntheorem dec_mem")],
    c[c.index("omit [CodeEnv] in\ntheorem cfg_mem"):c.index("/-! ## The four calls")],
    c[c.index("theorem config_top"):c.index("end Kraken.Examples.Sbr.SessionBin")],
]
header = f'''import Kraken.X64.Examples.Sbr.SessionBin.SApply
import Kraken.X64.Examples.Sbr.SessionBin.SConfig

/-! Exact source excerpts from zrlk/kraken commit {pin}:
TopDefs.lean (element splitting) and TopCalls.lean (separation helpers and
config/apply wrappers). Generated/checked by scripts/extract-public-calls.py.
The original instruction and session proofs are imported unchanged. Unused
parser imports and wrappers are omitted; no theorem body is adapted. -/
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.ParseModel hiding Live
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse
open Kraken.Examples.Sbr.SessionBin
namespace SbrClient.Upstream
section
'''
expected = header + slices[0] + "end\nsection\n" + "\n".join(slices[1:]) + "end\nend SbrClient.Upstream\n"
target = root / "SbrClient/FFmpeg/UpstreamCalls.lean"
parser = argparse.ArgumentParser()
parser.add_argument("--write", action="store_true")
args = parser.parse_args()
if args.write:
    target.write_text(expected)
elif target.read_text() != expected:
    raise SystemExit("UpstreamCalls.lean differs from pinned source excerpts")
print(f"Verified four exact source slices against {pin}; {len(expected.splitlines())} lines")
