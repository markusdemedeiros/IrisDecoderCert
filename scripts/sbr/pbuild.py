#!/usr/bin/env python3
"""Memory-aware parallel module build for ci.sh (used when SBR_JOBS > 1).

usage: pbuild.py OUT PREFIX MODULE...   (run from the repository root)

Builds every MODULE (`lake build PREFIX.MODULE`, each under its own SBR_CAP_CMD) as soon as
the MODULEs it imports have been built, with at most SBR_JOBS builds at a time and the sum of
the recorded peaks of the running builds (baseline/build_peaks.txt) at most
SBR_MEM_BUDGET_GB. Lake has no build lock, so two lake processes must never build the same
module: a prelude `lake build` first builds every non-MODULE import (the Kraken library), after
which each `lake build PREFIX.M` only elaborates M itself. Each module still gets its own log
OUT/build_M.txt, its own /usr/bin/time record and its own error/sorry scan; OUT/build.txt has
the same per-module lines as the sequential build (in MODULE order). Exit 1 if any build
failed, had an error line or a `sorry` warning.

Env: SBR_JOBS (max concurrent builds), SBR_MEM_BUDGET_GB (default 24), SBR_MEM_RESERVE_GB
(default 2: do not start a build while another runs unless MemAvailable, minus the peak
headroom still owed to running builds, covers its peak plus this reserve), SBR_PEAK_DEFAULT_GB
(default 4: peak assumed for modules missing from build_peaks.txt), SBR_CAP_CMD.
"""
import os, re, shlex, subprocess, sys, time

OUT, P, MODS = sys.argv[1], sys.argv[2], sys.argv[3:]
JOBS = max(1, int(os.environ.get("SBR_JOBS", "1")))
BUDGET = float(os.environ.get("SBR_MEM_BUDGET_GB", "24"))
RESERVE = float(os.environ.get("SBR_MEM_RESERVE_GB", "2"))
DEFPEAK = float(os.environ.get("SBR_PEAK_DEFAULT_GB", "4"))
CAP = shlex.split(os.environ.get("SBR_CAP_CMD", ""))
HERE = os.path.dirname(os.path.abspath(__file__))
TIMER = os.path.exists("/usr/bin/time")
T0 = time.time()

def log(msg):
    line = "[%6.0fs] %s" % (time.time() - T0, msg)
    print(line, flush=True)
    with open(os.path.join(OUT, "build_sched.txt"), "a") as f:
        f.write(line + "\n")

# ---- recorded peaks / times: "MODULE GB SECONDS"
PEAK, SECS = {}, {}
pf = os.path.join(HERE, "baseline", "build_peaks.txt")
if os.path.exists(pf):
    for l in open(pf):
        w = l.split("#")[0].split()
        if len(w) >= 3:
            PEAK[w[0]], SECS[w[0]] = float(w[1]), float(w[2])

# ---- import graph (direct `import` lines of each module's source)
def imports(mod):
    path = mod.replace(".", "/") + ".lean"
    r = []
    for l in open(path, encoding="utf-8"):
        m = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", l)
        if m:
            r.append(m.group(1))
    return r

mset = set(MODS)
DEPS, EXT = {}, []
for m in MODS:
    DEPS[m] = []
    for i in imports(P + "." + m):
        if i.startswith(P + ".") and i[len(P) + 1:] in mset:
            DEPS[m].append(i[len(P) + 1:])
        elif os.path.exists(i.replace(".", "/") + ".lean") and i not in EXT:
            EXT.append(i)  # a repository module outside MODS: built by the prelude

# priority: longest remaining path of recorded build seconds (critical path first)
USERS = {m: [u for u in MODS if m in DEPS[u]] for m in MODS}
BL = {}
for m in reversed(MODS):  # MODS is in dependency order
    BL[m] = SECS.get(m, 30.0) + max([BL[u] for u in USERS[m]], default=0.0)

def mem_available_gb():
    for l in open("/proc/meminfo"):
        if l.startswith("MemAvailable:"):
            return int(l.split()[1]) / 2**20
    return 0.0

def tree_rss_gb(pid):
    """Resident memory of pid and all its descendants."""
    kids, rss = {}, {}
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/stat" % d) as f:
                s = f.read()
            w = s[s.rindex(")") + 2:].split()
            kids.setdefault(int(w[1]), []).append(int(d))
            rss[int(d)] = int(w[21]) * os.sysconf("SC_PAGE_SIZE")
        except (OSError, ValueError):
            pass
    tot, st = 0, [pid]
    while st:
        p = st.pop()
        tot += rss.get(p, 0)
        st.extend(kids.get(p, []))
    return tot / 2**30

def start(m, target, logname):
    L = os.path.join(OUT, logname)
    cmd = (["/usr/bin/time", "-f", "%e s %M KB", "-o", L + ".time"] if TIMER else []) + CAP + ["lake", "build"] + target
    f = open(L, "w")
    return subprocess.Popen(cmd, stdout=f, stderr=subprocess.STDOUT), L

def scan(L, rc):
    txt = open(L, encoding="utf-8", errors="replace").read().splitlines()
    e = sum(1 for l in txt if l.startswith("error"))
    s = sum(1 for l in txt if re.search(r"declaration uses .sorry.", l))  # 'sorry' or `sorry`
    t = ""
    if os.path.exists(L + ".time"):
        tl = open(L + ".time").read().splitlines()
        t = tl[-1] if tl else ""
    return e, s, t

open(os.path.join(OUT, "build_sched.txt"), "w").close()
log("pbuild: %d modules, jobs=%d, budget=%.0f GB, reserve=%.0f GB, prelude=%d library modules"
    % (len(MODS), JOBS, BUDGET, RESERVE, len(EXT)))
LINES, bfail = {}, 0

# ---- prelude: the library modules imported by MODS (lake builds these with its own parallelism)
if EXT:
    p, L = start(None, EXT, "build_prelude.txt")
    rc = p.wait()
    e, s, t = scan(L, rc)
    LINES["(prelude)"] = "(prelude) rc=%d %s errors=%d sorry=%d" % (rc, t, e, s)
    log(LINES["(prelude)"])
    if rc or e or s:
        bfail = 1

state = {m: "wait" for m in MODS}  # wait | run | ok | fail | skip
if bfail:
    for m in MODS:
        state[m] = "skip"
running = {}  # m -> (Popen, log, t_start)
while any(v in ("wait", "run") for v in state.values()):
    # reap finished builds
    for m, (p, L, ts) in list(running.items()):
        rc = p.poll()
        if rc is None:
            continue
        del running[m]
        e, s, t = scan(L, rc)
        bad = rc != 0 or e != 0 or s != 0
        state[m] = "fail" if bad else "ok"
        bfail |= bad
        LINES[m] = "%s rc=%d %s errors=%d sorry=%d" % (m, rc, t, e, s)
        log("done  %-22s %s  (start +%.0fs)" % (m, LINES[m][len(m) + 1:], ts - T0))
    # modules whose dependency failed are not built (lake would rebuild the failed one)
    for m in MODS:
        if state[m] == "wait" and any(state[d] in ("fail", "skip") for d in DEPS[m]):
            state[m] = "skip"; bfail = 1
            LINES[m] = "%s rc=- skipped (dependency failed) errors=0 sorry=0" % m
            log("skip  " + m)
    ready = sorted((m for m in MODS if state[m] == "wait" and all(state[d] == "ok" for d in DEPS[m])),
                   key=lambda m: -BL[m])
    used = sum(PEAK.get(m, DEFPEAK) for m in running)
    owed = 0.0
    if running and ready:
        owed = sum(max(0.0, PEAK.get(m, DEFPEAK) - tree_rss_gb(p.pid)) for m, (p, _, _) in running.items())
    avail = mem_available_gb() - owed
    for m in ready:
        if len(running) >= JOBS:
            break
        need = PEAK.get(m, DEFPEAK)
        if running and (used + need > BUDGET or avail < need + RESERVE):
            continue  # a smaller ready module may still fit
        p, L = start(m, [P + "." + m], "build_%s.txt" % m)
        running[m] = (p, L, time.time())
        state[m] = "run"
        used += need; avail -= need
        log("start %-22s est %.1f GB, running %d (%.1f GB est), avail %.1f GB"
            % (m, need, len(running), used, avail + need))
    time.sleep(1)

with open(os.path.join(OUT, "build.txt"), "w") as f:
    for m in (["(prelude)"] if "(prelude)" in LINES else []) + MODS:
        f.write(LINES.get(m, "%s rc=- not built" % m) + "\n")
log("pbuild: wall %.0f s, %s" % (time.time() - T0, "FAIL" if bfail else "ok"))
sys.exit(1 if bfail else 0)
