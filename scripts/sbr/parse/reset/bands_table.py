#!/usr/bin/env python3
"""Evidence for `BandsOK` (ResetSpec.lean) with the host's libm `powf`/`log2f`.

Evaluates, for every input `BandsOK` quantifies over (a supported rate, bs_start_freq < 16, so
k0 = start_min + sbr_offset[row][start]; k2 in [k0, 64] with k2 - k0 <= max_qmf_subbands;
bs_freq_scale in {1, 2, 3}, bs_alter_scale in {0, 1}), the band counts and the `make_bands`
borders exactly as `BandsOK` states them (float32 division, multiplication, int->float
conversion, round-to-nearest-even `lrintf`), and prints a table of the counts and the border
range, and whether each clause holds. Exit status 1 if a clause fails.

Usage: bands_table.py [--all] [--md]   (--all: one line per input; --md: a table per rate)
"""
import ctypes
import struct
import sys

libm = ctypes.CDLL("libm.so.6")
libm.powf.restype = ctypes.c_float
libm.powf.argtypes = [ctypes.c_float, ctypes.c_float]
libm.log2f.restype = ctypes.c_float
libm.log2f.argtypes = [ctypes.c_float]


def f32(x):
  return struct.unpack("f", struct.pack("f", x))[0]


def div(a, b):
  return f32(a / b)  # double division of two floats, rounded once: the correctly rounded f32 quotient


def mul(a, b):
  return f32(a * b)  # exact in double, rounded once


def lrint(x):
  return round(x)  # Python rounds half to even


RATES = [16000, 22050, 24000, 32000, 44100, 48000, 64000, 88200, 96000, 128000, 176400, 192000]
SBR_OFFSET = [[-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7],
              [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13],
              [-5, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16],
              [-6, -4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16],
              [-4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16, 20],
              [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16, 20, 24]]


def rate_row(sr):
  return {16000: 0, 22050: 1, 24000: 2, 32000: 3, 44100: 4, 48000: 4, 64000: 4}.get(sr, 5)


def max_q(sr):
  return 48 if sr <= 32000 else 35 if sr == 44100 else 32


INVWARP = struct.unpack("f", struct.pack("I", 0x3f44ec4f))[0]


def nb_of(start, stop, h):
  return 2 * lrint(mul(f32(libm.log2f(div(float(stop), float(start)))), h))


def bands_at(start, stop, nb):
  """The `lrintf(prod)` values for j in [1, nb)."""
  b = f32(libm.powf(div(float(stop), float(start)), div(1.0, float(nb))))
  p = float(start)
  out = []
  for _ in range(1, nb):
    p = mul(b, p)
    out.append(lrint(p))
  return out


def main():
  show_all = "--all" in sys.argv
  bad = 0
  rows = 0
  nb0_rng = [99, -99]
  nb1_rng = [99, -99]
  v_rng = [99, -99]
  seen = set()
  summ = {}
  for sr in RATES:
   row = rate_row(sr)
   temp = 3000 if sr < 32000 else 4000 if sr < 64000 else 5000
   for start in range(16):
    k0 = (temp * 128 + sr // 2) // sr + SBR_OFFSET[row][start]
    for k2 in range(k0, 65):
      if k2 - k0 > max_q(sr):
        continue
      for fs in (1, 2, 3):
        for alter in (0, 1):
          rows += 1
          h0 = float(7 - fs)
          two = 110 * k0 < 49 * k2
          k1 = 2 * k0 if two else k2
          nb0 = nb_of(k0, k1, h0)
          ok = True
          vs = []
          if nb0 > 0:
            nb0_rng[0] = min(nb0_rng[0], nb0); nb0_rng[1] = max(nb0_rng[1], nb0)
            ok &= nb0 <= 48
            if ok:
              vs += bands_at(k0, k1, nb0)
          nb1 = None
          if two:
            h1 = mul(h0, 1.0 if alter == 0 else INVWARP)
            nb1 = nb_of(k1, k2, h1)
            nb1_rng[0] = min(nb1_rng[0], nb1); nb1_rng[1] = max(nb1_rng[1], nb1)
            ok &= 2 <= nb1 <= 48
            if ok:
              vs += bands_at(k1, k2, nb1)
          if vs:
            v_rng[0] = min(v_rng[0], min(vs)); v_rng[1] = max(v_rng[1], max(vs))
          ok &= all(0 <= v <= 64 for v in vs)
          if not ok:
            bad += 1
          r = summ.setdefault(sr, {"n": 0, "k0": set(), "k2": set(), "nb0": set(), "nb1": set(),
                                   "v": set(), "bad": 0})
          r["n"] += 1; r["k0"].add(k0); r["k2"].add(k2); r["bad"] += not ok
          if nb0 > 0: r["nb0"].add(nb0)
          if nb1 is not None: r["nb1"].add(nb1)
          r["v"].update(vs)
          if show_all or not ok:
            print(f"k0={k0:2} k2={k2:2} fs={fs} alter={alter} nb0={nb0:3} nb1={nb1} "
                  f"borders=[{min(vs) if vs else '-'},{max(vs) if vs else '-'}] {'ok' if ok else 'FAIL'}")
  if "--md" in sys.argv:
    rng = lambda xs: f"[{min(xs)}, {max(xs)}]" if xs else "-"
    print("| rate | inputs | k0 | k2 | nb0 (> 0) | nb1 (two regions) | borders | failing |")
    print("|---|---|---|---|---|---|---|---|")
    for sr, r in summ.items():
      print(f"| {sr} | {r['n']} | {rng(r['k0'])} | {rng(r['k2'])} | {rng(r['nb0'])} | "
            f"{rng(r['nb1'])} | {rng(r['v'])} | {r['bad']} |")
  print(f"inputs: {rows}, failing: {bad}")
  print(f"nb0 (when > 0) in {nb0_rng}, nb1 (two regions) in {nb1_rng}, borders in {v_rng}")
  sys.exit(1 if bad else 0)


if __name__ == "__main__":
  main()
