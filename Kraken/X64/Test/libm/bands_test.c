/* Machine test of `Reset.BandsOK lg pw` (Kraken/X64/Examples/Sbr/Parse/ResetSpec.lean) for
 * the C library's log2f and powf, and for every function within k ulp of a reference.
 *
 * Every step is the instruction the Lean definition models, so the arithmetic matches
 * bit for bit:
 *   BitVec.sitof32  cvtsi2ss      BitVec.f32div  divss      BitVec.f32mul  mulss
 *   BitVec.f32toi64 cvtss2si (64-bit destination, round to nearest even, indefinite on
 *                   NaN/overflow), default MXCSR.
 *
 * 1. `lg = log2f`, `pw = powf` of the C library: BandsOK must hold (exit 1 if not).
 * 2. Robustness: the reference values `ref_lg(x) = (float)log2((double)x)` and
 *    `ref_pw(a, b) = (float)pow((double)a, (double)b)`; for k ulp, every function whose value
 *    at each input lies within k representable floats of the reference. Each case of BandsOK
 *    reads `lg` at one or two inputs and `pw` at one or two; all perturbations are tried
 *    independently per use (sound: it covers every such function, and more). Reports the
 *    largest k for which BandsOK holds for all of them (binary search; failure is monotone
 *    in k since the windows grow) and the largest distance of the C library from the
 *    reference over the inputs used.
 */
#include <immintrin.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static float sitof32(int32_t a) { return _mm_cvtss_f32(_mm_cvtsi32_ss(_mm_setzero_ps(), a)); }
static float f32div(float a, float b) {
  return _mm_cvtss_f32(_mm_div_ss(_mm_set_ss(a), _mm_set_ss(b)));
}
static float f32mul(float a, float b) {
  return _mm_cvtss_f32(_mm_mul_ss(_mm_set_ss(a), _mm_set_ss(b)));
}
static int64_t f32toi64(float a) { return _mm_cvtss_si64(_mm_set_ss(a)); }

/* ParseModel.rates / rateRow / sbrOffset / k0Of, ResetSpec.maxQ / invwarp. */
static const int rates[12] = {16000, 22050, 24000, 32000, 44100, 48000,
                              64000, 88200, 96000, 128000, 176400, 192000};
static int rate_row(int sr) {
  switch (sr) {
    case 16000: return 0; case 22050: return 1; case 24000: return 2; case 32000: return 3;
    case 44100: case 48000: case 64000: return 4;
    default: return 5;
  }
}
static const int sbr_offset[6][16] = {
    {-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7},
    {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13},
    {-5, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16},
    {-6, -4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16},
    {-4, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16, 20},
    {-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 13, 16, 20, 24}};
static int k0_of(int sr, int row, int start) {
  int temp = sr < 32000 ? 3000 : sr < 64000 ? 4000 : 5000;
  return (temp * 128 + sr / 2) / sr + sbr_offset[row][start];
}
static int max_q(int sr) { return sr <= 32000 ? 48 : sr == 44100 ? 35 : 32; }
static float invwarp(int alter) {
  uint32_t u = alter ? 0x3f44ec4fu : 0x3f800000u;
  float f; memcpy(&f, &u, 4); return f;
}

/* ---- the functions under test: lg, pw at a perturbation `d` of a base function ---- */
static int use_libc;  /* 1: log2f/powf, 0: the reference */
static float base_lg(float x) { return use_libc ? log2f(x) : (float)log2((double)x); }
static float base_pw(float a, float b) {
  return use_libc ? powf(a, b) : (float)pow((double)a, (double)b);
}

/* BandsAt for the pw value `b`: every cvtss2si(start * b^j), 1 <= j < nb, in [0, 64]. */
static int bands_at_val(int start, float b, int64_t nb) {
  float prod = sitof32(start);
  for (int64_t j = 1; j < nb; j++) {
    prod = f32mul(b, prod);
    int64_t v = f32toi64(prod);
    if (v < 0 || v > 64) return 0;
  }
  return 1;
}

static int K;  /* the perturbation window */
static long fails;
static int verbose;

/* The window of k ulp around x: its ends, by the order-preserving map of floats to
 * integers (infinities are the ends of the order; a NaN stays a NaN). */
static int64_t ord(float x) {
  int32_t i; memcpy(&i, &x, 4);
  return i < 0 ? -(int64_t)(i & 0x7fffffff) : (int64_t)i;
}
static float unord(int64_t o) {
  const int64_t inf = 0x7f800000;
  if (o > inf) o = inf;
  if (o < -inf) o = -inf;
  int32_t i = o < 0 ? (int32_t)((-o) | 0x80000000u) : (int32_t)o;
  float x; memcpy(&x, &i, 4); return x;
}
static float lo_end(float x, int k) { return isnan(x) ? x : unord(ord(x) - k); }
static float hi_end(float x, int k) { return isnan(x) ? x : unord(ord(x) + k); }

/* Monotonicity: for h > 0, `l -> cvtss2si(l * h)` is non-decreasing (mulss by a positive
 * number and rounding are monotone), so the band counts over the window of `lg` values are
 * all integers between the counts at its ends. For b > 0 and start > 0 every product
 * `start * b^j` is non-decreasing in b, so BandsAt holds on the window of `pw` values iff it
 * holds at both ends; a window reaching b <= 0 is counted as a failure (conservative). The
 * counts at the ends are required to stay far from the int32 wrap of `2 * v`. */
static int bands_at_all(int start, int stop, int64_t nb) {
  float a = f32div(sitof32(stop), sitof32(start));
  float e = f32div(1.0f, sitof32((int32_t)nb));
  float b0 = base_pw(a, e);
  float lo = lo_end(b0, K), hi = hi_end(b0, K);
  if (!(lo > 0) && nb >= 2) return 0;
  return bands_at_val(start, lo, nb) && bands_at_val(start, hi, nb);
}

static int range_nb(float l, float h, int64_t *lo, int64_t *hi) {
  int64_t a = f32toi64(f32mul(lo_end(l, K), h)), b = f32toi64(f32mul(hi_end(l, K), h));
  if (a < -(1 << 29) || a > (1 << 29) || b < -(1 << 29) || b > (1 << 29)) return 0;
  *lo = 2 * a; *hi = 2 * b;
  return 1;
}

static int check_case(int sr, int start, int k2, int fs, int alter) {
  int k0 = k0_of(sr, rate_row(sr), start);
  if (k0 < 0) k0 = 0;
  if (!(k0 <= k2) || !(k2 - k0 <= max_q(sr))) return 1;
  float h0 = sitof32(7 - fs);
  int two = 110 * k0 < 49 * k2;
  int k1 = two ? 2 * k0 : k2;
  float q0 = f32div(sitof32(k1), sitof32(k0));
  int64_t lo, hi;
  if (!range_nb(base_lg(q0), h0, &lo, &hi)) return 0;
  for (int64_t nb0 = lo; nb0 <= hi; nb0 += 2)
    if (0 < nb0 && !(nb0 <= 48 && bands_at_all(k0, k1, nb0))) {
      if (verbose) printf("  fail first region sr=%d start=%d k2=%d fs=%d nb0=%lld\n",
                          sr, start, k2, fs, (long long)nb0);
      return 0;
    }
  if (two) {
    float q1 = f32div(sitof32(k2), sitof32(k1));
    float h1 = f32mul(h0, invwarp(alter));
    if (!range_nb(base_lg(q1), h1, &lo, &hi)) return 0;
    for (int64_t nb1 = lo; nb1 <= hi; nb1 += 2)
      if (!(2 <= nb1 && nb1 <= 48 && bands_at_all(k1, k2, nb1))) {
        if (verbose)
          printf("  fail second region sr=%d start=%d k2=%d fs=%d alter=%d nb1=%lld\n",
                 sr, start, k2, fs, alter, (long long)nb1);
        return 0;
      }
  }
  return 1;
}

/* NqOK: `cvtss2si(l * nb) < 2^32`; for nb > 0 monotone in l, so the ends of the window
 * decide it (nb = 0 gives 0, or the indefinite value for an infinite l). */
static int nq_ok(void) {
  for (int k2 = 0; k2 <= 64; k2++)
    for (int kx = 0; kx <= 32; kx++) {
      float l = base_lg(f32div(sitof32(k2), sitof32(kx)));
      float ends[3] = {lo_end(l, K), l, hi_end(l, K)};
      for (int t = 0; t < 3; t++)
        for (int nb = 0; nb < 256; nb++)
          if (!(f32toi64(f32mul(ends[t], sitof32(nb))) < (int64_t)1 << 32)) {
            if (verbose) printf("  fail NqOK k2=%d kx=%d nb=%d\n", k2, kx, nb);
            return 0;
          }
    }
  return 1;
}

static int bands_ok(void) {
  fails = 0;
  for (int r = 0; r < 12; r++)
    for (int start = 0; start < 16; start++)
      for (int k2 = 0; k2 <= 64; k2++)
        for (int fs = 1; fs <= 3; fs++)
          for (int alter = 0; alter <= 1; alter++)
            if (!check_case(rates[r], start, k2, fs, alter)) {
              fails++;
              if (!verbose) return 0;
            }
  return fails == 0 && nq_ok();
}

/* The largest ulp distance between the C library and the reference over the inputs used. */
static long ulp_dist(float a, float b) {
  int32_t x, y; memcpy(&x, &a, 4); memcpy(&y, &b, 4);
  if (x < 0) x = INT32_MIN - x;
  if (y < 0) y = INT32_MIN - y;
  return labs((long)x - (long)y);
}

static void libc_vs_ref(void) {
  long mlg = 0, mpw = 0;
  for (int s = 1; s <= 64; s++)
    for (int t = 0; t <= 64; t++) {
      float q = f32div(sitof32(t), sitof32(s));
      if (q > 0 && isfinite(q)) {
        long d = ulp_dist(log2f(q), (float)log2((double)q));
        if (d > mlg) mlg = d;
      }
      for (int nb = 1; nb <= 48; nb++) {
        float e = f32div(1.0f, sitof32(nb));
        if (q > 0 && isfinite(q)) {
          long d = ulp_dist(powf(q, e), (float)pow((double)q, (double)e));
          if (d > mpw) mpw = d;
        }
      }
    }
  printf("libc vs reference: log2f max %ld ulp, powf max %ld ulp\n", mlg, mpw);
}

int main(int argc, char **argv) {
  verbose = 0;
  use_libc = 1; K = 0;
  int ok_libc = bands_ok();
  printf("BandsOK(log2f, powf) of the C library: %s\n", ok_libc ? "PASS" : "FAIL");
  libc_vs_ref();
  use_libc = 0;
  K = 0;
  if (!bands_ok()) { printf("reference: FAIL at k = 0\n"); return 1; }
  int lo = 0, hi = 1;
  while (hi <= (1 << 22)) {
    K = hi;
    if (!bands_ok()) break;
    lo = hi; hi *= 2;
  }
  if (hi > (1 << 22)) {
    printf("robust: holds for every function within %d ulp of the reference\n", lo);
  } else {
    while (hi - lo > 1) {
      int mid = lo + (hi - lo) / 2;
      K = mid;
      if (bands_ok()) lo = mid; else hi = mid;
    }
    printf("robust: holds for every function within %d ulp of the reference; "
           "fails at %d ulp:\n", lo, hi);
    K = hi; verbose = 1; bands_ok();
    printf("  (%ld failing cases)\n", fails);
  }
  return ok_libc ? 0 : 1;
}
