# libm contract tests

`sbr_reset`'s specification (`Kraken/X64/Examples/Sbr/Parse/ResetSpec.lean`) treats `log2f` and
`powf` as functions `lg`, `pw` of their arguments and assumes one closed hypothesis about
them, `BandsOK lg pw`: over the finitely many integer inputs the code can reach, the band
counts it computes from `log2f` and the band borders it computes from `powf` stay in range.
There is no model of the C library's floating-point functions, so the hypothesis is not
proved; `bands_test.c` checks it on the machine.

```
./run.sh            # builds and runs bands_test.c with the system C compiler and libm
```

1. `BandsOK(log2f, powf)` for the C library's functions, every step computed with the
   instruction the Lean definition models (`cvtsi2ss`, `divss`, `mulss`, `cvtss2si`), so the
   arithmetic matches `BitVec.sitof32`/`f32div`/`f32mul`/`f32toi64` bit for bit. Exit status 1
   if it fails.
2. Robustness: the largest `k` such that `BandsOK` holds for every pair of functions whose
   values lie within `k` representable floats of the references `(float)log2((double)x)` and
   `(float)pow((double)a, (double)b)` (the checks use monotonicity, so only the ends of each
   window are evaluated; see the comments in the source), and the largest distance of the C
   library from the references over the inputs used.

Result (glibc, x86-64): `BandsOK(log2f, powf)` holds; the C library is within 1 ulp of the
references; `BandsOK` holds for every function within 42266 ulp of the references and fails at
42267 ulp (first region of `make_bands` at 16 kHz / 22.05 kHz, `bs_start_freq` 14 / 15,
`k[2] = 64`, `bs_freq_scale = 1`).
