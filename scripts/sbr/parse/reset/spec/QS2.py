# Entries of AV_QSORT copy 2 inlined in sbr_reset (the vk0 sort of shard A2; owner: gC): the
# labels strictly inside the copy. Same code as copies 1, 3, 4 (spec/QS.py) up to the registers
# (`REG2`), so the entries and the variant are `copy_entries` of spec/QS.py; the array is `vk0`
# (frame offset 0x400, `num_bands_0` elements), the exit `L1bbd` (spec/A2.py) needs its range
# and its sum.
import importlib.util
import os

_spec = importlib.util.spec_from_file_location(
    "qs_shared", os.path.join(os.path.dirname(os.path.abspath(__file__)), "QS.py"))
_qs = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_qs)

COPY2 = dict(
    labels="L1980 L1988 L19b0 L19dd L1a00 L1a0c L1a10 L1a1f L1a40 L1a50 L1a70 L1a84 L1a89 L1a90 "
           "L1ab0 L1ab4 L1ad0 L1ad4 L1af3 L1b00 L1b17 L1b20 L1b52 L1b70 L1ba0".split(),
    O="0x400", N=_qs.N0, R=f"(fun A0 => QS.AB {_qs.N0} A0 64 {_qs.TOT0})", regs=_qs.REG2,
    wrap=lambda b: _qs.S(f"{_qs.SF} ∧ {_qs.NB0} ∧ {_qs.R12} ∧ {_qs.R15} "
                         f"∧ {_qs.r('rax', _qs.n64(_qs.N0))} ∧ {b}"))

ENTRIES, VARS = _qs.copy_entries(COPY2)
