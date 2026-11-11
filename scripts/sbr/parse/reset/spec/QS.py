# Entries of the AV_QSORT copies inlined in sbr_reset (owner: qsort): the labels strictly inside
# each copy. The entry before a copy and the one after it are the boundary predicates of the
# shard that owns the surrounding code (spec/A1.py: the stop_dk sort; spec/A2.py: the vk0 sort,
# the vk1 sorts); an id may be defined in one spec file only. Each entry is the Lean text of a
# Prop in `k e a ra t₀ s`; `LEMMAS` (Lean text) goes after the LEMMAS of A1.py/A2.py/B.py.
#
# The four copies sort an `int16` array of the frame region `fr` (element `q`, 0-based, is
# `A2.fv fr o (q + 1)`), with the explicit stack of `AV_QSORT` at `fr[16 j]` (start) and
# `fr[16 j + 8]` (end, inclusive). Copies 1, 3, 4 are the same code (registers `REG1`); copy 2
# (registers `REG2`) is in spec/QS2.py. The exits need only the range and the sum of the array,
# so the invariant is `QW` of `Parse/LibQsort.lean` (a permutation) with `Depth`,
# the variant `[Φ, phase, dist]` with `Φ` the weight of the stack (read from memory) plus the
# current interval.

LEMMAS = r"""
/-! ## The `AV_QSORT` copies -/

namespace QS

/-- Element `q` (0-based) of the `int16` frame array at offset `o`. -/
abbrev av (fr : List UInt8) (o : Nat) : Nat → Int := fun q => A2.fv fr o (q + 1)

/-- The address of element `0` of the frame array at offset `o`. -/
abbrev pA (t₀ : MachineData) (o : Nat) : BitVec 64 :=
  t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (o + 2)

/-- The address of element `q`. -/
abbrev ep (t₀ : MachineData) (o q : Nat) : BitVec 64 := pA t₀ o + BitVec.ofNat 64 (2 * q)

/-- The median position of `[lo, e]`. -/
abbrev mid (lo e : Nat) : Nat := lo + (e - lo) / 2

/-- The stack in the frame holds the pending intervals `S` (`start`, inclusive `end`). -/
def StkRel (fr : List UInt8) (t₀ : MachineData) (o : Nat) (S : List Parse.Qsort.Iv) : Prop :=
  ∀ j (h : j < S.length), frSlot64 fr (0x570 - 16 * j) = ep t₀ o S[j].1
    ∧ frSlot64 fr (0x568 - 16 * j) = ep t₀ o S[j].2 - 2#64

/-- `A0[0 .. N)` in `[-B, B]`, summing to `tot`. -/
def AB (N : Nat) (A0 : Nat → Int) (B tot : Int) : Prop :=
  (∀ q, q < N → -B ≤ A0 q ∧ A0 q ≤ B) ∧ Parse.Qsort.sumTo A0 N = tot

/-- Between partitions: the stack `S` (`sp = |S|`), the array a permutation of some `A0`. -/
def Pop (R : (Nat → Int) → Prop) (t₀ : MachineData) (N o : Nat) (fr : List UInt8)
    (sp : BitVec 64) : Prop :=
  1 ≤ N ∧ N ≤ 49 ∧ ∃ (S : List Parse.Qsort.Iv) (A0 : Nat → Int), sp = BitVec.ofNat 64 S.length
    ∧ Parse.Qsort.Depth N S ∧ R A0 ∧ StkRel fr t₀ o S ∧ Parse.Qsort.QW N (av fr o) A0 S

/-- On the current interval `[lo, hi1)`, with the facts `P S A lo hi1` (`A` the array). -/
def Cur (R : (Nat → Int) → Prop) (t₀ : MachineData) (N o : Nat) (fr : List UInt8)
    (sp : BitVec 64) (P : List Parse.Qsort.Iv → (Nat → Int) → Nat → Nat → Prop) : Prop :=
  1 ≤ N ∧ N ≤ 49 ∧ ∃ (S : List Parse.Qsort.Iv) (A0 : Nat → Int) (lo hi1 : Nat),
    sp = BitVec.ofNat 64 S.length ∧ Parse.Qsort.Depth N S ∧ (hi1 - lo) * 2 ^ S.length ≤ N
    ∧ R A0 ∧ StkRel fr t₀ o S ∧ Parse.Qsort.QW N (av fr o) A0 (S ++ [(lo, hi1)])
    ∧ P S (av fr o) lo hi1

/-- As `Cur` for an array `A`, with memory `A` updated at `pos` by `A lo` (half a swap). -/
def CurU (R : (Nat → Int) → Prop) (t₀ : MachineData) (N o : Nat) (fr : List UInt8)
    (sp : BitVec 64) (P : List Parse.Qsort.Iv → (Nat → Int) → Nat → Nat → Nat → Prop) : Prop :=
  1 ≤ N ∧ N ≤ 49 ∧ ∃ (S : List Parse.Qsort.Iv) (A A0 : Nat → Int) (lo hi1 pos : Nat),
    sp = BitVec.ofNat 64 S.length ∧ Parse.Qsort.Depth N S ∧ (hi1 - lo) * 2 ^ S.length ≤ N
    ∧ R A0 ∧ StkRel fr t₀ o S ∧ Parse.Qsort.QW N A A0 (S ++ [(lo, hi1)])
    ∧ (∀ q, av fr o q = Parse.Qsort.upd A pos (A lo) q) ∧ P S A lo hi1 pos

/-- The partition invariant on `[lo, e]`: `left = l`, `right = rt`, the pivot `pv` at `e - 1`. -/
def PInv (A : Nat → Int) (lo e l rt : Nat) (pv : Int) : Prop :=
  lo + 1 ≤ l ∧ l ≤ rt + 2 ∧ rt + 2 ≤ e ∧ l + 1 ≤ e ∧ A (e - 1) = pv

/-- After the pivot is placed at `l`. -/
def PDone (A : Nat → Int) (lo e l rt : Nat) : Prop :=
  lo + 1 ≤ l ∧ l ≤ rt + 2 ∧ rt < l ∧ l + 1 ≤ e

/-- The weight of the stack in memory, `n` entries. -/
def stkPhi (s : MachineData) (n : Nat) : Nat :=
  ((List.range n).map fun j => Parse.Qsort.wBn 2 (slot64 s (0x570 - 16 * j)).toNat
    (slot64 s (0x568 - 16 * j)).toNat).sum

end QS
"""

# ---------------------------------------------------------------------------------------------
# helpers producing Lean text (as in spec/A2.py)

def S(body):
  return f"A2.S k e a ra t₀ s (fun k0 k2 st fr => {body})"

def r(reg, v):
  return f"s.regs.get64 .{reg} = {v}"

def n64(v):
  return f"BitVec.ofNat 64 ({v})"

R12 = "s.regs.get64 .r12 = arg1 t₀"
R15 = "s.regs.get64 .r15 = arg0 t₀"
K1 = "(A2.k1Of k0 k2)"
N0 = "(A2.n0N e a k0 k2)"
N1 = "(A2.n1N e a k0 k2)"
SF = "A2.SF fr e a t₀ k0 k2"
NB0 = "A2.N0 e a k0 k2"
NB1 = "A2.N1 e a k0 k2"
VM = "-64 ≤ vm ∧ vm ≤ 64"
INC0 = f"A2.Inc fr 0x400 {N0} k0 {K1}"
TWO = f"110 * k0 < 49 * k2 ∧ {INC0} ∧ {NB0}"
R15N1 = (f"(s.regs.get64 .r15).setWidth 32 + (s.regs.get64 .r15).setWidth 32 "
         f"= BitVec.ofNat 32 {N1}")
QX = f"{TWO} ∧ {NB1} ∧ {R15N1} ∧ {R12} ∧ {r('r13', n64(N1))}"
TOT0 = f"(({K1} : Nat) - (k0 : Int))"
TOT1 = f"(((k2 : Nat) : Int) - (({K1} : Nat) : Int))"
S30N1 = f"frSlot64 fr 0x30 = {n64(N1)}"

# ---------------------------------------------------------------------------------------------
# the copies

REG1 = dict(SP="rax", ST="rdx", EN="rcx", E1="rdi", MD="rsi", X="r8", Y="r9", F="r10", Z="r11",
            T="r14")
REG2 = dict(SP="rcx", ST="rsi", EN="rdx", E1="r8", MD="rdi", X="r9", Y="r10", F="r11", Z="r14",
            T="r13")

COPIES = [
    dict(labels="L12d0 L12d8 L1300 L132d L1350 L135c L1360 L136f L1390 L13a0 L13c0 L13d4 L13d9 "
                "L13e0 L1400 L1404 L1420 L1424 L1442 L1450 L1467 L1470 L14a2 L14c0 L14f0".split(),
         O="0x4fe", N="13", R="(fun _ => True)", regs=REG1,
         wrap=lambda b: f"SD k e a ra t₀ s (fun _ fr => {b})"),
    dict(labels="L2390 L2398 L23c0 L23ed L2410 L241c L2420 L242f L2450 L2460 L2480 L2494 L2499 "
                "L24a0 L24c0 L24c4 L24e0 L24e4 L2502 L2510 L2527 L2530 L2562 L2580 L25b0".split(),
         O="0x480", N=N1, R=f"(fun A0 => QS.AB {N1} A0 64 {TOT1})", regs=REG1,
         wrap=lambda b: S(f"{QX} ∧ {S30N1} ∧ ∃ vm, {VM} ∧ A2.TA fr t₀ {N0} vm ∧ {b}")),
    dict(labels="L2640 L2648 L2670 L269d L26c0 L26cc L26d0 L26df L2700 L2710 L2730 L2744 L2749 "
                "L2750 L2770 L2774 L2790 L2794 L27b2 L27c0 L27d7 L27e0 L2812 L2830 L2860".split(),
         O="0x480", N=N1, R=f"(fun A0 => QS.AB {N1} A0 256 {TOT1})", regs=REG1,
         wrap=lambda b: S(f"{QX} ∧ {S30N1} ∧ ∃ vm, A2.TA fr t₀ {N0} vm ∧ {b}")),
]


def copy_entries(c):
  R, O, N, Rp, wrap = c["regs"], c["O"], c["N"], c["R"], c["wrap"]
  g = lambda role: f"s.regs.get64 .{R[role]}"
  EP = lambda q: f"QS.ep t₀ {O} ({q})"
  w16 = lambda role, v: f"({g(role)}).setWidth 16 = BitVec.ofInt 16 ({v})"
  POS = f"{g('ST')} = {EP('lo')} ∧ {g('EN')} = {EP('hi1')} - 2#64"
  M = "QS.mid lo (hi1 - 1)"
  E = "(hi1 - 1)"
  AM = f"A ({M})"
  AE = f"A {E}"
  MED0 = f"lo + 3 ≤ hi1 ∧ {g('E1')} = {EP('hi1 - 2')} ∧ {g('MD')} = {EP(M)}"
  E1EQ = f"{g('E1')} = {EP('hi1 - 2')}"

  def pop(extra):
    return wrap(f"QS.Pop {Rp} t₀ {N} {O} fr ({g('SP')}){extra}")

  def cur(P):
    return wrap(f"QS.Cur {Rp} t₀ {N} {O} fr ({g('SP')}) (fun S A lo hi1 => {POS} ∧ {P})")

  def curu(P):
    return wrap(f"QS.CurU {Rp} t₀ {N} {O} fr ({g('SP')}) (fun S A lo hi1 pos => {POS} ∧ {P})")

  def pt(P):
    return cur(f"{E1EQ} ∧ ∃ l rt pv, QS.PInv A lo {E} l rt pv ∧ {g('Y')} = {EP('l')} "
               f"∧ {g('X')} = {EP('rt')} ∧ {P}")

  def dn(P):
    return cur(f"∃ l rt, QS.PDone A lo {E} l rt ∧ {g('Y')} = {EP('l')} "
               f"∧ {g('X')} = {EP('rt')} ∧ {P}")

  MV = f"{MED0} ∧ {w16('Y', 'A lo')} ∧ {w16('Z', AE)} ∧ {w16('X', AM)}"
  CH = lambda role: f"∃ m, lo ≤ m ∧ m ≤ {E} ∧ {g(role)} = {EP('m')}"
  ents = [
      pop(""),
      pop(f" ∧ {g('SP')} ≠ 0#64"),
      cur("True"),
      cur(MV),
      cur(MV),
      cur(f"{MED0} ∧ {w16('Y', 'A lo')} ∧ {w16('X', AM)}"),
      curu(f"{MED0} ∧ {w16('X', 'A pos')} ∧ (pos = {M} ∨ pos = {E})"),
      cur(f"{MED0} ∧ {w16('X', AM)} ∧ {w16('Z', AE)}"),
      cur(f"{MED0} ∧ {w16('X', AM)}"),
      cur(f"{MED0} ∧ lo + 4 ≤ hi1 ∧ {w16('Z', AM)} "
          f"∧ {g('X')} = {EP('hi1 - 3')}"),
      pt(f"l ≤ rt ∧ {w16('T', 'A rt')}"),
      pt("True"),
      pt("l ≤ rt"),
      pt(f"l ≤ rt ∧ {w16('Z', 'pv')}"),
      pt(f"l ≤ rt ∧ {w16('Z', 'pv')}"),
      pt(f"l ≤ rt + 1 ∧ {w16('Z', 'pv')}"),
      pt("rt < l"),
      pt(f"rt < l ∧ {w16('Z', 'pv')}"),
      dn("True"),
      dn(CH("E1")),
      dn(CH("MD")),
      dn("True"),
      dn(f"{E} - l < l - lo ∧ QS.StkRel fr t₀ {O} (S ++ [(lo, rt + 1)])"),
      dn(f"l - lo ≤ {E} - l"),
      cur("hi1 = lo + 2"),
  ]
  rn = lambda role: f"(s.regs.get64 .{R[role]}).toNat"
  PHS = f"QS.stkPhi s {rn('SP')}"
  PHC = f"{PHS} + Parse.Qsort.wBn 2 {rn('ST')} {rn('EN')}"
  DP = f"(({rn('X')} + 4 - {rn('Y')}) / 2)"
  LLE = f"{rn('Y')} ≤ {rn('X')}"
  def V(phi, ph, d="0"):
    return f"[{phi}, {ph}, {d}]"
  vars_ = [V(PHS, "3500"), V(PHS, "3500")] + [V(PHC, "3000")] * 8 + [
      V(PHC, f"1000 + 4 * {DP}"),
      V(PHC, f"if {LLE} then 1000 + 4 * {DP} + 3 else 1000"),
      V(PHC, f"1000 + 4 * {DP} + 3"),
      V(PHC, f"1000 + 4 * {DP} + 3"),
      V(PHC, f"1000 + 4 * {DP} + 1"),
      V(PHC, f"if {LLE} then 1000 + 4 * {DP} + 2 else 1001"),
      V(PHC, "900"),
      V(PHC, "900"),
      V(PHC, "800"),
      V(PHC, "500", f"{rn('EN')} - {rn('E1')}"),
      V(PHC, "400"),
      V(PHC, "300"),
      V(PHC, "300"),
      V(PHC, "300"),
      V(PHC, "3000"),
  ]
  assert len(ents) == 25 and len(vars_) == 25 and len(c["labels"]) == 25
  return dict(zip(c["labels"], ents)), dict(zip(c["labels"], vars_))


ENTRIES = {}
VARS = {}
for _c in COPIES:
  _e, _v = copy_entries(_c)
  ENTRIES.update(_e)
  VARS.update(_v)

# the entering blocks of copies 3 and 4 (after the start is stored, the end in `rax`)
_EP3 = "QS.ep t₀ 0x480"
ENTRIES["L237d"] = S(f"{QX} ∧ {S30N1} ∧ ∃ vm, {VM} ∧ A2.TA fr t₀ {N0} vm "
                     f"∧ frSlot64 fr 0x570 = QS.pA t₀ 0x480 "
                     f"∧ {r('rax', _EP3 + ' ' + N1 + ' - 2#64')} "
                     f"∧ A2.Arr fr 0x480 {N1} 64 {TOT1}")
ENTRIES["L262c"] = S(f"{QX} ∧ {S30N1} ∧ ∃ vm, A2.TA fr t₀ {N0} vm "
                     f"∧ frSlot64 fr 0x570 = QS.pA t₀ 0x480 "
                     f"∧ {r('rax', _EP3 + ' ' + N1 + ' - 2#64')} "
                     f"∧ A2.Arr fr 0x480 {N1} 256 {TOT1}")
