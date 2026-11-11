LEMMAS = r"""
/-! ## Shard B (env): `sbr_make_f_derived`, the `f_tablelow` copy (`derived2`) -/

/-- `f_tablelow` with entry `0` stored and the entries `1..m` copied from `f_tablehigh`. -/
def LowM (x : Args) (xo : Nat) (f : Nat → Nat) (m : Nat) : List UInt8 :=
  mk16 25 (fun k => if k = 0 then f xo
    else if k ≤ m then f (xo + (2 * k - x.n1 % 2)) else u16 x.ftLow k)

/-- `derived1`'s values. -/
abbrev dD1 (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) : Args :=
  derived1 (x0D a k0) nm (xoOf a) f

/-- `derived2` in progress: `m` entries copied. -/
abbrev dLw (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) (m : Nat) : Args :=
  { dD1 a k0 nm f with ftLow := LowM (dD1 a k0 nm f) (xoOf a) f m }

/-- The remainder of the 16-wide loop (`n0 & 15`, or `16`). -/
abbrev R16 (n : Nat) : Nat := if n % 16 = 0 then 16 else n % 16

/-- The remainder of the 4-wide loop (`n0 & 3`, or `4`). -/
abbrev R4 (n : Nat) : Nat := if n % 4 = 0 then 4 else n % 4

/-- The `vpshufb` mask of the 16-wide loop (`.LCPI5_6`). -/
abbrev C56 : BitVec 128 := 0x0f0e0d0c0d0c09080d0c090805040100#128

/-- The `vpshufb` mask of the 4-wide loop (`.LCPI5_9`, `vmovq`). -/
abbrev C59 : BitVec 128 := 0x0d0c090805040100#128

/-- The `f_tablelow` copy: `m` entries done; `r14 = f xo`, `r15 = n0`, `r10 = f xo`, `rcx = f nm`
(stored by `L2b30`); `P n0 p m` the
registers (`p = n1 % 2`). -/
def AtLw (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : Nat → Nat → Nat → Prop) : Prop :=
  AtNq k e a ra t₀ s (fun st fr nm k0 => ∃ m, st.x = dLw a k0 nm (fOf st) m
    ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a))
    ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2)
    ∧ s.regs.get64 .r10 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((fOf st) nm)
    ∧ P ((nm - (xoOf a) + 1) / 2) ((nm - (xoOf a)) % 2) m)
"""

_R13 = "s.regs.get64 .r13 = BitVec.ofNat 64 p"
_X0_6 = "(s.zmms.get (AvxReg.xmm .mm0)).setWidth 128 = C56"
_X0_9 = "(s.zmms.get (AvxReg.xmm .mm0)).setWidth 128 = C59"
_L16 = ("s.regs.get64 .r8 = arg1 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ + BitVec.ofNat 64 (0x4c2b8 - 2 * p) "
        "∧ s.regs.get64 .r9 = BitVec.ofNat 64 (n0 - R16 n0) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (R16 n0) "
        "∧ s.regs.get64 .rax = BitVec.ofNat 64 (n0 - R16 n0 + 1)")

ENTRIES = {
    # 16 ≤ n1 + 1 ≥ 34: the 16-wide loop
    "L29f4": f"AtLw k e a ra t₀ s (fun n0 p m => m = 0 ∧ 17 ≤ n0 ∧ {_R13})",
    "L2a26": f"AtLw k e a ra t₀ s (fun n0 p m => m = 0 ∧ 17 ≤ n0 ∧ {_R13} ∧ {_L16})",
    "L2a30": f"AtLw k e a ra t₀ s (fun n0 p m => 17 ≤ n0 ∧ {_R13} ∧ {_L16} ∧ m % 16 = 0 "
             f"∧ m < n0 - R16 n0 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 m ∧ {_X0_6})",
    "L2a77": f"AtLw k e a ra t₀ s (fun n0 p m => 17 ≤ n0 ∧ {_R13} ∧ {_L16} ∧ m % 16 = 0 ∧ 16 ≤ m "
             f"∧ m ≤ n0 - R16 n0 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 (m - 16) ∧ {_X0_6})",
    # the 4-wide loop (from `L20d8` with `5 ≤ n0 ≤ 16`, or after the 16-wide loop)
    "L2a85": f"AtLw k e a ra t₀ s (fun n0 p m => {_R13} ∧ m % 16 = 0 ∧ m + 5 ≤ n0 "
             "∧ s.regs.get64 .r9 = BitVec.ofNat 64 m)",
    "L2aaf": f"AtLw k e a ra t₀ s (fun n0 p m => {_R13} ∧ m % 16 = 0 ∧ m + 5 ≤ n0 "
             "∧ s.regs.get64 .r9 = BitVec.ofNat 64 m ∧ s.regs.get64 .r8 = arg1 t₀ "
             "∧ s.regs.get64 .rsi = arg1 t₀ + BitVec.ofNat 64 (2 * m) "
             "∧ s.regs.get64 .rdx = BitVec.ofNat 64 (n0 - R4 n0 - m) "
             "∧ s.regs.get64 .rax = BitVec.ofNat 64 (n0 - R4 n0 + 1))",
    "L2ad6": f"AtLw k e a ra t₀ s (fun n0 p m => {_R13} ∧ ∃ b j, m = b + j ∧ b % 4 = 0 ∧ j % 4 = 0 "
             "∧ b + j < n0 - R4 n0 ∧ s.regs.get64 .rdi = BitVec.ofNat 64 j "
             "∧ s.regs.get64 .rdx = BitVec.ofNat 64 (n0 - R4 n0 - b) "
             "∧ s.regs.get64 .rax = BitVec.ofNat 64 (n0 - R4 n0 + 1) "
             "∧ s.regs.get64 .rsi = arg1 t₀ + BitVec.ofNat 64 (0x4c254 + 2 * b) "
             f"∧ s.regs.get64 .r8 = arg1 t₀ + BitVec.ofNat 64 (0x4c288 + 4 * b - 2 * p) ∧ {_X0_9})",
    # the scalar loop (the remainder)
    "L2aef": f"AtLw k e a ra t₀ s (fun n0 p m => m < n0 ∧ {_R13} "
             "∧ s.regs.get64 .rax = BitVec.ofNat 64 (m + 1))",
    "L2b20": "AtLw k e a ra t₀ s (fun n0 p m => ∃ b j, m = b + j ∧ m < n0 "
             "∧ s.regs.get64 .rsi = BitVec.ofNat 64 j ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (n0 - b) "
             "∧ s.regs.get64 .rdx = arg1 t₀ + BitVec.ofNat 64 (0x4c252 + 2 * (b + 1)) "
             "∧ s.regs.get64 .rax = arg1 t₀ + BitVec.ofNat 64 (0x4c284 + 4 * (b + 1) - 2 * p))",
}

VARS = {
    "L2a30": "[(s.regs.get64 .r9).toNat - (s.regs.get64 .rdi).toNat, 1, 0]",
    "L2a77": "[(s.regs.get64 .r9).toNat - (s.regs.get64 .rdi).toNat, 0, 0]",
    "L2ad6": "[(s.regs.get64 .rdx).toNat - (s.regs.get64 .rdi).toNat, 0, 0]",
    "L2b20": "[(s.regs.get64 .r8).toNat - (s.regs.get64 .rsi).toNat, 0, 0]",
}
