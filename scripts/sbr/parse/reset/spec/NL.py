# Entries of shard B, part `f_tablenoise` (`derived3`, the noise-band border loop, l.605-611):
# L2bde..L2c5b, and L2c89 (the values `derived3` leaves, before `sbr_hf_calc_npatches`).
LEMMAS = r"""
/-! ## Shard B: `f_tablenoise` (`derived3`) -/

/-- `f_tablenoise` with entry `0` stored and the entries `1..j` computed. -/
def NzM (x : Args) (q j : Nat) : List UInt8 :=
  mk16 6 (fun k => if k = 0 then u16 x.ftLow 0
    else if k ≤ j then u16 x.ftLow (ntemp x.n0 q k) else u16 x.ftNoise k)

/-- `derived3` in progress: `n_q = q`, `j` entries computed. -/
abbrev dNz (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) (q j : Nat) : Args :=
  { dD2 a k0 nm f with nq := q, ftNoise := NzM (dD2 a k0 nm f) q j }

/-- In the noise-border loop: `1 ≤ n_q ≤ 5`, `j` entries computed, `r11 = n_master`,
`r12 = sbr`, the frame slots `rbp - 0x50` (`k[2]` as `f_master[n_master]`) and `rbp - 0x80`
(`kx[1]`); `P st n0 q j` the rest. -/
def AtNz (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : St → Nat → Nat → Nat → Prop) : Prop :=
  AtNq k e a ra t₀ s (fun st fr nm k0 => ∃ q j, 1 ≤ q ∧ q < 6 ∧ st.x = dNz a k0 nm (fOf st) q j
    ∧ s.regs.get64 .r11 = BitVec.ofNat 64 nm ∧ s.regs.get64 .r12 = arg1 t₀
    ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 ((fOf st) nm)
    ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 ((fOf st) (xoOf a))
    ∧ P st ((nm - (xoOf a) + 1) / 2) q j)
"""


def R(r, v):
  return f"s.regs.get64 .{r} = BitVec.ofNat 64 ({v})"


CX = "BitVec.setWidth 32 (s.regs.get64 .rcx) = BitVec.ofNat 32 q"


Q2 = "(q - q % 2)"

ENTRIES = {
    # `n_q ≥ 2`: the loop by two
    "L2bde": f"AtNz k e a ra t₀ s (fun st n0 q j => {CX} ∧ j = 0 ∧ 2 ≤ q ∧ {R('r15', 'n0')})",
    # loop head: `j` (even) entries computed, `temp = ntemp j` in `esi`, `r10 = n_q + 1 - (j + 1)`
    "L2bed": (f"AtNz k e a ra t₀ s (fun st n0 q j => {CX} ∧ j % 2 = 0 ∧ j + 2 ≤ {Q2} ∧ {R('r15', 'n0')} "
              f"∧ {R('r8', 'j')} ∧ {R('rsi', 'ntemp n0 q j')} ∧ {R('r10', 'q - j')} ∧ {R('r9', Q2)})"),
    # after the first store of the pair (`j` odd), `edi = ntemp j`, `eax = n0`
    "L2c1b": (f"AtNz k e a ra t₀ s (fun st n0 q j => {CX} ∧ j % 2 = 1 ∧ j + 1 ≤ {Q2} ∧ {R('r15', 'n0')} "
              f"∧ {R('r8', 'j - 1')} ∧ {R('rdi', 'ntemp n0 q j')} ∧ {R('rax', 'n0')} "
              f"∧ {R('r10', 'q - (j - 1)')} ∧ {R('r9', Q2)})"),
    # after the pair (`r10` not yet decremented)
    "L2c4a": (f"AtNz k e a ra t₀ s (fun st n0 q j => {CX} ∧ j % 2 = 0 ∧ 2 ≤ j ∧ j ≤ {Q2} ∧ {R('r15', 'n0')} "
              f"∧ {R('r8', 'j')} ∧ {R('rsi', 'ntemp n0 q j')} ∧ {R('r10', 'q - (j - 2)')} "
              f"∧ {R('r9', Q2)})"),
    # the last entry (`n_q` odd, or `n_q = 1`)
    "L2c5b": (f"AtNz k e a ra t₀ s (fun st n0 q j => {CX} ∧ j + 1 = q ∧ {R('r15', 'n0')} ∧ {R('r8', 'q')} "
              f"∧ {R('rsi', 'ntemp n0 q j')})"),
    # `derived3` done
    "L2c89": "AtNz k e a ra t₀ s (fun st n0 q j => j = q)",
}

VARS = {
    "L2bed": "[(s.regs.get64 .r9).toNat - (s.regs.get64 .r8).toNat, 1, 0]",
    "L2c1b": "[(s.regs.get64 .r9).toNat - (s.regs.get64 .r8).toNat, 1, 0]",
    "L2c4a": "[(s.regs.get64 .r9).toNat - (s.regs.get64 .r8).toNat, 2, 0]",
}
