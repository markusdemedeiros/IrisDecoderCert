# Entries of shard A1 (owner: rsA1): the prologue, the sample-rate dispatch, k[0], the stop
# frequency (make_bands(stop_min, 64, 13), the stop_dk AV_QSORT, the sum), k[2] and its checks,
# and the bs_freq_scale = 0 path of sbr_make_f_master (dk bands, check_n_master, the prefix sums).

LEMMAS = r"""
/-! ## Shard A1: `sbr_make_f_master` up to `L2012` -/

/-- `sbr->sample_rate` as an integer. -/
abbrev srI (a : RArgs) : Int := a.x.sampleRate.toInt

/-- The row `sbr_offset[r]` at its label. -/
def offLab : Nat → BitVec 64
  | 0 => lab "sbr_offset_0"
  | 1 => lab "sbr_offset_1"
  | 2 => lab "sbr_offset_2"
  | 3 => lab "sbr_offset_3"
  | 4 => lab "sbr_offset_4"
  | _ => lab "sbr_offset_5"

/-- `temp` of `sbr_make_f_master` (`3000`, `4000`, `5000`). -/
def tmpOf (sr : Nat) : Nat := if sr < 32000 then 3000 else if sr < 64000 then 4000 else 5000

/-- `k[0]` for the row. -/
abbrev k0A (a : RArgs) (row : Nat) : Int := k0Of (srI a) row (u8 a.sp 0)

abbrev k0N (a : RArgs) (row : Nat) : Nat := (k0A a row).toNat

/-- The decoder values with `k[0]` stored. -/
abbrev xk0 (a : RArgs) (row : Nat) : Args := { a.x with k0 := k0N a row }

/-- Inside `sbr_make_f_master`: the side conditions, `rsp`/`rbp`, the memory `Mm` at values
`st` whose decoder values are `x`, and `P` on the rest. -/
def A1S (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) (x : Args)
    (P : St → List UInt8 → Prop) : Prop :=
  ResetCI a t₀ ∧ BandsOK e.lg e.pw ∧ Base t₀ s
  ∧ ∃ (st : St) (fr : List UInt8), st.x = x ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ P st fr ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)

/-- The pushed registers after `j` pushes (`j = 2`: `rbp`, `r15`; `j = 4`: also `r14`, `r13`). -/
def ProM (j : Nat) (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  match j with
  | 2 => c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ c8 (r - 0x10#64) (t₀.regs.get64 .r15)
  | _ => c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
      ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14) ⋆ c8 (r - 0x20#64) (t₀.regs.get64 .r13)))

/-- The prologue after `j` pushes: the rest of the reservation below them. -/
def Pro (j : Nat) (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ BandsOK e.lg e.pw
  ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - BitVec.ofNat 64 (8 * j)
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
  ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
  ∧ s.regs.get64 .rbx = t₀.regs.get64 .rbx ∧ s.regs.get64 .r12 = t₀.regs.get64 .r12
  ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13 ∧ s.regs.get64 .r14 = t₀.regs.get64 .r14
  ∧ (s.dmem =⋆ ProM j t₀ ⋆ (Reserve (resetNeed k - 8 * j)
      (t₀.regs.get64 .rsp - BitVec.ofNat 64 (8 * j)) ⋆ (RetCell ra (t₀.regs.get64 .rsp)
      ⋆ (RF e a t₀ ⋆ a.x.R))))

/-- The rate dispatch: nothing written, `rcx` the rate. -/
def RD (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  A1S k e a ra t₀ s a.x (fun _ _ => True) ∧ s.regs.get64 .r12 = arg1 t₀
  ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .rcx = a.x.sampleRate.setWidth 64

/-- After `k[0]` (row `row`): `r12 = sbr`, `r15 = ac`, `P` on the rest. -/
def K0S (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : Nat → St → List UInt8 → Prop) : Prop :=
  ∃ row, rateRow (srI a) = some row
    ∧ A1S k e a ra t₀ s (xk0 a row) (P row) ∧ s.regs.get64 .r12 = arg1 t₀
    ∧ s.regs.get64 .r15 = arg0 t₀

/-- The `stop_dk` part (`bs_stop_freq < 14`): `ac` and `sbr` saved in the frame. -/
def SD (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : St → List UInt8 → Prop) : Prop :=
  ∃ row, rateRow (srI a) = some row ∧ u8 a.sp 1 ≤ 13
    ∧ A1S k e a ra t₀ s (xk0 a row)
      (fun st fr => frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ P st fr)

/-- The unrolled `stop_dk` sum (`L1555` .. `L15fb`): `r12 = sbr`, `r15 = ac`,
`rax = bs_stop_freq`; `k[2]` is scratch. -/
def SumS (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  SD k e a ra t₀ s (fun _ _ => True) ∧ s.regs.get64 .r12 = arg1 t₀
  ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 a.sp 1)

/-- `k[2]` clamped (`≤ 64`) and stored, `rsi = k[2]`. -/
def K2S (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ row k2, rateRow (srI a) = some row ∧ k2 ≤ 64
    ∧ A1S k e a ra t₀ s (xk0 a row) (fun st _ => st.k2 = BitVec.ofNat 32 k2)
    ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀
    ∧ s.regs.get64 .rsi = BitVec.ofNat 64 k2

/-- **The interface A1 → A2 at `L1684`**: `k[0]`, `k[2]` stored and checked as `Master`
requires; `rsi = k[2]`, `r13 = k[0]`, `rcx = k[2] - k[0]`. -/
def AtMaster (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ∃ (row k2 : Nat), rateRow (srI a) = some row ∧ k2 ≤ 64 ∧ k0N a row ≤ k2
    ∧ (k2 : Int) - k0A a row ≤ maxQ (srI a)
    ∧ A1S k e a ra t₀ s (xk0 a row) (fun st _ => st.k2 = BitVec.ofNat 32 k2)
    ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀
    ∧ s.regs.get64 .rsi = BitVec.ofNat 64 k2 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (k0N a row)
    ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (k2 - k0N a row)

/-- `n_master` for `bs_freq_scale = 0`: `((k[2] - k[0] + (dk & 2)) >> dk) << 1`,
`dk = bs_alter_scale + 1`. -/
def nmOf (d alter : Nat) : Nat := if alter = 0 then 2 * (d / 2) else 2 * ((d + 2) / 4)

/-- `k2diff = k[2] - k[0] - n_master * dk`. -/
abbrev diffOf (k0 k2 nm dk : Nat) : Int := (k2 : Int) - k0 - nm * dk

/-- The steps `f_master[i]`, `1 ≤ i ≤ n_master`, after the `k2diff` correction. -/
def stepOf (dk nm : Nat) (diff : Int) (i : Nat) : Int :=
  dk - (if diff < 0 ∧ i = 1 then 1 else 0) - (if diff < -1 ∧ i = 2 then 1 else 0)
    + (if 0 < diff ∧ i = nm then 1 else 0)

/-- `f_master[j]` after the prefix sums. -/
def fvOf (k0 dk nm : Nat) (diff : Int) : Nat → Int
  | 0 => k0
  | j + 1 => fvOf k0 dk nm diff j + stepOf dk nm diff (j + 1)

/-- `f_master[1 .. j)` hold `dk`. -/
def Filled (fm : List UInt8) (dk j : Nat) : Prop := ∀ i, 1 ≤ i → i < j → u16 fm i = dk

/-- `f_master[1 ..= nm]` hold the steps. -/
def Stepped (fm : List UInt8) (dk nm : Nat) (diff : Int) : Prop :=
  ∀ i, 1 ≤ i → i ≤ nm → (u16 fm i : Int) = stepOf dk nm diff i

/-- The prefix sums done up to `j`. -/
def Summed (fm : List UInt8) (k0 dk nm : Nat) (diff : Int) (j : Nat) : Prop :=
  (∀ i, i ≤ j → (u16 fm i : Int) = fvOf k0 dk nm diff i)
  ∧ ∀ i, j < i → i ≤ nm → (u16 fm i : Int) = stepOf dk nm diff i

/-- The `int16` broadcast of `v` (`vmovd` + `vpshufb` with `.LCPI5_4`). -/
def bc16 (v : Nat) : BitVec 128 :=
  let w := BitVec.ofNat 16 v
  w ++ w ++ w ++ w ++ w ++ w ++ w ++ w

/-- `bs_freq_scale = 0`: `k[0]`, `k[2]` checked; `P k0 k2 nm dk st fr` on the rest
(`nm = n_master`, `dk = bs_alter_scale + 1`). -/
def F0 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : Nat → Nat → Nat → Nat → St → List UInt8 → Prop) : Prop :=
  ∃ (row k2 : Nat), rateRow (srI a) = some row ∧ k2 ≤ 64 ∧ k0N a row ≤ k2
    ∧ (k2 : Int) - k0A a row ≤ maxQ (srI a) ∧ u8 a.sp 3 = 0
    ∧ A1S k e a ra t₀ s (xk0 a row) (fun st fr => st.k2 = BitVec.ofNat 32 k2
        ∧ P (k0N a row) k2 (nmOf (k2 - k0N a row) (u8 a.sp 4)) (u8 a.sp 4 + 1) st fr)
    ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀

/-- `n_master` stored and checked (`2 ≤ nm`, `bs_xover_band < nm`), `rdx = nm`. -/
abbrev F0b (s : MachineData) (nm : Nat) (st : St) (a : RArgs) : Prop :=
  2 ≤ nm ∧ u8 a.sp 2 < nm ∧ st.nm = BitVec.ofNat 32 nm ∧ s.regs.get64 .rdx = BitVec.ofNat 64 nm

/-- `F0b` and `rsi = k[2]`, `r13 = k[0]`, `rax = dk`, `rcx = nm` (the fill loops). -/
abbrev F0n (s : MachineData) (k0 k2 nm dk : Nat) (st : St) (a : RArgs) : Prop :=
  F0b s nm st a ∧ s.regs.get64 .rsi = BitVec.ofNat 64 k2 ∧ s.regs.get64 .r13 = BitVec.ofNat 64 k0
  ∧ s.regs.get64 .rax = BitVec.ofNat 64 dk ∧ s.regs.get64 .rcx = BitVec.ofNat 64 nm

/-- `xmm0` holds the `int16` broadcast of `dk`. -/
abbrev Xbc (s : MachineData) (dk : Nat) : Prop :=
  (s.zmms.get (AvxReg.xmm .mm0)).setWidth 128 = bc16 dk
"""

# The rate dispatch: path facts on the rate.
RDF = {
    "L10d9": "0xf9ff < srI a",
    "L10fe": "0x7cff < srI a ∧ srI a ≤ 0xf9ff",
    "L10b8": "srI a ≤ 0x7cff ∧ srI a ≠ 16000",
    "L1127": "0x1f3ff < srI a",
    "L111e": "rateRow (srI a) = some 4",
    "L1143": "rateRow (srI a) = some 5",
    "L17fc": "rateRow (srI a) = some 0",
    "L1814": "rateRow (srI a) = some 1",
    "L1808": "rateRow (srI a) = some 3",
    "L1820": "rateRow (srI a) = none",
}

ENTRIES = {
    "L1086": "Pro 2 k e a ra t₀ s",
    "L108a": "Pro 4 k e a ra t₀ s",
    "L114a": "RD k e a ra t₀ s ∧ ∃ row, rateRow (srI a) = some row ∧ s.regs.get64 .rdi = offLab row",
    "L1179": "RD k e a ra t₀ s ∧ (∃ row, rateRow (srI a) = some row ∧ s.regs.get64 .rdi = offLab row) "
             "∧ s.regs.get64 .rax = BitVec.ofNat 64 (tmpOf a.x.sampleRate.toNat * 128 + a.x.sampleRate.toNat / 2) "
             "∧ s.regs.get64 .rsi = BitVec.ofNat 64 (tmpOf a.x.sampleRate.toNat) "
             "∧ s.regs.get64 .r8 = BitVec.ofNat 64 (a.x.sampleRate.toNat / 2)",
    # after the `div`: rax = (temp * 128 + sr / 2) / sr
    "L117d": "RD k e a ra t₀ s ∧ (∃ row, rateRow (srI a) = some row ∧ s.regs.get64 .rdi = offLab row) "
               "∧ s.regs.get64 .rax = BitVec.ofNat 64 ((tmpOf a.x.sampleRate.toNat * 128 "
               "+ a.x.sampleRate.toNat / 2) / a.x.sampleRate.toNat) "
               "∧ s.regs.get64 .rsi = BitVec.ofNat 64 (tmpOf a.x.sampleRate.toNat) "
               "∧ s.regs.get64 .r8 = BitVec.ofNat 64 (a.x.sampleRate.toNat / 2)",
    # k[0] stored
    "L118e": "K0S k e a ra t₀ s (fun row _ _ => s.regs.get64 .rdx = BitVec.ofNat 64 (k0N a row) "
               "∧ s.regs.get64 .rcx = a.x.sampleRate.setWidth 64)",
    # bs_stop_freq >= 14
    "L150a": "K0S k e a ra t₀ s (fun row _ _ => 13 < u8 a.sp 1 "
             "∧ s.regs.get64 .rax = BitVec.ofNat 64 (u8 a.sp 1) "
             "∧ s.regs.get64 .rdx = BitVec.ofNat 64 (k0N a row))",
    "L161f": "K0S k e a ra t₀ s (fun row _ _ => s.regs.get64 .rdx = BitVec.ofNat 64 (k0N a row))",
    "L1762": "AtFail k e a ra t₀ s",
    # bs_stop_freq < 14: stop_min, make_bands(stop_dk, stop_min, 64, 13)
    "L11a7": "∃ row, rateRow (srI a) = some row ∧ u8 a.sp 1 ≤ 13 "
             "∧ A1S k e a ra t₀ s (xk0 a row) (fun _ fr => frSlot64 fr 0x40 = arg0 t₀) "
             "∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .rcx = a.x.sampleRate.setWidth 64",
    "L11ad": "∃ row, rateRow (srI a) = some row ∧ u8 a.sp 1 ≤ 13 "
               "∧ A1S k e a ra t₀ s (xk0 a row) (fun _ fr => frSlot64 fr 0x40 = arg0 t₀) "
               "∧ s.regs.get64 .r12 = arg1 t₀",
    "L11bd": "SD k e a ra t₀ s (fun _ _ => True)",
    "L11db": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1211": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1249": "SD k e a ra t₀ s (fun _ _ => True)",
    "L126b": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1278": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1280": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1288": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1292": "SD k e a ra t₀ s (fun _ _ => True)",
    "L129c": "SD k e a ra t₀ s (fun _ _ => True)",
    "L12aa": "SD k e a ra t₀ s (fun _ _ => True) "
             "∧ s.regs.get64 .rax = t₀.regs.get64 .rsp - 0x60#64",
    "L12ba": "SD k e a ra t₀ s (fun _ fr => frSlot64 fr 0x570 = t₀.regs.get64 .rsp - 0x78#64) "
             "∧ s.regs.get64 .rax = t₀.regs.get64 .rsp - 0x60#64",
    # after the AV_QSORT: k[2] = stop_min + sum of the first bs_stop_freq stop_dk
    "L1523": "SD k e a ra t₀ s (fun _ _ => True)",
    "L1555": "SumS k e a ra t₀ s",
    "L157b": "SumS k e a ra t₀ s",
    "L15a1": "SumS k e a ra t₀ s",
    "L15bf": "SumS k e a ra t₀ s",
    "L15dd": "SumS k e a ra t₀ s",
    "L15fb": "SumS k e a ra t₀ s",
    "L1618": "K0S k e a ra t₀ s (fun _ _ _ => True)",
    "L1622": "K0S k e a ra t₀ s (fun _ _ _ => True)",
    # k[2] clamped, the max_qmf_subbands check
    "L1655": "K2S k e a ra t₀ s ∧ s.regs.get64 .rcx = a.x.sampleRate.setWidth 64 "
             "∧ s.regs.get64 .rax = 0x20#64 ∧ 0x7d01 ≤ srI a ∧ srI a ≠ 44100",
    "L1661": "K2S k e a ra t₀ s ∧ s.regs.get64 .rax = BitVec.ofNat 64 (maxQ (srI a)).toNat",
    "L167a": "AtFailLog k e a ra t₀ s",
    "L17e7": "AtFail k e a ra t₀ s",
    # bs_freq_scale = 0
    "L1779": "AtMaster k e a ra t₀ s ∧ u8 a.sp 3 = 0",
    "L17a0": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => 2 ≤ nm ∧ st.nm = BitVec.ofNat 32 nm "
             "∧ s.regs.get64 .rcx = BitVec.ofNat 64 nm ∧ s.regs.get64 .rsi = BitVec.ofNat 64 k2 "
             "∧ s.regs.get64 .r13 = BitVec.ofNat 64 k0 ∧ s.regs.get64 .rax = BitVec.ofNat 64 dk "
             "∧ s.regs.get64 .rdi = a.x.avctx)",
    "L17d6": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a ∧ 8 ≤ nm "
             "∧ s.regs.get64 .rdi = 1#64)",
    "L1e09": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a ∧ 32 ≤ nm)",
    "L1e30": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a ∧ 32 ≤ nm "
             "∧ s.regs.get64 .r8 = BitVec.ofNat 64 (nm / 32 * 32) ∧ Xbc s dk "
             "∧ s.regs.get64 .rdi = BitVec.ofNat 64 (nm / 32 * 32 + 1) "
             "∧ ∃ j, s.regs.get64 .r9 = BitVec.ofNat 64 j ∧ j % 32 = 0 ∧ j < nm / 32 * 32 "
             "∧ Filled st.fm dk (j + 1))",
    "L1e44": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a ∧ 32 ≤ nm "
             "∧ s.regs.get64 .r8 = BitVec.ofNat 64 (nm / 32 * 32) ∧ Xbc s dk "
             "∧ s.regs.get64 .rdi = BitVec.ofNat 64 (nm / 32 * 32 + 1) "
             "∧ ∃ j, s.regs.get64 .r9 = BitVec.ofNat 64 j ∧ j % 32 = 0 ∧ j < nm / 32 * 32 "
             "∧ Filled st.fm dk (j + 17))",
    "L1e6b": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a "
             "∧ ∃ j, s.regs.get64 .r8 = BitVec.ofNat 64 j ∧ j % 8 = 0 ∧ j + 8 ≤ nm "
             "∧ Filled st.fm dk (j + 1))",
    "L1e90": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a "
             "∧ s.regs.get64 .r9 = BitVec.ofNat 64 (nm / 8 * 8) ∧ Xbc s dk "
             "∧ s.regs.get64 .rdi = BitVec.ofNat 64 (nm / 8 * 8 + 1) "
             "∧ ∃ j, s.regs.get64 .r8 = BitVec.ofNat 64 j ∧ j % 8 = 0 ∧ j < nm / 8 * 8 "
             "∧ Filled st.fm dk (j + 1))",
    "L1ea8": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a "
             "∧ ∃ j, s.regs.get64 .rdi = BitVec.ofNat 64 j ∧ 1 ≤ j ∧ j ≤ nm ∧ Filled st.fm dk j)",
    "L1eb0": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a "
             "∧ s.regs.get64 .r8 = BitVec.ofNat 64 (nm + 1) "
             "∧ ∃ j, s.regs.get64 .rdi = BitVec.ofNat 64 j ∧ 1 ≤ j ∧ j ≤ nm ∧ Filled st.fm dk j)",
    "L1ec1": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0n s k0 k2 nm dk st a "
             "∧ Filled st.fm dk (nm + 1))",
    "L1ed8": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ s.regs.get64 .r13 = BitVec.ofNat 64 k0 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 nm "
             "∧ diffOf k0 k2 nm dk < 0 "
             "∧ s.regs.get64 .rsi = (BitVec.ofInt 32 (diffOf k0 k2 nm dk)).setWidth 64 "
             "∧ Filled st.fm dk (nm + 1))",
    "L1f08": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ s.regs.get64 .r13 = BitVec.ofNat 64 k0 ∧ s.regs.get64 .rcx = BitVec.ofNat 64 nm "
             "∧ Stepped st.fm dk nm (diffOf k0 k2 nm dk))",
    "L1f30": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ s.regs.get64 .rcx = BitVec.ofNat 64 (nm / 8 * 8) "
             "∧ ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 j ∧ j % 8 = 0 ∧ j < nm / 8 * 8 "
             "∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) j "
             "∧ (s.regs.get64 .r13).setWidth 16 = BitVec.ofInt 16 (fvOf k0 dk nm (diffOf k0 k2 nm dk) j))",
    "L1f5d": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ s.regs.get64 .rcx = BitVec.ofNat 64 (nm / 8 * 8) "
             "∧ ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 j ∧ j % 8 = 0 ∧ j < nm / 8 * 8 "
             "∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) (j + 2) "
             "∧ (s.regs.get64 .r13).setWidth 16 = BitVec.ofInt 16 (fvOf k0 dk nm (diffOf k0 k2 nm dk) (j + 3)))",
    "L1f81": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ s.regs.get64 .rcx = BitVec.ofNat 64 (nm / 8 * 8) "
             "∧ ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 j ∧ j % 8 = 0 ∧ j < nm / 8 * 8 "
             "∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) (j + 4) "
             "∧ (s.regs.get64 .r13).setWidth 16 = BitVec.ofInt 16 (fvOf k0 dk nm (diffOf k0 k2 nm dk) (j + 5)))",
    "L1fa5": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ s.regs.get64 .rcx = BitVec.ofNat 64 (nm / 8 * 8) "
             "∧ ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 j ∧ j % 8 = 0 ∧ j < nm / 8 * 8 "
             "∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) (j + 6) "
             "∧ (s.regs.get64 .r13).setWidth 16 = BitVec.ofInt 16 (fvOf k0 dk nm (diffOf k0 k2 nm dk) (j + 7)))",
    "L1fd5": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => F0b s nm st a "
             "∧ ∃ j, s.regs.get64 .rax = BitVec.ofNat 64 (j + 1) ∧ j % 8 = 0 ∧ j < nm ∧ nm < j + 8 "
             "∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) j "
             "∧ (s.regs.get64 .r13).setWidth 16 = BitVec.ofInt 16 (fvOf k0 dk nm (diffOf k0 k2 nm dk) j))",
    "L1ff0": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => 2 ≤ nm ∧ u8 a.sp 2 < nm ∧ st.nm = BitVec.ofNat 32 nm "
             "∧ ∃ j i, s.regs.get64 .rax = arg1 t₀ + BitVec.ofNat 64 (0x4c1f0 + 2 * (j + 1)) "
             "∧ j % 8 = 0 ∧ j < nm ∧ nm < j + 8 ∧ i < nm - j "
             "∧ s.regs.get64 .rcx = BitVec.ofNat 64 (2 * (nm - j)) "
             "∧ s.regs.get64 .rdx = BitVec.ofNat 64 (2 * i) "
             "∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) (j + i) "
             "∧ (s.regs.get64 .r13).setWidth 16 = BitVec.ofInt 16 (fvOf k0 dk nm (diffOf k0 k2 nm dk) (j + i)))",
    "L2003": "F0 k e a ra t₀ s (fun k0 k2 nm dk st _ => 2 ≤ nm ∧ u8 a.sp 2 < nm "
             "∧ st.nm = BitVec.ofNat 32 nm ∧ Summed st.fm k0 dk nm (diffOf k0 k2 nm dk) nm)",
}

for lab, f in RDF.items():
  ENTRIES[lab] = f"RD k e a ra t₀ s ∧ {f}"

# Loop variants (inner digits; the rank of the loop is the first digit).
VARS = {
    "L1e30": "[0x10000 - (s.regs.get64 .r9).toNat, 1, 0]",
    "L1e44": "[0x10000 - (s.regs.get64 .r9).toNat, 0, 0]",
    "L1e90": "[0x10000 - (s.regs.get64 .r8).toNat, 0, 0]",
    "L1eb0": "[0x10000 - (s.regs.get64 .rdi).toNat, 0, 0]",
    "L1f30": "[0x10000 - (s.regs.get64 .rax).toNat, 3, 0]",
    "L1f5d": "[0x10000 - (s.regs.get64 .rax).toNat, 2, 0]",
    "L1f81": "[0x10000 - (s.regs.get64 .rax).toNat, 1, 0]",
    "L1fa5": "[0x10000 - (s.regs.get64 .rax).toNat, 0, 0]",
    "L1ff0": "[0x10000 - (s.regs.get64 .rdx).toNat, 0, 0]",
}
