
LEMMAS = r"""
/-! ## Shard B: `sbr_make_f_derived` -/

/-- `bs_xover_band`. -/
abbrev xoOf (a : RArgs) : Nat := u8 a.sp 2

/-- The decoder values after `sbr_make_f_master` stored `k[0]`. -/
abbrev x0D (a : RArgs) (k0 : Int) : Args := { a.x with k0 := k0.toNat }

/-- `derived1`'s stores, one at a time (`n[1]`, `n[0]`, `f_tablehigh`, `m[1]`; then `kx[1]`). -/
abbrev d1a (x : Args) (nm xo : Nat) : Args := { x with n1 := nm - xo }
abbrev d1b (x : Args) (nm xo : Nat) : Args := { d1a x nm xo with n0 := (nm - xo + 1) / 2 }
abbrev d1c (x : Args) (nm xo : Nat) (f : Nat → Nat) : Args :=
  { d1b x nm xo with ftHigh := mk16 49 (fun i => if i ≤ nm - xo then f (xo + i) else u16 x.ftHigh i) }
abbrev d1d (x : Args) (nm xo : Nat) (f : Nat → Nat) : Args :=
  { d1c x nm xo f with m1 := f nm - f xo }

/-- Inside `sbr_make_f_derived`: `Master` succeeded with `n_master = nm`, `f_master = fOf st`
(not written again), `ac` in the frame slot `rbp - 0x40`; `P` the progress. -/
def AtDer (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : St → List UInt8 → Nat → Int → Prop) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ ∃ (st : St) (fr : List UInt8) (nm : Nat) (k0 : Int),
    Master a.x.sampleRate.toInt (u8 a.sp 0) (u8 a.sp 2) (some k0) (some (nm, fOf st))
    ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr ∧ frSlot64 fr 0x40 = arg0 t₀
    ∧ P st fr nm k0 ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)
/-- After `sbr_hf_calc_npatches` succeeded: what `Derived.ok` asks before
`sbr_make_f_tablelim`, the current values being `y` (the patches' result). -/
def TailOk (a : RArgs) (y : Args) : Prop :=
  ∃ (k0 : Int) (nm : Nat) (f : Nat → Nat) (q : Nat),
    Master a.x.sampleRate.toInt (u8 a.sp 0) (xoOf a) (some k0) (some (nm, f))
    ∧ (derived1 (x0D a k0) nm (xoOf a) f).kx1 + (derived1 (x0D a k0) nm (xoOf a) f).m1 ≤ 64
    ∧ (derived1 (x0D a k0) nm (xoOf a) f).kx1 ≤ 32 ∧ 1 ≤ q ∧ q ≤ 5
    ∧ Patches f a.x.sampleRate.toInt (x0D a k0).k0 (f (xoOf a)) (f nm - f (xoOf a)) nm
        (derived3 (derived2 (derived1 (x0D a k0) nm (xoOf a) f) (xoOf a) f) q) y true

/-- `sbr_make_f_tablelim`'s requirements on the values (`TlimC` without the address bound). -/
def TlimIn (a : RArgs) (y : Args) : Prop :=
  y.n0 ≤ 24 ∧ y.npatch ≤ 6 ∧ (0 < a.lb.toNat → 1 ≤ y.n0 + y.npatch)
  ∧ y.ftLow.length = 50 ∧ y.ftLim.length = 60 ∧ y.pnum.length = 6
  ∧ TabIn y.ftLow y.n0 y.kx1 (y.kx1 + y.m1) ∧ psum y.pnum y.npatch ≤ y.m1 ∧ y.kx1 + y.m1 ≤ 64
  ∧ y.nlim < 2 ^ 32

/-- `sbr_make_f_derived` returned `0` with the values `z`. -/
def DerOk (a : RArgs) (z : Args) : Prop :=
  ∃ (k0 : Int) (nm : Nat) (f : Nat → Nat),
    Master a.x.sampleRate.toInt (u8 a.sp 0) (xoOf a) (some k0) (some (nm, f))
    ∧ Derived a.x.sampleRate.toInt a.lb.toNat nm (xoOf a) f (x0D a k0) z true

/-- The success tail (`L3228`, `L3230`): `r12 = sbr`, `P` the progress. -/
def AtTail (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) (P : St → Prop) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ s.regs.get64 .r12 = arg1 t₀
  ∧ ∃ (st : St) (fr : List UInt8), P st ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)
/-- `derived1` then `derived2` (`f_tablelow` copied). -/
abbrev dD2 (a : RArgs) (k0 : Int) (nm : Nat) (f : Nat → Nat) : Args :=
  derived2 (derived1 (x0D a k0) nm (xoOf a) f) (xoOf a) f

/-- The `n_q` part (from `L2b30`): derived1's checks passed, `f_tablelow` copied, the frame slots
`rbp - 0x30` (`sbr`), `rbp - 0x38` (`n_master`); `P` the progress. -/
def AtNq (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : St → List UInt8 → Nat → Int → Prop) : Prop :=
  AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ (fOf st) nm ≤ 64 ∧ (fOf st) (xoOf a) ≤ 32
    ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ P st fr nm k0)
"""
# Entries of shard B (owner: reset): sbr_make_f_derived, sbr_hf_calc_npatches, the
# sbr_make_f_tablelim call, sbr_turnoff and the failure paths.
ENTRIES = {
    # the error logs (every failure ends at L1d31); `AtFailLog`: rdi = avctx
    "L1cf4": "AtFail k e a ra t₀ s",
    "L1cff": "AtFailLog k e a ra t₀ s",
    "L1d0b": "AtFail k e a ra t₀ s",
    "L1d0d": "AtFail k e a ra t₀ s ∧ s.regs.get64 .rdi = a.x.avctx",
    "L1d1b": "AtFail k e a ra t₀ s ∧ s.regs.get64 .rdi = a.x.avctx",
    "L1d2a": "AtFailLog k e a ra t₀ s",
    "L1d48": "AtFailLog k e a ra t₀ s ∧ s.regs.get64 .rbx = arg1 t₀ + 0x1c#64",
    # sbr_turnoff
    "L1d4d": "AtOff 0 k e a ra t₀ s",
    "L1d5f": "AtOff 1 k e a ra t₀ s",
    "L1d71": "AtOff 2 k e a ra t₀ s",
    "L1d89": "AtOff 2 k e a ra t₀ s",
    # sbr_make_f_derived: derived1
    "L2032": "AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ st.x = d1a (x0D a k0) nm (xoOf a) ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (nm - (xoOf a) + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (nm - (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ s.regs.get64 .rax = BitVec.ofNat 64 ((xoOf a)))",
    "L2059": "AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ st.x = d1b (x0D a k0) nm (xoOf a) ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (nm - (xoOf a) + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (nm - (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ s.regs.get64 .rdi = arg1 t₀ + 0x4c284#64 ∧ s.regs.get64 .rsi = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (xoOf a)) ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (2 * (nm - (xoOf a) + 1)))",
    "L205e": "AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ st.x = d1c (x0D a k0) nm (xoOf a) (fOf st) ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (nm - (xoOf a) + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (nm - (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2))",
    "L208b": "AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ st.x = d1d (x0D a k0) nm (xoOf a) (fOf st) ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (nm - (xoOf a) + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (nm - (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((fOf st) nm) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 ((fOf st) (xoOf a)))",
    "L20aa": "AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ st.x = derived1 (x0D a k0) nm (xoOf a) (fOf st) ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (nm - (xoOf a) + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (nm - (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((fOf st) nm) ∧ (fOf st) nm ≤ 64)",
    "L20c8": "AtDer k e a ra t₀ s (fun st fr nm k0 => ((st.x = derived1 (x0D a k0) nm (xoOf a) (fOf st) ∧ (64 < (fOf st) nm ∨ ((fOf st) nm ≤ 64 ∧ 32 < (fOf st) (xoOf a)))) ∨ Reset (spOf a) (lbN a) a.x st.x.turnoff) ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .rdi = a.x.avctx)",
    "L20cf": "AtDer k e a ra t₀ s (fun st fr nm k0 => ((st.x = derived1 (x0D a k0) nm (xoOf a) (fOf st) ∧ (64 < (fOf st) nm ∨ ((fOf st) nm ≤ 64 ∧ 32 < (fOf st) (xoOf a)))) ∨ Reset (spOf a) (lbN a) a.x st.x.turnoff) ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀)",
    "L20d8": "AtDer k e a ra t₀ s (fun st fr nm k0 => NqIn e st ∧ st.x = derived1 (x0D a k0) nm (xoOf a) (fOf st) ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 nm ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ s.regs.get64 .r12 = BitVec.ofNat 64 (nm - (xoOf a) + 1) ∧ s.regs.get64 .r13 = BitVec.ofNat 64 (nm - (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ (fOf st) nm ≤ 64 ∧ (fOf st) (xoOf a) ≤ 32 ∧ s.regs.get64 .r10 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((fOf st) nm))",
    # n_q (log2f), the badNq failure
    "L2b30": "AtNq k e a ra t₀ s (fun st fr nm k0 => st.x = dD2 a k0 nm (fOf st) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ s.regs.get64 .r10 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .rcx = BitVec.ofNat 64 ((fOf st) nm))",
    "L2b45": "AtNq k e a ra t₀ s (fun st fr nm k0 => st.x = dD2 a k0 nm (fOf st) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 ((fOf st) (xoOf a)) ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 ((fOf st) nm) ∧ lo32 s .mm0 = A2.fl (u8 a.sp 5)) ∧ s.regs.get64 .r12 = arg1 t₀",
    "L2b60": "AtNq k e a ra t₀ s (fun st fr nm k0 => st.x = dD2 a k0 nm (fOf st) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 ((fOf st) (xoOf a)) ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 ((fOf st) nm) ∧ frSlot32 fr 0x48 = A2.fl (u8 a.sp 5) ∧ lo32 s .mm0 = BitVec.f32div (A2.fl st.k2.toNat) (A2.fl ((fOf st) (xoOf a)))) ∧ s.regs.get64 .r12 = arg1 t₀",
    "L2b65": "AtNq k e a ra t₀ s (fun st fr nm k0 => st.x = dD2 a k0 nm (fOf st) ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2) ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 ((fOf st) (xoOf a)) ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 ((fOf st) nm) ∧ frSlot32 fr 0x48 = A2.fl (u8 a.sp 5) ∧ lo32 s .mm0 = e.lg (BitVec.f32div (A2.fl st.k2.toNat) (A2.fl ((fOf st) (xoOf a))))) ∧ s.regs.get64 .r12 = arg1 t₀",
    "L2b9d": "AtNq k e a ra t₀ s (fun st fr nm k0 => ∃ q : Nat, 5 < q ∧ st.x = { dD2 a k0 nm (fOf st) with nq := q }) ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .rdi = a.x.avctx",
    "L2ba4": "AtNq k e a ra t₀ s (fun st fr nm k0 => ∃ q : Nat, 5 < q ∧ st.x = { dD2 a k0 nm (fOf st) with nq := q }) ∧ s.regs.get64 .r12 = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀",
    "L2bb5": "AtNq k e a ra t₀ s (fun st fr nm k0 => frSlot32 fr 0x80 = BitVec.ofNat 32 ((fOf st) (xoOf a)) ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 ((fOf st) nm) ∧ ∃ q : Nat, 1 ≤ q ∧ q < 6 ∧ st.x = { dD2 a k0 nm (fOf st) with nq := q } ∧ BitVec.setWidth 32 (s.regs.get64 .rcx) = BitVec.ofNat 32 q ∧ s.regs.get64 .r14 = BitVec.ofNat 64 ((fOf st) (xoOf a)) ∧ s.regs.get64 .r15 = BitVec.ofNat 64 ((nm - (xoOf a) + 1) / 2)) ∧ s.regs.get64 .r12 = arg1 t₀",
    # the success tail: sbr_make_f_tablelim, f_indexnoise = 0
    "L3228": "AtTail k e a ra t₀ s (fun st => TailOk a st.x ∧ TlimIn a st.x)",
    "L3230": "AtTail k e a ra t₀ s (fun st => DerOk a { st.x with d0 := clrNoise st.x.d0, d1 := clrNoise st.x.d1 })",
}
