# Entries of shard B, part `sbr_hf_calc_npatches` (owner: gB, helper of reset): L30df..L320e.
LEMMAS = r"""
/-! ## Shard B: `sbr_hf_calc_npatches` (owner gB) -/

/-- The context of the patch loop: `k[0]`, `n_master`, `n_q`. -/
structure PCx where
  k0 : Int
  nm : Nat
  q : Nat

/-- The values the patch loop starts from (`derived3 ∘ derived2 ∘ derived1`). -/
abbrev px0 (a : RArgs) (c : PCx) (f : Nat → Nat) : Args :=
  derived3 (derived2 (derived1 (x0D a c.k0) c.nm (xoOf a) f) (xoOf a) f) c.q

/-- `k[0]`, `kx[1]`, `kx[1] + m[1]` as the model's loop sees them. -/
abbrev pk0 (c : PCx) : Nat := c.k0.toNat
abbrev pkx (a : RArgs) (f : Nat → Nat) : Nat := f (xoOf a)
abbrev ptop (a : RArgs) (c : PCx) (f : Nat → Nat) : Nat := f (xoOf a) + (f c.nm - f (xoOf a))

/-- The loop's start state (`Patches.run`). -/
abbrev pinit (a : RArgs) (c : PCx) (f : Nat → Nat) (ki : Nat) : PL :=
  { k := ki, lk := -1, msb := pk0 c, lmsb := -1, usb := pkx a f, np := 0,
    pn := mk 6 (old (px0 a c f).pnum), pst := mk 6 (old (px0 a c f).pstart), sb := 0 }

abbrev PR (a : RArgs) (c : PCx) (f : Nat → Nat) : PL → PL → Bool → Prop :=
  PRun f (pk0 c) (pkx a f) c.nm (ptop a c f)

/-- `s` is reached from the start: every run from `s` is a run from the start. -/
def PReach (a : RArgs) (c : PCx) (f : Nat → Nat) (s : PL) : Prop :=
  ∃ ki, KInit f c.nm (ptop a c f) (goalSb a.x.sampleRate.toInt) ki
    ∧ ∀ r b, PR a c f s r b → PR a c f (pinit a c f ki) r b

/-- The fixed facts of the loop: `Derived`'s checks passed, `sbr_make_f_tablelim`'s needs on the
values that the loop does not write. -/
def PFix (a : RArgs) (c : PCx) (f : Nat → Nat) : Prop :=
  Master a.x.sampleRate.toInt (u8 a.sp 0) (xoOf a) (some c.k0) (some (c.nm, f))
  ∧ (derived1 (x0D a c.k0) c.nm (xoOf a) f).kx1 + (derived1 (x0D a c.k0) c.nm (xoOf a) f).m1 ≤ 64
  ∧ (derived1 (x0D a c.k0) c.nm (xoOf a) f).kx1 ≤ 32 ∧ 1 ≤ c.q ∧ c.q ≤ 5
  ∧ TlimIn a { px0 a c f with npatch := 0 } ∧ (px0 a c f).pstart.length = 6

/-- The values while the loop runs in state `s`. -/
abbrev pxs (a : RArgs) (c : PCx) (f : Nat → Nat) (s : PL) : Args :=
  { px0 a c f with npatch := s.np, pnum := s.pn, pstart := s.pst }

/-- The loop invariant at `L312e` (and its variant facts). -/
def PHd (a : RArgs) (c : PCx) (f : Nat → Nat) (s : PL) : Prop :=
  PReach a c f s ∧ PInv (pk0 c) (pkx a f) c.nm (ptop a c f) s
  ∧ ((s.msb : Int) = s.lmsb → s.msb = pkx a f) ∧ (s.msb ≠ s.usb → s.msb ≠ pkx a f → s.lk = -1)
  ∧ -1 ≤ s.lk ∧ s.lk ≤ 48 ∧ -1 ≤ s.lmsb ∧ s.lmsb ≤ 64

/-- Not `k == last_k && msb == last_msb`. -/
abbrev PNr (s : PL) : Prop := ¬ ((s.k : Int) = s.lk ∧ (s.msb : Int) = s.lmsb)

/-- Inside the patch loop: `r12 = sbr` unless said otherwise, the frame slots of the loop. -/
def AtPat (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData)
    (P : St → PCx → Prop) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ ∃ (st : St) (fr : List UInt8) (c : PCx),
    PFix a c (fOf st) ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
    ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
    ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
    ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))
    ∧ P st c ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)

/-- A failure of the patch loop decided (`Derived.badPatch`): the values, `r12 = sbr`. -/
def AtPatF (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s ∧ s.regs.get64 .r12 = arg1 t₀
  ∧ ∃ (st : St) (fr : List UInt8) (c : PCx),
    Master a.x.sampleRate.toInt (u8 a.sp 0) (xoOf a) (some c.k0) (some (c.nm, fOf st))
    ∧ Reset (spOf a) (lbN a) a.x st.x.turnoff ∧ st.x.avctx = a.x.avctx ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)

/-- `num_patches > 5` decided (`L31f5`, from the inner loop): as `AtPatF`, `r12` free. -/
def AtPatG (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  ResetCI a t₀ ∧ Base t₀ s
  ∧ ∃ (st : St) (fr : List UInt8) (c : PCx),
    Master a.x.sampleRate.toInt (u8 a.sp 0) (xoOf a) (some c.k0) (some (c.nm, fOf st))
    ∧ Reset (spOf a) (lbN a) a.x st.x.turnoff ∧ st.x.avctx = a.x.avctx ∧ st.sp = a.sp ∧ st.fm.length = 98 ∧ FrOk fr
    ∧ frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀ ∧ (s.dmem =⋆ Mm k e a ra t₀ st fr)
"""


def R(r, v):
  return f"s.regs.get64 .{r} = {v}"


def R32(r, v):
  return f"(s.regs.get64 .{r}).setWidth 32 = {v}"


F = "(fOf st)"
N64 = lambda v: f"BitVec.ofNat 64 ({v})"
COMMON = (f"{R('rsi', N64('pk0 c'))} ∧ {R('r8', '0#64')}")
HD = (f"PHd a c {F} p ∧ st.x = pxs a c {F} p ∧ {R('r9', N64('p.msb'))} ∧ {R('r10', N64('p.usb'))} "
      f"∧ {R('rcx', N64('p.np'))} ∧ {COMMON}")
NR = f"PHd a c {F} p ∧ PNr p"
INNER = f"Inner {F} (pk0 c) p.msb p.k j"
PB = f"(pbody {F} (pk0 c) (pkx a {F}) c.nm p j)"
REGS0 = (f"{R('r9', N64('p.msb'))} ∧ {R('r10', N64('p.usb'))} ∧ {R('rcx', N64('p.np'))} ∧ {COMMON}")

ENTRIES = {
    # after the goal_sb search: k = ki, num_patches = 0
    "L30df": ("AtPat k e a ra t₀ s (fun st c => KInit (fOf st) c.nm (ptop a c (fOf st)) "
              "(goalSb a.x.sampleRate.toInt) (s.regs.get64 .rdi).toNat "
              f"∧ st.x = {{ px0 a c (fOf st) with npatch := 0 }} "
              f"∧ {R('rsi', N64('pk0 c'))} ∧ {R('r12', 'arg1 t₀')})"),
    # the loop head: last_k in eax, last_msb in r15d
    "L312e": (f"AtPat k e a ra t₀ s (fun st c => ∃ p : PL, {HD} ∧ {R('rdi', N64('p.k'))} "
              f"∧ {R32('rax', 'BitVec.ofInt 32 p.lk')} ∧ {R32('r15', 'BitVec.ofInt 32 p.lmsb')} "
              f"∧ {R('r12', 'arg1 t₀')})"),
    # not a repetition
    "L3141": (f"AtPat k e a ra t₀ s (fun st c => ∃ p : PL, {NR} ∧ st.x = pxs a c {F} p "
              f"∧ {R('rax', N64('p.k'))} ∧ {R('rdi', N64('p.k'))} ∧ {REGS0} ∧ {R('r12', 'arg1 t₀')})"),
    # the inner loop at index i (r12 = i - k)
    "L3160": (f"AtPat k e a ra t₀ s (fun st c => ∃ (p : PL) (i : Nat), {NR} ∧ st.x = pxs a c {F} p "
              f"∧ i ≤ p.k ∧ (∀ i', i < i' → i' ≤ p.k → ((pk0 c : Int) - 1 + p.msb - oddOf (pk0 c) ({F} i')) < {F} i') "
              f"∧ {R('rdi', N64('p.k'))} ∧ {R('rax', N64('p.k'))} ∧ {R32('r14', 'BitVec.ofNat 32 (p.msb + pk0 c)')} "
              f"∧ {R('r15', 'arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * p.k)')} "
              f"∧ {R('r12', 'BitVec.ofNat 64 i - BitVec.ofNat 64 p.k')} ∧ {REGS0})"),
    # the inner loop stopped at j: sb = f j in r11, odd in r13
    "L318c": (f"AtPat k e a ra t₀ s (fun st c => ∃ (p : PL) (j : Nat), {NR} ∧ {INNER} ∧ st.x = pxs a c {F} p "
              f"∧ {R('rdi', N64('p.k'))} ∧ {R('rax', N64('p.k'))} ∧ {R('r11', N64(F + ' j'))} "
              f"∧ {R('r13', N64('oddOf (pk0 c) (' + F + ' j)'))} ∧ {REGS0})"),
    # patch_num_subbands[np] stored
    "L31b5": (f"AtPat k e a ra t₀ s (fun st c => ∃ (p : PL) (j : Nat), {NR} ∧ {INNER} ∧ p.np ≤ 5 "
              f"∧ st.x = {{ pxs a c {F} p with pnum := {PB}.pn }} "
              f"∧ {R('rdi', N64('p.k'))} ∧ {R('rax', N64('p.k'))} ∧ {R('r11', N64(F + ' j'))} "
              f"∧ {R('r14', N64(F + ' j - p.usb'))} ∧ {R('r15', N64(F + ' j - p.usb + oddOf (pk0 c) (' + F + ' j)'))} "
              f"∧ {R('r12', N64('pk0 c'))} ∧ {R('rbx', N64('p.np'))} ∧ {R('rdx', 'arg1 t₀')} ∧ {REGS0})"),
    # a nonempty patch: num_patches++
    "L30f8": (f"AtPat k e a ra t₀ s (fun st c => ∃ (p : PL) (j : Nat), {NR} ∧ {INNER} ∧ p.np ≤ 5 "
              f"∧ 0 < {F} j - p.usb ∧ st.x = {{ pxs a c {F} p with pnum := {PB}.pn, pstart := {PB}.pst }} "
              f"∧ {R('rdi', N64('p.k'))} ∧ {R('rax', N64('p.k'))} ∧ {R('r11', N64(F + ' j'))} "
              f"∧ {R('r12', 'arg1 t₀')} ∧ {REGS0})"),
    # the pass done except k: msb' in r14, usb' in r10, np' in ecx
    "L3108": (f"AtPat k e a ra t₀ s (fun st c => ∃ (p : PL) (j : Nat), {NR} ∧ {INNER} ∧ p.np ≤ 5 "
              f"∧ st.x = pxs a c {F} {PB} "
              f"∧ {R('rdi', N64('p.k'))} ∧ {R('rax', N64('p.k'))} ∧ {R('r11', N64(F + ' j'))} "
              f"∧ {R('r9', N64('p.msb'))} ∧ {R('r14', N64(PB + '.msb'))} ∧ {R('r10', N64(PB + '.usb'))} "
              f"∧ {R('rcx', N64(PB + '.np'))} ∧ {COMMON} ∧ {R('r12', 'arg1 t₀')})"),
    # the last pass ended normally (sb = kx[1] + m[1])
    "L320e": (f"AtPat k e a ra t₀ s (fun st c => ∃ (ki : Nat) (r : PL), "
              f"KInit {F} c.nm (ptop a c {F}) (goalSb a.x.sampleRate.toInt) ki "
              f"∧ PR a c {F} (pinit a c {F} ki) r true ∧ PInv (pk0 c) (pkx a {F}) c.nm (ptop a c {F}) r "
              f"∧ st.x = pxs a c {F} r ∧ {R('rcx', N64('r.np'))} ∧ {R('r12', 'arg1 t₀')})"),
    # the two returns of the loop (repetition, num_patches > 5)
    "L31d5": "AtPatF k e a ra t₀ s",
    "L31eb": "AtFailLog k e a ra t₀ s",
    "L31f0": "AtFail k e a ra t₀ s",
    "L31f5": "AtPatG k e a ra t₀ s",
}

_NP = "(s.regs.get64 .rcx).toNat"
_K = "(s.regs.get64 .rdi).toNat"
_MSB = "(s.regs.get64 .r9).toNat"
_USB = "(s.regs.get64 .r10).toNat"
_KX = "(slot32 s 0x80).toNat"
_W = (f"(2 + (if {_MSB} = {_USB} then 1 else 0) + (if {_MSB} ≠ {_USB} ∧ {_MSB} ≠ {_KX} then 2 else 0))")
_Y = ("((if (s.regs.get64 .rax).setWidth 32 ≠ (s.regs.get64 .rdi).setWidth 32 then 2 else 0) "
      "+ (if (s.regs.get64 .r9).setWidth 32 ≠ (s.regs.get64 .r15).setWidth 32 then 2 else 0) "
      f"+ (if {_MSB} = {_USB} then 1 else 0))")
_Z = lambda t: f"8 * (48 - {_K}) + {t}"
_P3108 = ("(if s.regs.get64 .r14 = s.regs.get64 .r10 ∧ s.regs.get64 .r10 = s.regs.get64 .r11 "
          f"∧ s.regs.get64 .r9 ≠ s.regs.get64 .r10 then 3 else {_W} - 1)")

VARS = {
    "L312e": f"[6 - {_NP}, {_Z(_Y)}, 49]",
    "L3141": f"[6 - {_NP}, {_Z(_W)}, 49]",
    "L3160": f"[6 - {_NP}, {_Z(_W)}, ((s.regs.get64 .rdi + s.regs.get64 .r12).setWidth 32).toNat]",
    "L318c": f"[6 - {_NP}, {_Z(_W)}, 0]",
    "L31b5": f"[6 - {_NP}, {_Z(_W)}, 0]",
    "L30f8": f"[5 - {_NP}, 1000, 49]",
    "L3108": f"[6 - {_NP}, {_Z(_P3108)}, 49]",
}
