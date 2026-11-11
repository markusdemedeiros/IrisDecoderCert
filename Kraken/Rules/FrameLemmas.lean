import Kraken.MachineWP
import Kraken.Rules.CallFrame

/-!
# Lemmas and tactics for block-by-block proofs of large procedures

Collected from the proof of `sbr_qmf_synthesis` (FFmpeg
`libavcodec/aacsbr_template.c`), where each was found missing; each is stated
once here for the later procedures of the same shape.

* `cltq` (`cdqe`) has a rule (`MachineWP.cltq_spec`).
* Triples: fix the entry state (`MachineWP.Triple.pin`), weaken the normal
  postcondition (`MachineWP.Triple.post_imp`).
* Frames: the procedure's own bytes off the top of its reservation, with the
  slot of a saved `rbp` apart (`Reserve_split_frame`); `Entails` under a
  frame (`Mem.Entails.sep_left`); an 8-byte cell's contents forgotten
  (`Mem.Entails.forget8`); a name `grind` does not unfold for a region the
  block does not touch (`Mem.Hid`).
* `int`↔`Nat` bridges for counters and offsets: a small natural as a 32-bit
  `int` (`BitVec.toInt_ofInt32_natCast`, `BitVec.toNat_ofInt32_natCast`), a
  32-bit difference without overflow (`BitVec.toInt_sub_of_nonneg_le32`),
  `toNat = toInt` and sign extension = zero extension for non-negative values,
  `Int.ofBytes_toBytes_of_lt`, and the `cltq; lea (v,%rax,4)` pointer
  `v + (c - r)` read back as an index (`BitVec.cltq_lea_bridge`).
* `BitVec.setWidth_32_64_32`, `BitVec.sub_sub_eight` (the `rsp - 8 - 8 - …`
  chains of pushes).
* Tactics: `measure_hb "name" tacs` (heartbeats and wall time of `tacs`) and
  `opaque_stores` (stored values become variables).

The `grind` attributes are scoped (`open scoped Kraken.FrameLemmas.Int32Nat`).
-/

open Kraken Kraken.SysV Mem Std.ExtHashMap Std.WP MachineWP

namespace MachineWP

section
variable [CodeEnv] {p : Program} {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- `cltq` (`cdqe`): `rax` becomes the sign extension of `eax`. -/
@[spec] theorem cltq_spec (asz osz : Width) :
    ⦃ fun s => WP.wp p Q E
        { s with regs := s.regs.set64 .rax (((s.regs.get64 .rax).setWidth 32).signExtend 64) } ⦄
      (Directive.instr (.regular asz osz .cltq) :: p) ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
      Reg64s.set_low64, Effects.All]
    simpa [Reg64s.get_low32] using hP)

/-- `cltd` (`cdq`): `edx` becomes the sign of `eax` (all ones or all zeros), the upper half
of `rdx` is cleared. -/
@[spec] theorem cltd_spec (asz osz : Width) :
    ⦃ fun s => WP.wp p Q E { s with regs := (s.regs.set64 .rdx
        ((((s.regs.get64 .rax).setWidth 32).sshiftRight 31).setWidth 64)) } ⦄
      (Directive.instr (.regular asz osz .cltd) :: p) ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.setReg,
      Reg64s.set_low32, Effects.All]
    simpa [Reg64s.get_low32] using hP)

/-- The rule of a cell that falls through only under a side condition `C` (otherwise it traps)
and leaves a value unspecified: the precondition is `C` and the tail's wp whatever the machine
picks. -/
theorem fallthrough_nondet_cond_spec {α : Type} [NondetSupportingType α] {i : Instr}
    {C : MachineData → Prop} {f : MachineData → α → MachineData}
    (hcell : ∀ (s : MachineData) (rng : Std.Rco Int64) (P : MachineState → Prop), C s →
      (∀ v : α, P (f s v, 0)) → (@Directive.interp (_root_.Executable.labels cenv)
        (Directive.instr i) s rng (fun s' => .done (s', 0))
        (fun _ _ => .unimplemented "jump")).All P) :
    ⦃ fun s => C s ∧ ∀ v : α, WP.wp p Q E (f s v) ⦄ (Directive.instr i :: p) ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    exact step_here hseg (Or.inl (hcell s _ _ h.1 (fun v => h.2 v _ hpl')))

/-- `divl %r32`: `edx:eax` divided by `r32`, unsigned; the quotient and remainder are
zero-extended into `rax` and `rdx`, the flags are arbitrary. The divisor must be nonzero and
the quotient must fit in 32 bits (otherwise the instruction raises #DE). -/
@[spec] theorem div32_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let n := ((s.regs.get64 .rdx).setWidth 32).toNat * 2 ^ 32
          + ((s.regs.get64 .rax).setWidth 32).toNat
        let d := ((s.regs.get64 r).setWidth 32).toNat
        (d ≠ 0 ∧ n / d < 2 ^ 32) ∧ ∀ st : StatusFlags, WP.wp p Q E
          { s with
              regs := (s.regs.set64 .rax ((BitVec.ofNat 32 (n / d)).setWidth 64)).set64 .rdx
                ((BitVec.ofNat 32 (n % d)).setWidth 64),
              status := st } ⦄
      (Directive.instr (.regular asz .W32 (.div (.reg (.low r .W32)))) :: p) ⦃ Q; E ⦄ :=
  fallthrough_nondet_cond_spec (fun s rng P hC hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.setReg, Reg64s.get_low32, Reg64s.set_low32, Effects.All]
    simp only [Width.bits, show (Width.W32 == Width.W8) = false from rfl, Bool.false_eq_true,
      ↓reduceIte, Nat.not_le.mpr hC.2, hC.1, false_or, Effects.All]
    exact hP)

/-- `divq %r64`: `rdx:rax` divided by `r64`, unsigned. As `div32_reg_spec`. -/
@[spec] theorem div64_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let n := (s.regs.get64 .rdx).toNat * 2 ^ 64 + (s.regs.get64 .rax).toNat
        let d := (s.regs.get64 r).toNat
        (d ≠ 0 ∧ n / d < 2 ^ 64) ∧ ∀ st : StatusFlags, WP.wp p Q E
          { s with
              regs := (s.regs.set64 .rax (BitVec.ofNat 64 (n / d))).set64 .rdx
                (BitVec.ofNat 64 (n % d)),
              status := st } ⦄
      (Directive.instr (.regular asz .W64 (.div (.reg (.low r .W64)))) :: p) ⦃ Q; E ⦄ :=
  fallthrough_nondet_cond_spec (fun s rng P hC hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All]
    simp only [Width.bits, show (Width.W64 == Width.W8) = false from rfl, Bool.false_eq_true,
      ↓reduceIte, Nat.not_le.mpr hC.2, hC.1, false_or, Effects.All]
    exact hP)

/-- `idivl %r32`: `edx:eax` divided by `r32`, signed, truncating toward zero (`Int.tdiv`,
`Int.tmod`); the quotient and remainder are zero-extended into `rax` and `rdx`, the flags are
arbitrary. The divisor must be nonzero and the quotient must fit in 32 bits (otherwise the
instruction raises #DE; `INT_MIN / -1` is such a case). -/
@[spec] theorem idiv32_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let n := ((s.regs.get64 .rdx).setWidth 32).toInt * 2 ^ 32
          + (((s.regs.get64 .rax).setWidth 32).toNat : Int)
        let d := ((s.regs.get64 r).setWidth 32).toInt
        (d ≠ 0 ∧ -2 ^ 31 ≤ n.tdiv d ∧ n.tdiv d < 2 ^ 31) ∧ ∀ st : StatusFlags, WP.wp p Q E
          { s with
              regs := (s.regs.set64 .rax ((BitVec.ofInt 32 (n.tdiv d)).setWidth 64)).set64 .rdx
                ((BitVec.ofInt 32 (n.tmod d)).setWidth 64),
              status := st } ⦄
      (Directive.instr (.regular asz .W32 (.idiv (.reg (.low r .W32)))) :: p) ⦃ Q; E ⦄ :=
  fallthrough_nondet_cond_spec (fun s rng P hC hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.setReg, Reg64s.get_low32, Reg64s.set_low32, Effects.All]
    simp only [Width.bits, show (Width.W32 == Width.W8) = false from rfl, Bool.false_eq_true,
      ↓reduceIte, Int.not_lt.mpr hC.2.1, Int.not_le.mpr hC.2.2, hC.1, false_or, Effects.All]
    exact hP)

/-- `idivq %r64`: `rdx:rax` divided by `r64`, signed. As `idiv32_reg_spec`. -/
@[spec] theorem idiv64_reg_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let n := (s.regs.get64 .rdx).toInt * 2 ^ 64 + ((s.regs.get64 .rax).toNat : Int)
        let d := (s.regs.get64 r).toInt
        (d ≠ 0 ∧ -2 ^ 63 ≤ n.tdiv d ∧ n.tdiv d < 2 ^ 63) ∧ ∀ st : StatusFlags, WP.wp p Q E
          { s with
              regs := (s.regs.set64 .rax (BitVec.ofInt 64 (n.tdiv d))).set64 .rdx
                (BitVec.ofInt 64 (n.tmod d)),
              status := st } ⦄
      (Directive.instr (.regular asz .W64 (.idiv (.reg (.low r .W64)))) :: p) ⦃ Q; E ⦄ :=
  fallthrough_nondet_cond_spec (fun s rng P hC hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.setReg, Reg64s.get_low64, Reg64s.set_low64, Effects.All]
    simp only [Width.bits, show (Width.W64 == Width.W8) = false from rfl, Bool.false_eq_true,
      ↓reduceIte, Int.not_lt.mpr hC.2.1, Int.not_le.mpr hC.2.2, hC.1, false_or, Effects.All]
    exact hP)

/-- A block from one fixed entry state: the logical variables of a call (the
caller's memory subtrees, which mention the entry state) can then be named
before `vcgen` steps to the call. -/
theorem Triple.pin {P : MachineData → Prop} {c : Program} {Q : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop}
    (h : ∀ s₀, P s₀ → ⦃ fun s => s = s₀ ⦄ c ⦃ Q; E ⦄) : ⦃ P ⦄ c ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => (h s hs).le_wp s rfl

/-- Weaken the normal postcondition of a triple: prove a small `Q'` (say,
"registers unchanged and the same memory shape") and recover `Q` from it. -/
theorem Triple.post_imp {P : MachineData → Prop} {c : Program} {Q Q' : Unit → MachineData → Prop}
    {E : Int64 → MachineData → Prop} (h : ⦃ P ⦄ c ⦃ Q'; E ⦄) (hq : ∀ s, Q' () s → Q () s) :
    ⦃ P ⦄ c ⦃ Q; E ⦄ :=
  Triple.intro fun s hs => by
    have h1 := h.le_wp s hs
    rw [wp_eq] at h1 ⊢
    exact Executable.wp_mono (hq ·) (fun _ _ x => x) h1

end

end MachineWP

/-! ## Frames -/

/-- A procedure's own `f` bytes off the top of a reservation of `f + k`,
split into the 8 bytes at the bottom and the `f - 8` above them (a frame whose
top slots are the saved registers, below the return address). -/
theorem Reserve_split_frame (f k : Nat) (hf : 8 ≤ f) (r : BitVec 64) (hw : f ≤ r.toNat)
    (K : Mem 64 → Prop) :
    Reserve (f + k) r ⋆ K
      = 8 ?@ (r - .ofNat 64 f) ⋆ (Reserve k (r - .ofNat 64 f)
        ⋆ ((f - 8) ?@ (r - .ofNat 64 (f - 8)) ⋆ K)) := by
  rw [Reserve_split f k r hw]
  have e : f = (f - 8) + 8 := by omega
  have := r.isLt
  rw [show (f ?@ (r - BitVec.ofNat 64 f) : Mem 64 → Prop)
      = ((f - 8) + 8) ?@ (r - BitVec.ofNat 64 f) by rw [← e],
    Block.split_at (r - BitVec.ofNat 64 f) ((f - 8) + 8) 8 (by omega) (by omega),
    show r - BitVec.ofNat 64 f + BitVec.ofNat 64 8 = r - BitVec.ofNat 64 (f - 8) by
      rw [e, Nat.add_sub_cancel]; bv_omega,
    show (f - 8) + 8 - 8 = f - 8 by omega]
  ac_rfl

/-- `Entails` under a frame on the left. -/
theorem Mem.Entails.sep_left {A X Y : Mem 64 → Prop} (e : Mem.Entails X Y) :
    Mem.Entails (A ⋆ X) (A ⋆ Y) := by
  intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
  exact ⟨m₁, m₂, hd, hm, h₁, e m₂ h₂⟩

/-- An 8-byte cell holding `v`, its contents forgotten. -/
theorem Mem.Entails.forget8 (a v : BitVec 64) {K K' : Mem 64 → Prop} (e : Mem.Entails K K') :
    Mem.Entails ((Int.toBytes 8 v.toInt =@ a) ⋆ K) (8 ?@ a ⋆ K') :=
  Mem.Entails.forget (Mem.Split.here _ _) e (by simp [Int.toBytes_length]) (by decide)

/-- A region behind a name `grind` does not unfold: a block's memory fact as
the cells it touches in front of one `Hid` atom (the opaque-region recipe). -/
def Mem.Hid (P : Mem 64 → Prop) : Mem 64 → Prop := P

/-! ## `int` ↔ `Nat` -/

/-- A small natural as a signed 32-bit value (an `int` cell, read back). -/
theorem BitVec.toInt_ofInt32_natCast (n : Nat) (h : n < 2 ^ 31) :
    (BitVec.ofInt 32 (n : Int)).toInt = n := by
  have e : BitVec.ofInt 32 (n : Int) = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [e, BitVec.toInt_ofNat', Int.bmod_def]; split <;> omega

theorem BitVec.toNat_ofInt32_natCast (n : Nat) (h : n < 2 ^ 32) :
    (BitVec.ofInt 32 (n : Int)).toNat = n := by
  have e : BitVec.ofInt 32 (n : Int) = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [e, BitVec.toNat_ofNat]; omega

/-- A 32-bit difference of two signed values `0 ≤ b ≤ a` does not overflow. -/
theorem BitVec.toInt_sub_of_nonneg_le32 (a b : BitVec 32) (hb : 0 ≤ b.toInt)
    (hab : b.toInt ≤ a.toInt) : (a - b).toInt = a.toInt - b.toInt := by
  rw [BitVec.toInt_sub, Int.bmod_def]
  have := a.toInt_lt; have := b.toInt_le
  split <;> omega

/-- A non-negative signed value: `toNat = toInt`. -/
theorem BitVec.toNat_eq_toInt_of_nonneg {w : Nat} (x : BitVec w) (h : 0 ≤ x.toInt) :
    (x.toNat : Int) = x.toInt := by
  rw [BitVec.toInt_eq_toNat_cond] at *
  split at * <;> omega

/-- Sign extension of a non-negative signed value is zero extension
(`cltq`/`movslq` on a non-negative `int`). -/
theorem BitVec.signExtend_of_toInt_nonneg {w v : Nat} (x : BitVec w)
    (h : 0 ≤ x.toInt) : x.signExtend v = x.setWidth v := by
  apply BitVec.signExtend_eq_setWidth_of_msb_false
  rw [BitVec.msb_eq_toInt]; simp; omega

/-- An `n`-byte cell holding a value in `[0, 2^(8n))` reads back as the
value. -/
theorem Int.ofBytes_toBytes_of_lt (n : Nat) (v : Int) (h0 : 0 ≤ v) (h : v < 2 ^ (8 * n)) :
    Int.ofBytes (Int.toBytes n v) = v := by
  rw [_root_.ofBytes_toBytes, Int.take, Int.emod_eq_of_lt h0 h]

theorem BitVec.setWidth_32_64_32 (y : BitVec 32) : (y.setWidth 64).setWidth 32 = y := by
  apply BitVec.eq_of_toNat_eq
  have := y.isLt
  simp only [BitVec.toNat_setWidth]; omega

/-- The pointer `v0 + (c - r)` (`int` difference, `cltq`, `lea (v0,%rax,4)`)
read back as an index: `c - r` elements of 4 bytes, for `0 ≤ r ≤ c`. -/
theorem BitVec.cltq_lea_bridge (v0 : BitVec 64) (c r : BitVec 32) (hr0 : 0 ≤ r.toInt)
    (hrc : r.toInt ≤ c.toInt) :
    (((v0 + (((c - r).setWidth 64).setWidth 32).signExtend 64 * 4#64
        - v0).toNat / 4 : Nat) : Int) = (((c - r).setWidth 64).setWidth 32).toInt
    ∧ ((v0 + (((c - r).setWidth 64).setWidth 32).signExtend 64 * 4#64
        - v0).toNat : Int) = 4 * (c.toInt - r.toInt)
    ∧ (v0 + (((c - r).setWidth 64).setWidth 32).signExtend 64 * 4#64
        - v0).toNat = 4 * (c.toInt - r.toInt).toNat := by
  rw [BitVec.setWidth_32_64_32]
  have ht := BitVec.toInt_sub_of_nonneg_le32 c r hr0 hrc
  have hn := BitVec.toNat_eq_toInt_of_nonneg (c - r) (by omega)
  rw [BitVec.signExtend_of_toInt_nonneg _ (by omega),
    show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
  have := (c - r).isLt
  have hm : ((c - r).setWidth 64 * 4#64).toNat = 4 * (c - r).toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth]; simp; omega
  rw [hm]; refine ⟨by omega, by omega, by omega⟩

/-- Two pushes: `rsp - b - 8 = rsp - (b + 8)`, so that `BitVec.reduceAdd`
folds a chain of pushes into one offset. -/
theorem BitVec.sub_sub_eight (a b : BitVec 64) : a - b - 8#64 = a - (b + 8#64) := by bv_omega

-- `open scoped Kraken.FrameLemmas.Int32Nat`: the two `ofInt32_natCast` lemmas.
namespace Kraken.FrameLemmas.Int32Nat
attribute [scoped grind =] BitVec.toInt_ofInt32_natCast BitVec.toNat_ofInt32_natCast
end Kraken.FrameLemmas.Int32Nat

/-! ## Tactics -/

open Lean Elab Tactic in
/-- `measure_hb "name" tacs`: run the tactics and report the heartbeats (in
`maxHeartbeats` units of 1000) and the wall time they took (the per-block
cost of a proof). -/
elab "measure_hb " s:str t:tacticSeq : tactic => do
  let h0 ← IO.getNumHeartbeats
  let t0 ← IO.monoMsNow
  evalTactic t
  let h1 ← IO.getNumHeartbeats
  let t1 ← IO.monoMsNow
  logInfo m!"MEASURE {s.getString}: {(h1 - h0) / 1000} heartbeats(k), {t1 - t0} ms"

open Lean Elab Tactic Meta in
/-- Replace every stored value `v` of a `Mem.storeInt m a n v` in the goal and
the hypotheses by a fresh variable: the values of a vector block are large
`zmms` terms that memory safety never needs. -/
elab "opaque_stores" : tactic => do
  let find (e : Expr) : Option Expr :=
    (e.find? fun t => t.isAppOfArity ``Mem.storeInt 5 && !(t.getArg! 4).isFVar
      && !(t.getArg! 4).hasLooseBVars).map (·.getArg! 4)
  for _ in [0:200] do
    let g ← getMainGoal
    let done ← g.withContext do
      let tgt ← instantiateMVars (← g.getType)
      let mut v? := find tgt
      let mut hs : Array FVarId := #[]
      for d in (← getLCtx) do
        if !d.isImplementationDetail then
          let ty ← instantiateMVars d.type
          if v?.isNone then v? := find ty
          if let some v := v? then
            if (ty.find? (· == v)).isSome then hs := hs.push d.fvarId
      match v? with
      | none => return true
      | some v =>
        let (fs, g1) ← g.revert hs (preserveOrder := true)
        let g2 ← g1.withContext do
          let gs ← g1.generalize #[{ expr := v }]
          pure gs.2
        let (_, g3) ← g2.introNP fs.size
        replaceMainGoal [g3]
        return false
    if done then return
