import Kraken.X64.Examples.Sbr.Parse.Lib
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# Procedures that may abort

Some parser routines reach `abort()` from the bitstream (`av_assert0`), so their spec cannot be a
plain `ProcSpec` (a run that reaches the return address). `ProcSpecA` is the same with a second
outcome: the run reaches the entry of `abort`. Nothing is assumed about `abort` itself.

* `ProcSpecA entry Pre Post`: every run from `Pre` reaches the return address with `Post`, or
  `abort`'s entry.
* `ProcSpec.toA`: a `ProcSpec` is a `ProcSpecA`.
* `call_procA_spec_at`: a `call` of a `ProcSpecA` callee, for `vcgen`: the caller's continuation
  after the return, and its exit channel at `abort`'s entry.
* `call_abort_at`: `call abort` itself, an exit at `abort`'s entry.
* `ProcSpecA.of_cfg_post`: `ProcSpec.of_cfg_post` with the blocks' exits the return (`Post'`) or
  `abort`'s entry.
* `ProcSpecS stops`: the same with any set of safe stop addresses (`abort`'s entry, a trap
  instruction); `ProcSpecA = ProcSpecS (· = abortA)` (`ProcSpecA.iff_S`).
-/

open Kraken MachineWP Std.WP Lean.Order Mem

namespace Kraken.Examples.Sbr.Parse

variable [CodeEnv]

/-- A run entered at `entry` in a state `t` with `Pre x ra t` reaches `ra` in a state `s'` with
`Post x ra t s'`, or reaches the entry of `abort`. -/
def ProcSpecA (entry : Int64) {α : Type} (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually cenv.instrStep (fun st => (st.2 = ra ∧ Post x ra t st.1) ∨ st.2 = abortA) (t, entry)

theorem ProcSpec.toA {entry : Int64} {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (h : cenv.ProcSpec entry Pre Post) :
    ProcSpecA entry Pre Post :=
  fun x ra t hp => eventually_weaken _ _ _ _ (fun _ hs => Or.inl hs) (h x ra t hp)

theorem ProcSpecA.mono {entry : Int64} {α : Type} {Pre Pre' : α → Int64 → MachineData → Prop}
    {Post Post' : α → Int64 → MachineData → MachineData → Prop} (h : ProcSpecA entry Pre Post)
    (hpre : ∀ x ra t, Pre' x ra t → Pre x ra t)
    (hpost : ∀ x ra t s, Pre' x ra t → Post x ra t s → Post' x ra t s) :
    ProcSpecA entry Pre' Post' :=
  fun x ra t hp => eventually_weaken _ _ _ _
    (fun _ hs => hs.imp (fun ⟨h1, h2⟩ => ⟨h1, hpost _ _ _ _ hp h2⟩) id) (h x ra t (hpre _ _ _ hp))

/-- Stepping a `call` of a callee that may abort: as `call_proc_spec`, and the caller's exit
channel accepts `abort`'s entry in any state. -/
theorem call_procA_spec {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} {p : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} (x : α) (asz osz : Width)
    (l : Label) (hproc : ProcSpecA ((_root_.Executable.labels cenv).label l) Pre Post) :
    ⦃ fun s =>
        (∀ ra : Int64, Pre x ra (s.pushRa ra)
          ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
        ∧ (∀ s' : MachineData, E abortA s')
        ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes).isSome = true ⦄
      (Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  obtain ⟨hP, hE, hmapped⟩ := h
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z + ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label l := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hv, Effects.All, hcancel]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.pushRa (pc + Int64.ofNat z)) (hP _).1) ?_
  rintro ⟨s', a⟩ (⟨rfl, hpost⟩ | habort)
  · rw [after_instr hseg]
    exact (hP _).2 s' hpost _ hpl'
  · dsimp only at habort
    subst habort
    exact Eventually.done _ (Or.inr (hE s'))

/-- `call_procA_spec` with the widths, the tail and the channels open, for `vcgen [hc]`. -/
theorem call_procA_spec_at {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (l : Label)
    (hproc : ProcSpecA ((_root_.Executable.labels cenv).label l) Pre Post) :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          (∀ ra : Int64, Pre x ra (s.pushRa ra)
            ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
          ∧ (∀ s' : MachineData, E abortA s')
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
      ⦃ Q; E ⦄ :=
  fun asz osz _ _ _ => call_procA_spec x asz osz l hproc

/-- `call abort`: an exit at `abort`'s entry (no spec of `abort` is used). -/
theorem call_abort_at :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s => (∀ s' : MachineData, E abortA s')
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label "abort") .after_current_instruction)))) :: p)
      ⦃ Q; E ⦄ := by
  intro asz osz p Q E
  refine Triple.intro fun s h => ?_
  obtain ⟨hE, hmapped⟩ := h
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z + ((_root_.Executable.labels cenv).label "abort" - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label "abort" := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hv, Effects.All, hcancel]
  exact Eventually.done _ (Or.inr (hE _))

/-- A procedure that may abort, from its blocks: `ProcSpec.of_cfg_post` with every block's exit
either the return (`a = ra ∧ Post' x ra t₀ s`) or `abort`'s entry. -/
theorem ProcSpecA.of_cfg_post {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ ((a = ra ∧ Post' x ra t₀ s) ∨ a = abortA) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    ProcSpecA ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach (T x ra t) var
    (fun a s => (a = ra ∧ Post' x ra t s) ∨ a = abortA) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_weaken _ _ _ _
    (fun st hst => hst.imp (fun ⟨h1, h2⟩ => ⟨h1, hpost x ra t st.1 h2⟩) id) h

/-! ## Safe stops

`ProcSpecS stops` generalizes `ProcSpecA`: a run reaches the return address with `Post`, or an
address in `stops` (any address the run may stop at without a fault in the model's sense, e.g.
`abort`'s entry or a compiler-inserted trap instruction). `ProcSpecA` is `ProcSpecS (· = abortA)`
(`ProcSpecA.iff_S`, by `Iff.rfl`).

* `call_procS_spec(_at)`: a `call` of a `ProcSpecS stops` callee; the caller's exit channel must
  accept every callee stop.
* `ProcSpecS.of_cfg_post`: the blocks' exits the return (`Post'`) or a stop.
-/

/-- A run entered at `entry` in a state `t` with `Pre x ra t` reaches `ra` in a state `s'` with
`Post x ra t s'`, or reaches an address in `stops`. -/
def ProcSpecS (stops : Int64 → Prop) (entry : Int64) {α : Type}
    (Pre : α → Int64 → MachineData → Prop)
    (Post : α → Int64 → MachineData → MachineData → Prop) : Prop :=
  ∀ (x : α) (ra : Int64) (t : MachineData), Pre x ra t →
    Eventually cenv.instrStep (fun st => (st.2 = ra ∧ Post x ra t st.1) ∨ stops st.2) (t, entry)

theorem ProcSpecA.iff_S {entry : Int64} {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} :
    ProcSpecA entry Pre Post ↔ ProcSpecS (· = abortA) entry Pre Post := Iff.rfl

theorem ProcSpecA.toS {entry : Int64} {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (h : ProcSpecA entry Pre Post) :
    ProcSpecS (· = abortA) entry Pre Post := h

theorem ProcSpecS.toA {entry : Int64} {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ProcSpecS (· = abortA) entry Pre Post) : ProcSpecA entry Pre Post := h

theorem ProcSpec.toS {entry : Int64} {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (stops : Int64 → Prop)
    (h : cenv.ProcSpec entry Pre Post) : ProcSpecS stops entry Pre Post :=
  fun x ra t hp => eventually_weaken _ _ _ _ (fun _ hs => Or.inl hs) (h x ra t hp)

/-- More stops, a weaker precondition, a weaker postcondition. -/
theorem ProcSpecS.mono {stops stops' : Int64 → Prop} {entry : Int64} {α : Type}
    {Pre Pre' : α → Int64 → MachineData → Prop}
    {Post Post' : α → Int64 → MachineData → MachineData → Prop}
    (h : ProcSpecS stops entry Pre Post) (hst : ∀ a, stops a → stops' a)
    (hpre : ∀ x ra t, Pre' x ra t → Pre x ra t)
    (hpost : ∀ x ra t s, Pre' x ra t → Post x ra t s → Post' x ra t s) :
    ProcSpecS stops' entry Pre' Post' :=
  fun x ra t hp => eventually_weaken _ _ _ _
    (fun _ hs => hs.imp (fun ⟨h1, h2⟩ => ⟨h1, hpost _ _ _ _ hp h2⟩) (hst _))
    (h x ra t (hpre _ _ _ hp))

/-- A `ProcSpecA` callee in a caller with more stops. -/
theorem ProcSpecA.toS_of {stops : Int64 → Prop} (hab : stops abortA) {entry : Int64} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ProcSpecA entry Pre Post) : ProcSpecS stops entry Pre Post :=
  ProcSpecS.mono h.toS (fun _ ha => ha ▸ hab) (fun _ _ _ hp => hp) (fun _ _ _ _ _ hq => hq)

/-- Stepping a `call` of a callee with stops: as `call_proc_spec`, and the caller's exit
channel accepts every callee stop in any state. -/
theorem call_procS_spec {stops : Int64 → Prop} {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} {p : Program}
    {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} (x : α) (asz osz : Width)
    (l : Label) (hproc : ProcSpecS stops ((_root_.Executable.labels cenv).label l) Pre Post) :
    ⦃ fun s =>
        (∀ ra : Int64, Pre x ra (s.pushRa ra)
          ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
        ∧ (∀ a, stops a → ∀ s' : MachineData, E a s')
        ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
             Width.W64.bytes).isSome = true ⦄
      (Directive.instr (.regular asz osz
          (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  obtain ⟨hP, hE, hmapped⟩ := h
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hmapped
  have hcancel : Int64.ofBitVec
      (pc + Int64.ofNat z + ((_root_.Executable.labels cenv).label l - (pc + Int64.ofNat z))).toBitVec
      = (_root_.Executable.labels cenv).label l := by
    rw [Int64.ofBitVec_toBitVec]
    apply Int64.toBitVec_inj.mp
    simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  refine step_cps _ _ _ ⟨_, _, _, hseg, Or.inr ?_⟩
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
    ConstExpr.interp, MachineData.store, hv, Effects.All, hcancel]
  refine eventually_trans _ _ _ _
    (hproc x (pc + Int64.ofNat z) (s.pushRa (pc + Int64.ofNat z)) (hP _).1) ?_
  rintro ⟨s', a⟩ (⟨rfl, hpost⟩ | hstop)
  · rw [after_instr hseg]
    exact (hP _).2 s' hpost _ hpl'
  · exact Eventually.done _ (Or.inr (hE a hstop s'))

/-- `call_procS_spec` with the widths, the tail and the channels open, for `vcgen [hc]`. -/
theorem call_procS_spec_at {stops : Int64 → Prop} {α : Type}
    {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop} (x : α) (l : Label)
    (hproc : ProcSpecS stops ((_root_.Executable.labels cenv).label l) Pre Post) :
    ∀ ⦃asz osz : Width⦄ ⦃p : Program⦄ ⦃Q : Unit → MachineData → Prop⦄
      ⦃E : Int64 → MachineData → Prop⦄,
      ⦃ fun s =>
          (∀ ra : Int64, Pre x ra (s.pushRa ra)
            ∧ ∀ s' : MachineData, Post x ra (s.pushRa ra) s' → WP.wp p Q E s')
          ∧ (∀ a, stops a → ∀ s' : MachineData, E a s')
          ∧ (Mem.loadInt s.dmem (s.regs.get64 .rsp - Width.W64.bytesv)
               Width.W64.bytes).isSome = true ⦄
        (Directive.instr (.regular asz osz
            (.call (.rel (.sub (.label l) .after_current_instruction)))) :: p)
      ⦃ Q; E ⦄ :=
  fun asz osz _ _ _ => call_procS_spec x asz osz l hproc

/-- A procedure with stops, from its blocks: `ProcSpec.of_cfg_post` with every block's exit
either the return (`a = ra ∧ Post' x ra t₀ s`) or a stop. -/
theorem ProcSpecS.of_cfg_post {stops : Int64 → Prop} {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ ((a = ra ∧ Post' x ra t₀ s) ∨ stops a) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    ProcSpecS stops ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach (T x ra t) var
    (fun a s => (a = ra ∧ Post' x ra t s) ∨ stops a) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_weaken _ _ _ _
    (fun st hst => hst.imp (fun ⟨h1, h2⟩ => ⟨h1, hpost x ra t st.1 h2⟩) id) h

/-! ## The precondition at the exit

`of_cfg_postP`: as `of_cfg_post`, with `hpost` also given the precondition at the entry state
(for its stack headroom, `CallPre.le`: rebuilding the caller's reservation from the frame needs
the frame below `rsp` not to wrap). -/

/-- `ProcSpec.of_cfg_post` with the precondition in hand at the exit. -/
theorem ProcSpec.of_cfg_postP {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ (a = ra ∧ Post' x ra t₀ s) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Pre x ra t₀ → Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label l₀) Pre Post :=
  Kraken.Executable.ProcSpec.of_cfg_post_pre T Post' var (fun x ra t₀ _ => hblocks x ra t₀) hpre
    hpost hp hwf hpl

/-- `ProcSpecS.of_cfg_post` with the precondition in hand at the exit. -/
theorem ProcSpecS.of_cfg_postP {stops : Int64 → Prop} {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ ((a = ra ∧ Post' x ra t₀ s) ∨ stops a) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Pre x ra t₀ → Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    ProcSpecS stops ((_root_.Executable.labels cenv).label l₀) Pre Post := by
  intro x ra t ht
  have h := MachineWP.cfg_reach (T x ra t) var
    (fun a s => (a = ra ∧ Post' x ra t s) ∨ stops a) (hblocks x ra t) hp hwf hpl t
    (hpre x ra t ht)
  exact eventually_weaken _ _ _ _
    (fun st hst => hst.imp (fun ⟨h1, h2⟩ => ⟨h1, hpost x ra t st.1 ht h2⟩) id) h

/-- `ProcSpecA.of_cfg_post` with the precondition in hand at the exit. -/
theorem ProcSpecA.of_cfg_postP {p p' : Program} {l₀ : Label}
    {α : Type} {Pre : α → Int64 → MachineData → Prop}
    {Post : α → Int64 → MachineData → MachineData → Prop}
    (T : α → Int64 → MachineData → Label → MachineData → Prop)
    (Post' : α → Int64 → MachineData → MachineData → Prop)
    (var : Label → MachineData → Nat := fun _ _ => 0)
    (hblocks : ∀ (x : α) (ra : Int64) (t₀ : MachineData) l blk,
      Program.blockAt p l = some blk → ∀ n : Nat,
      ⦃ fun s => T x ra t₀ l s ∧ var l s = n ⦄ blk.body
      ⦃ (match blk.next with
         | some l' => fun _ s => T x ra t₀ l' s ∧ var l' s ≤ n
         | none => fun _ _ => False);
        fun a s => Table.ofLabels (fun l' s => (Program.blockAt p l').isSome ∧ T x ra t₀ l' s
          ∧ Program.EdgeLt p var l n l' s) a s ∨ ((a = ra ∧ Post' x ra t₀ s) ∨ a = abortA) ⦄)
    (hpre : ∀ x ra t, Pre x ra t → T x ra t l₀ t)
    (hpost : ∀ x ra t₀ s, Pre x ra t₀ → Post' x ra t₀ s → Post x ra t₀ s)
    (hp : p = Directive.label l₀ :: p' := by rfl)
    (hwf : Program.WF p := by decide)
    (hpl : Program.PlacedIn p := by assumption) :
    ProcSpecA ((_root_.Executable.labels cenv).label l₀) Pre Post :=
  ProcSpecS.of_cfg_postP (stops := (· = abortA)) T Post' var hblocks hpre hpost hp hwf hpl

end Kraken.Examples.Sbr.Parse
