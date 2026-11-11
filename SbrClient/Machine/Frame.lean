import SbrClient.Machine.Execution
import Kraken.SeparationMem

/-! Spatial locality of Kraken's actual instruction interpreter. -/

open Std Std.ExtHashMap Kraken

namespace SbrClient

def Disjoint (m f : Mem 64) : Prop := m.inter f = ∅

def frame (s : MachineData) (f : Mem 64) : MachineData :=
  { s with dmem := s.dmem.union f }

theorem get_union_of_disjoint {m f : Mem 64} (hd : Disjoint m f)
    {a : BitVec 64} {b : UInt8} (h : m[a]? = some b) :
    (m.union f)[a]? = some b := by
  rw [union_comm_of_disjoint m f hd]
  simp only [union_eq, getElem?_union, h, Option.some_or]

theorem loadBytes_frame {m f : Mem 64} (hd : Disjoint m f)
    {a : BitVec 64} {n : Nat} {bs : List UInt8}
    (h : m.loadBytes a n = some bs) : Mem.loadBytes (m.union f) a n = some bs := by
  have hs : ∀ i ∈ List.range n, (m.get? (a + .ofNat 64 i)).isSome = true := by
    have := congrArg Option.isSome h
    simpa only [Mem.loadBytes, Option.isSome_some, List.krakenAllSome_isSome_iff, List.forall_mem_map] using this
  unfold Mem.loadBytes at h ⊢
  have he : (List.range n).map (fun i => (m.union f).get? (a + .ofNat 64 i)) =
      (List.range n).map (fun i => m.get? (a + .ofNat 64 i)) := by
    apply List.map_congr_left
    intro i hi
    have hx := hs i hi
    cases hv : m.get? (a + .ofNat 64 i) with
    | none => simp only [hv, Option.isSome_none, Bool.false_eq_true] at hx
    | some b =>
      rw [get?_eq_getElem?] at hv ⊢
      exact get_union_of_disjoint hd hv
  rw [he]
  exact h

theorem loadInt_frame {m f : Mem 64} (hd : Disjoint m f)
    {a : BitVec 64} {n : Nat} {v : Int}
    (h : m.loadInt a n = some v) : Mem.loadInt (m.union f) a n = some v := by
  unfold Mem.loadInt at h ⊢
  cases hb : m.loadBytes a n with
  | none => simp [hb] at h
  | some bs => rw [loadBytes_frame hd hb]; simpa [hb] using h

theorem storeInt_disjoint {m f : Mem 64} (hd : Disjoint m f)
    {a : BitVec 64} {n : Nat} {old : Int}
    (h : m.loadInt a n = some old) (v : Int) :
    Disjoint (m.storeInt a n v) f := by
  have hs : ∀ i ∈ List.range n, (m.get? (a + .ofNat 64 i)).isSome = true := by
    have := congrArg Option.isSome h
    simpa only [Mem.loadInt, Option.isSome_map, Mem.loadBytes,
      Option.isSome_some, List.krakenAllSome_isSome_iff, List.forall_mem_map] using this
  apply eq_empty_iff_forall_not_mem.mpr
  intro k hk
  have ⟨hm, hf⟩ := mem_inter_iff.mp hk
  have hm' : k ∈ m := by
    simp only [Mem.storeInt, Mem.storeBytes, union_eq, mem_union_iff] at hm
    rcases hm with hm | hm
    · exact hm
    · obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hm
      rw [Int.toBytes_length] at hi
      have := hs i (List.mem_range.mpr hi)
      simpa only [get?_eq_getElem?, isSome_getElem?_iff_mem] using this
  have hx : k ∈ m.inter f := mem_inter_iff.mpr ⟨hm', hf⟩
  rw [show m.inter f = ∅ from hd] at hx
  exact not_mem_empty hx

theorem storeInt_frame {m f : Mem 64} (hd : Disjoint m f)
    {a : BitVec 64} {n : Nat} {old : Int}
    (h : m.loadInt a n = some old) (v : Int) :
    Mem.storeInt (m.union f) a n v = (m.storeInt a n v).union f := by
  have hd' := storeInt_disjoint hd h v
  apply ExtHashMap.ext_getElem?
  intro k
  have hf : (m.storeInt a n v)[k]?.isSome = true → f[k]? = none := by
    intro hm
    apply getElem?_eq_none
    intro hx
    have hm' : k ∈ m.storeInt a n v := isSome_getElem?_iff_mem.mp hm
    have hx' : k ∈ (m.storeInt a n v).inter f := mem_inter_iff.mpr ⟨hm', hx⟩
    rw [show (m.storeInt a n v).inter f = ∅ from hd'] at hx'
    exact not_mem_empty hx'
  simp only [Mem.storeInt, Mem.storeBytes, union_eq, getElem?_union] at hf ⊢
  cases hx : ((Int.toBytes n v).At a)[k]? with
  | none => simp only [hx, Option.none_or]
  | some b =>
    have := hf (by simp [hx])
    simp [hx, this]


/-- The instruction keeps exactly the mapped addresses of its input. -/
def SameDomain (m m' : Mem 64) : Prop := ∀ k, k ∈ m' ↔ k ∈ m

theorem storeInt_sameDomain {m : Mem 64} {a : BitVec 64} {n : Nat} {old : Int}
    (h : m.loadInt a n = some old) (v : Int) : SameDomain m (m.storeInt a n v) := by
  have hs : ∀ i ∈ List.range n, (m.get? (a + .ofNat 64 i)).isSome = true := by
    have := congrArg Option.isSome h
    simpa only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, Option.isSome_some,
      List.krakenAllSome_isSome_iff, List.forall_mem_map] using this
  intro k
  simp only [Mem.storeInt, Mem.storeBytes, union_eq, mem_union_iff]
  constructor
  · rintro (hm | hm)
    · exact hm
    · obtain ⟨i, hi, rfl⟩ := (mem_At_iff _ _ _).mp hm
      rw [Int.toBytes_length] at hi
      have := hs i (List.mem_range.mpr hi)
      simpa only [get?_eq_getElem?, isSome_getElem?_iff_mem] using this
  · exact Or.inl

private def Stable (m₀ f m : Mem 64) : Prop := SameDomain m₀ m ∧ Disjoint m f

private theorem stable_store {m₀ m f : Mem 64} (hd : Stable m₀ f m)
    {a : BitVec 64} {n : Nat} {old : Int} (h : m.loadInt a n = some old) (v : Int) :
    Stable m₀ f (m.storeInt a n v) :=
  ⟨fun k => (storeInt_sameDomain h v k).trans (hd.1 k), storeInt_disjoint hd.2 h v⟩

section Transport
variable {P Q : MachineState → Prop} {f m₀ : Mem 64}

private theorem load_frame {s : MachineData} {addr : BitVec 64} {w : Width}
    {r₁ r₂ : w.type → MachineData → Effects} (hd : Stable m₀ f s.dmem)
    (hk : ∀ v s', Stable m₀ f s'.dmem → (r₁ v s').All P → (r₂ v (frame s' f)).All Q)
    (h : (s.load addr w r₁).All P) : ((frame s f).load addr w r₂).All Q := by
  unfold MachineData.load at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes with
  | none => simp only [hm, Effects.All] at h
  | some v =>
    have hm' := loadInt_frame hd.2 hm
    change Mem.loadInt (frame s f).dmem addr w.bytes = some v at hm'
    rw [hm']
    exact hk _ _ hd (by simpa only [hm] using h)

private theorem store_frame {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects} (hd : Stable m₀ f s.dmem)
    (hk : ∀ s', Stable m₀ f s'.dmem → (r₁ s').All P → (r₂ (frame s' f)).All Q)
    (h : (s.store addr v r₁).All P) : ((frame s f).store addr v r₂).All Q := by
  unfold MachineData.store at h ⊢
  simp only [Effects.All] at h ⊢
  cases hm : Mem.loadInt s.dmem addr w.bytes with
  | none => simp only [hm, Effects.All] at h
  | some old =>
    have hm' := loadInt_frame hd.2 hm
    change Mem.loadInt (frame s f).dmem addr w.bytes = some old at hm'
    rw [hm']
    have hr := hk _ (stable_store hd hm v.toInt) (by simpa only [hm] using h)
    simpa only [frame, storeInt_frame hd.2 hm] using hr

private theorem regOrMem_frame [Labels] [AddressSize] {w} {o : RegOrMem w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ v s', Stable m₀ f s'.dmem → (r₁ v s').All P → (r₂ v (frame s' f)).All Q)
    (h : (o.interp s p r₁).All P) : (o.interp (frame s f) p r₂).All Q := by
  cases o with
  | reg r => exact hk _ _ hd h
  | mem a => exact load_frame hd hk h

private theorem operand_frame [Labels] [AddressSize] {w} {o : Operand w}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : w.type → MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ v s', Stable m₀ f s'.dmem → (r₁ v s').All P → (r₂ v (frame s' f)).All Q)
    (h : (o.interp s p r₁).All P) : (o.interp (frame s f) p r₂).All Q := by
  cases o with
  | regOrMem rm => exact regOrMem_frame hd hk h
  | imm v => exact hk _ _ hd h

private theorem relRegOrMem_frame [Labels] [AddressSize] {o : RelRegOrMem}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : BitVec 64 → MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ v s', Stable m₀ f s'.dmem → (r₁ v s').All P → (r₂ v (frame s' f)).All Q)
    (h : (o.interp s p r₁).All P) : (o.interp (frame s f) p r₂).All Q := by
  cases o with
  | rel c => exact hk _ _ hd h
  | reg r => exact hk _ _ hd h
  | mem a => exact load_frame hd hk h

private theorem set_frame [Labels] [AddressSize] {w} {d : Dst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ s', Stable m₀ f s'.dmem → (r₁ s').All P → (r₂ (frame s' f)).All Q)
    (h : (s.set d v p r₁).All P) : ((frame s f).set d v p r₂).All Q := by
  cases d with
  | reg r => exact hk (s.setReg r v) hd h
  | mem a => exact store_frame hd hk h

private theorem interpLow_frame [Labels] [AddressSize] {o : AvxRegOrMem .W128} {n : Width}
    {s : MachineData} {p : Std.Rco Int64} {r₁ r₂ : n.type → MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ v s', Stable m₀ f s'.dmem → (r₁ v s').All P → (r₂ v (frame s' f)).All Q)
    (h : (o.interpLow n s p r₁).All P) : (o.interpLow n (frame s f) p r₂).All Q := by
  cases o with
  | avx r => exact hk _ _ hd h
  | mem a => exact load_frame hd hk h

private theorem avxRead_frame [Labels] [AddressSize] {w} {o : AvxRegOrMem w}
    {s : MachineData} {p : Std.Rco Int64} {K₁ K₂ : w.type → MachineData → Prop} {b : Bool}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ v s', Stable m₀ f s'.dmem → K₁ v s' → K₂ v (frame s' f))
    (h : o.wpRead s p b K₁) : o.wpRead (frame s f) p b K₂ := by
  cases o with
  | avx r => exact hk _ _ hd h
  | mem a =>
    obtain ⟨hal, i, hi, hp⟩ := h
    exact ⟨hal, i, loadInt_frame hd.2 hi, hk _ _ hd hp⟩

private theorem avxWrite_frame [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type}
    {s : MachineData} {p : Std.Rco Int64} {legacy b : Bool} {K₁ K₂ : MachineData → Prop}
    (hd : Stable m₀ f s.dmem)
    (hk : ∀ s', Stable m₀ f s'.dmem → K₁ s' → K₂ (frame s' f))
    (h : d.wpWrite v s p legacy b K₁) : d.wpWrite v (frame s f) p legacy b K₂ := by
  cases d with
  | avx r =>
    unfold AvxDst.wpWrite at h ⊢
    cases legacy with
    | false => exact hk (s.setAvxReg r v) hd h
    | true => exact hk (s.setAvxLegacyReg r v) hd h
  | mem a =>
    obtain ⟨hal, i, hi, hp⟩ := h
    refine ⟨hal, i, loadInt_frame hd.2 hi, ?_⟩
    have hr := hk _ (stable_store hd hi v.toInt) hp
    simpa only [frame, storeInt_frame hd.2 hi] using hr


@[simp] theorem frame_regs (s : MachineData) (f : Mem 64) : (frame s f).regs = s.regs := rfl
@[simp] theorem frame_zmms (s : MachineData) (f : Mem 64) : (frame s f).zmms = s.zmms := rfl
@[simp] theorem frame_status (s : MachineData) (f : Mem 64) : (frame s f).status = s.status := rfl

theorem shift_frame [Labels] (c : ShiftCountExpr) (s : MachineData) (f : Mem 64)
    (p : Std.Rco Int64) (w : Width) : c.interpMasked (frame s f) p w = c.interpMasked s p w := by
  cases c <;> rfl

set_option allowUnsafeReducibility true in
attribute [local irreducible] RegOrMem.interp Operand.interp RelRegOrMem.interp
  AvxRegOrMem.interp AvxRegOrMem.interpLow MachineData.set MachineData.setAvx MachineData.setAvxLegacy
  MachineData.load MachineData.store MachineData.loadAvx MachineData.storeAvx

private theorem operation_frame {w} [Labels] [AddressSize]
    {op : Operation w} {p : Std.Rco Int64} {s : MachineData}
    {n₁ n₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hn : ∀ s', Stable m₀ f s'.dmem → (n₁ s').All P → (n₂ (frame s' f)).All Q)
    (hj : ∀ pc s', Stable m₀ f s'.dmem → (j₁ pc s').All P → (j₂ pc (frame s' f)).All Q)
    (h : (Operation.interp op p s n₁ j₁).All P) :
    (Operation.interp op p (frame s f) n₂ j₂).All Q := by
  cases op <;>
    simp only [Operation.interp, Reg.interp, Effects.All, frame_regs, frame_zmms,
      frame_status, shift_frame] at h ⊢ <;>
    repeat' first
      | (apply hn _ _ h; exact hd)
      | (apply hj _ _ _ h; exact hd)
      | exact h.elim
      | refine operand_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
      | refine regOrMem_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
      | refine relRegOrMem_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
      | refine set_frame (h := h) (by exact hd) (fun s' hd h => ?_)
      | refine load_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
      | refine store_frame (h := h) (by exact hd) (fun s' hd h => ?_)
      | (intro v; specialize h v)
      | (split <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, ite_true, ite_false] at h ⊢)
      | (split at h <;> rename_i hcond <;>
          simp only [hcond, Bool.false_eq_true, ite_true, ite_false])
      | simp only [Effects.All, frame_regs, frame_zmms, frame_status, shift_frame] at h ⊢
      | simp only [] at h ⊢
      | cases w


private theorem directive_frame [Labels] {d : Directive} {p : Std.Rco Int64}
    {s : MachineData} {n₁ n₂ : MachineData → Effects} {j₁ j₂ : Int64 → MachineData → Effects}
    (hd : Stable m₀ f s.dmem)
    (hn : ∀ s', Stable m₀ f s'.dmem → (n₁ s').All P → (n₂ (frame s' f)).All Q)
    (hj : ∀ pc s', Stable m₀ f s'.dmem → (j₁ pc s').All P → (j₂ pc (frame s' f)).All Q)
    (h : (d.interp s p n₁ j₁).All P) :
    (d.interp (frame s f) p n₂ j₂).All Q := by
  cases d with
  | label l => exact hn _ hd h
  | byteArray bs => cases h
  | instr i =>
    simp only [Directive.interp, Instr.interp, Effects.All] at h ⊢
    cases i with
    | regular asz osz op =>
      letI : AddressSize := .mk asz
      exact operation_frame hd hn hj h
    | avx asz osz aop =>
      simp only [Instr.interp, Effects.All] at h ⊢
      generalize (AddressSize.mk asz : AddressSize) = A at h ⊢
      cases aop <;>
        simp only [AvxOperation.interp, All_avxRegOrMem, All_setAvx,
          All_setAvxLegacy, Effects.All, frame_regs, frame_zmms, frame_status] at h ⊢ <;>
        repeat' first
          | (apply hn _ _ h; exact hd)
          | exact h.elim
          | refine avxRead_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
          | refine avxWrite_frame (h := h) (by exact hd) (fun s' hd h => ?_)
          | refine load_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
          | refine store_frame (h := h) (by exact hd) (fun s' hd h => ?_)
          | refine set_frame (h := h) (by exact hd) (fun s' hd h => ?_)
          | refine regOrMem_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
          | refine interpLow_frame (h := h) (by exact hd) (fun v s' hd h => ?_)
          | (split at h <;> try simp only [Effects.All] at h ⊢)
          | simp only [frame_regs, frame_zmms, frame_status] at h ⊢
          | simp only [] at h ⊢

end Transport

/-- One real instruction on a larger heap reproduces a small instruction,
leaves the arbitrary disjoint frame unchanged, and preserves the exact domain
of the owned heap. The statement covers all nondeterministic outcomes. -/
theorem instruction_frame {e : Kraken.Executable Directive} {s : MachineState}
    {f : Mem 64} {P : MachineState → Prop} (hd : Disjoint s.1.dmem f)
    (h : (instruction e s).All P) :
    (instruction e (frame s.1 f, s.2)).All (fun st => ∃ t : MachineState,
      st = (frame t.1 f, t.2) ∧ SameDomain s.1.dmem t.1.dmem ∧ Disjoint t.1.dmem f ∧ P t) := by
  letI : Labels := _root_.Executable.labels e
  unfold instruction at h ⊢
  cases hc : e.codeAt s.2 with
  | nil => simp only [hc, Effects.All] at h
  | cons c rest =>
    obtain ⟨d, z⟩ := c
    simp only [hc] at h ⊢
    apply directive_frame (d := d) (p := .mk s.2 (s.2 + .ofNat z))
      (s := s.1) (P := P) (m₀ := s.1.dmem)
      (n₁ := fun t => .done (t, s.2 + .ofNat z))
      (j₁ := fun pc t => .done (t, pc))
      (n₂ := fun t => .done (t, s.2 + .ofNat z))
      (j₂ := fun pc t => .done (t, pc))
      ⟨fun _ => Iff.rfl, hd⟩ _ _ h
    · intro t ht hp
      change P (t, s.2 + Int64.ofNat z) at hp
      exact ⟨(t, s.2 + Int64.ofNat z), rfl, ht.1, ht.2, hp⟩
    · intro pc t ht hp
      exact ⟨(t, pc), rfl, ht.1, ht.2, hp⟩

/-- The small-step framing result consumed by concurrent program logic. -/
theorem instrOutcome_frame {e : Kraken.Executable Directive} {s : MachineState}
    {f : Mem 64} {P : MachineState → Prop} (hd : Disjoint s.1.dmem f)
    (h : e.instrStep s P) {r : Option MachineState}
    (hr : InstrOutcome e (frame s.1 f, s.2) r) :
    ∃ t : MachineState, r = some (frame t.1 f, t.2) ∧
      SameDomain s.1.dmem t.1.dmem ∧ Disjoint t.1.dmem f ∧ P t := by
  obtain ⟨st, rfl, t, rfl, hdom, hdis, hp⟩ := hr.of_all (instruction_frame hd (instrStep_all h))
  exact ⟨t, rfl, hdom, hdis, hp⟩

end SbrClient
