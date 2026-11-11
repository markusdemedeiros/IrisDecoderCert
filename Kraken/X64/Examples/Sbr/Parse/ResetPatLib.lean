import Kraken.X64.Examples.Sbr.Parse.ResetDer
import Kraken.X64.Examples.Sbr.Parse.ResetA2Lib

/-!
# `sbr_reset`: the patch loop `sbr_hf_calc_npatches`, pure facts (shard B, gB)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false

namespace Kraken.Examples.Sbr.Reset

theorem rsB_master_f0 {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat}
    (h : Master sr st xo (some k0) (some (nm, f))) : (f 0 : Int) = k0 := by
  cases h with
  | ok k2 _ _ hr h64 hk hq hxo hf0 hinc hfn => exact hf0

/-- The numeric facts of `PFix`. -/
theorem rsB_fix {a : RArgs} {c : PCx} {f : Nat → Nat} (h : PFix a c f) :
    pk0 c = f 0 ∧ f 0 ≤ pkx a f ∧ pkx a f ≤ 32 ∧ ptop a c f = f c.nm ∧ pkx a f ≤ f c.nm
    ∧ f c.nm ≤ 64 ∧ c.nm ≤ 48 ∧ xoOf a < c.nm
    ∧ (∀ i j, i ≤ j → j ≤ c.nm → f i + (j - i) ≤ f j) := by
  obtain ⟨hM, h64, h32, -⟩ := h
  have h0 := rsB_master_f0 hM
  obtain ⟨hxo, hnm, hfn, hmono⟩ := master_bounds hM
  have hx := hmono 0 (xoOf a) (Nat.zero_le _) (Nat.le_of_lt hxo)
  have hxn := hmono (xoOf a) c.nm (Nat.le_of_lt hxo) (Nat.le_refl _)
  have e1 : (derived1 (x0D a c.k0) c.nm (xoOf a) f).kx1 = f (xoOf a) := rfl
  rw [e1] at h32
  refine ⟨?_, by simp only [pkx]; omega, h32, by simp only [ptop]; omega, by simp only [pkx]; omega,
    hfn, hnm, hxo, hmono⟩
  simp only [pk0]; omega

theorem rsB_hf {a : RArgs} {c : PCx} {f : Nat → Nat} (h : PFix a c f) :
    ∀ i, i ≤ c.nm → f i ≤ ptop a c f := by
  obtain ⟨-, -, -, et, -, -, -, -, hmono⟩ := rsB_fix h
  intro i hi; have := hmono i c.nm hi (Nat.le_refl _); omega

theorem rsB_reach_init {a : RArgs} {c : PCx} {f : Nat → Nat} {ki : Nat}
    (hk : KInit f c.nm (ptop a c f) (goalSb a.x.sampleRate.toInt) ki) :
    PReach a c f (pinit a c f ki) := ⟨ki, hk, fun _ _ h => h⟩

theorem rsB_reach_step {a : RArgs} {c : PCx} {f : Nat → Nat} {s : PL} {j : Nat}
    (h : PReach a c f s) (hnr : PNr s) (hj : Inner f (pk0 c) s.msb s.k j) (hnp : s.np ≤ 5)
    (ht : f j ≠ ptop a c f) : PReach a c f (pbody f (pk0 c) (pkx a f) c.nm s j) :=
  let ⟨ki, hk, hr⟩ := h
  ⟨ki, hk, fun r b hrun => hr r b (PRun.cont s j hnr hj hnp ht hrun)⟩

theorem rsB_hd_init {a : RArgs} {c : PCx} {f : Nat → Nat} {ki : Nat} (hF : PFix a c f)
    (hk : KInit f c.nm (ptop a c f) (goalSb a.x.sampleRate.toInt) ki) :
    PHd a c f (pinit a c f ki) := by
  obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, hxo, hmono⟩ := rsB_fix hF
  have hki : ki ≤ c.nm := by
    unfold KInit at hk; split at hk
    · exact hk.1
    · omega
  refine ⟨rsB_reach_init hk, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, mk_length _ _, mk_length _ _, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [pinit] <;> try omega
  all_goals first | exact Or.inl trivial | (simp [psum]; done) | (intros; trivial)

theorem rsB_hd_step {a : RArgs} {c : PCx} {f : Nat → Nat} {s : PL} {j : Nat} (hF : PFix a c f)
    (h : PHd a c f s) (hnr : PNr s) (hj : Inner f (pk0 c) s.msb s.k j) (hnp : s.np ≤ 5)
    (ht : f j ≠ ptop a c f) : PHd a c f (pbody f (pk0 c) (pkx a f) c.nm s j) := by
  obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, hxo, hmono⟩ := rsB_fix hF
  obtain ⟨hR, hI, -, -, -, -, -, -⟩ := h
  have hI' := pbody_inv (by omega) (by omega) (rsB_hf hF) hI hj hnp
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := hI
  refine ⟨rsB_reach_step hR hnr hj hnp ht, hI', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> dsimp only [pbody]
  · split <;> omega
  · split <;> omega
  · omega
  · omega
  · omega
  · omega

/-- The byte lists start as read: `mk 6 (old l) = l`. -/
theorem rsB_mk_old {l : List UInt8} (h : l.length = 6) : mk 6 (old l) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp [mk, old, List.getD, List.getElem?_eq_getElem h2]

/-- Lexicographic comparison of the loop's variants (digits below `2 ^ 64`). -/
theorem rsB_lex_le {c a1 b1 a2 b2 a3 b3 : Nat} (h1 : a1 = b1) (hb2 : b2 < 2 ^ 64)
    (hb3 : b3 < 2 ^ 64) (h2 : a2 < b2 ∨ (a2 = b2 ∧ a3 ≤ b3)) :
    lex [c, a1, a2, a3] ≤ lex [c, b1, b2, b3] := by
  subst h1
  refine lex_cons_le_cons rfl (lex_cons_le_cons rfl ?_)
  rcases h2 with h | ⟨rfl, h⟩
  · exact lex_cons_le_of_lt rfl (by rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb2]; exact h)
  · refine lex_cons_le_cons rfl ?_
    simp only [lex_cons, lex_nil, List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
      Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb3]; exact h

theorem rsB_lex_lt {c a1 b1 a2 b2 a3 b3 : Nat} (hb1 : b1 < 2 ^ 64) (hb2 : b2 < 2 ^ 64)
    (hb3 : b3 < 2 ^ 64) (h : a1 < b1 ∨ (a1 = b1 ∧ (a2 < b2 ∨ (a2 = b2 ∧ a3 < b3)))) :
    lex [c, a1, a2, a3] < lex [c, b1, b2, b3] := by
  refine lex_cons_lt_cons rfl ?_
  rcases h with h | ⟨rfl, h⟩
  · exact lex_cons_lt_of_lt rfl (by rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb1]; exact h)
  refine lex_cons_lt_cons rfl ?_
  rcases h with h | ⟨rfl, h⟩
  · exact lex_cons_lt_of_lt rfl (by rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb2]; exact h)
  refine lex_cons_lt_cons rfl ?_
  simp only [lex_cons, lex_nil, List.length_nil, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
    Nat.add_zero]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb3]; exact h

theorem rsB_k0_pos {sr : Int} {st xo : Nat} {k0 : Int} {nm : Nat} {f : Nat → Nat}
    (h : Master sr st xo (some k0) (some (nm, f))) (hst : st < 16) : 1 ≤ k0 := by
  cases h with
  | ok k2 _ _ hr h64 hk hq hxo hf0 hinc hfn => exact (k0Of_range hr hst).1

/-- A 32-bit compare of a small `Nat` register with an `Int` value. -/
theorem rsB_bv32_eq {z : Int} {x : Nat} (hz1 : -1 ≤ z) (hz2 : z < 2 ^ 31) (hx : x < 2 ^ 31) :
    (BitVec.ofNat 64 x).setWidth 32 = BitVec.ofInt 32 z ↔ (x : Int) = z := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt] at this
    omega
  · intro h; subst h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega

/-- A loop run that returned `0` (from a reached state) is a failure `Reset` allows. -/
theorem rsB_reset_fail {a : RArgs} {c : PCx} {f : Nat → Nat} {p r : PL} (hst : u8 a.sp 0 < 16)
    (hF : PFix a c f) (hR : PReach a c f p) (hr : PR a c f p r false) :
    Reset (spOf a) (lbN a) a.x (pxs a c f r).turnoff := by
  obtain ⟨hM, h64, h32, hq1, hq5, -⟩ := hF
  obtain ⟨ki, hk, hrun⟩ := hR
  have hP : Patches f a.x.sampleRate.toInt (x0D a c.k0).k0 (f (xoOf a)) (f c.nm - f (xoOf a)) c.nm
      (px0 a c f) _ false := Patches.run ki hk (hrun r false hr)
  have hD : Derived a.x.sampleRate.toInt (lbN a) c.nm (xoOf a) f (x0D a c.k0) _ false :=
    Derived.badPatch c.q h64 h32 hq1 hq5 hP
  have := Reset.badDerived (sp := spOf a) hst hM hD
  simp only [Bool.false_eq_true, false_and, ↓reduceIte] at this
  exact this

theorem rsB_bv32_eq' {z : Int} {x : Nat} (hz1 : -1 ≤ z) (hz2 : z < 2 ^ 31) (hx : x < 2 ^ 31) :
    BitVec.ofInt 32 z = (BitVec.ofNat 64 x).setWidth 32 ↔ (x : Int) = z := by
  rw [eq_comm]; exact rsB_bv32_eq hz1 hz2 hx

section Slot
variable [CodeEnv]

/-- The variants' frame slot `slot32 s d` is the frame's `frSlot32 fr d`. -/
theorem rsB_slot32 {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData} {st : St}
    {fr : List UInt8} (hm : s.dmem =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr)
    (hrbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) {d : Nat} (h1 : 0x2c ≤ d)
    (h2 : d ≤ 0x570) : slot32 s d = frSlot32 fr d := by
  rw [slot32_of_load (v := Int.ofBytes (slice fr (rb d) 4))
    (by rw [hrbp]; exact fr_load hm hF (by omega) h2)]

/-- `rsB_slot32` for a later state with the same memory and `rbp`. -/
theorem rsB_slot32' {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ s : MachineData} {st : St}
    {fr : List UInt8} (hm : s.dmem =⋆ Mm k e a ra t₀ st fr) (hF : FrOk fr)
    (hrbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) {d : Nat} (h1 : 0x2c ≤ d)
    (h2 : d ≤ 0x570) (s' : MachineData) (hd : s'.dmem = s.dmem)
    (hb : s'.regs.get64 .rbp = s.regs.get64 .rbp) : slot32 s' d = frSlot32 fr d :=
  rsB_slot32 (hd ▸ hm) hF (hb ▸ hrbp) h1 h2

/-- An element of `f_master`. -/
theorem rsB_fm_load {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
    {fr : List UInt8} {m : Mem 64} (hm : m =⋆ Mm k e a ra t₀ st fr) (hfm : st.fm.length = 98)
    {i : Nat} (hi : i < 49) {addr : BitVec 64}
    (ha : addr = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * i)) :
    m.loadInt addr 2 = some (fOf st i : Int) := by
  rw [region_load (o := 2 * i) (n := 2) (focus (Mm_fm ..) hm) ha (by omega) (by omega),
    ofBytes_slice2 _ _ (by omega)]
  try rfl

end Slot

/-- The low half of a 4-byte slot holding a small value. -/
theorem rsB_slice2_of4 {l : List UInt8} {o v : Nat} (hl : o + 4 ≤ l.length)
    (h : BitVec.ofInt 32 (Int.ofBytes (slice l o 4)) = BitVec.ofNat 32 v) (hv : v < 2 ^ 16) :
    Int.ofBytes (slice l o 2) = v := by
  have e4 : slice l o 4 = [l[o], l[o + 1], l[o + 2], l[o + 3]] := by
    apply List.ext_getElem (by simp only [slice, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]; omega)
    intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [slice, List.getElem_take, List.getElem_drop]
    rcases j with _ | _ | _ | _ | j
    · rfl
    · rfl
    · rfl
    · rfl
    · omega
  have e2 : slice l o 2 = [l[o], l[o + 1]] := by
    apply List.ext_getElem (by simp only [slice, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]; omega)
    intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [slice, List.getElem_take, List.getElem_drop]
    rcases j with _ | _ | j
    · rfl
    · rfl
    · omega
  rw [e4] at h; rw [e2]
  simp only [Int.ofBytes_cons, show Int.ofBytes [] = 0 from rfl] at h ⊢
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat] at h'
  have b0 := UInt8.toNat_lt l[o]
  have b1 := UInt8.toNat_lt l[o + 1]
  have b2 := UInt8.toNat_lt l[o + 2]
  have b3 := UInt8.toNat_lt l[o + 3]
  omega

/-- `~odd + (msb + k0)` in 32 bits. -/
theorem rsB_not_add {x y : Nat} (hx : x ≤ 1) (hy : y < 2 ^ 31) (hxy : x + 1 ≤ y) :
    (~~~(BitVec.ofNat 32 x) + BitVec.ofNat 32 y).toNat = y - x - 1 := by
  simp only [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat]
  omega

theorem rsB_sw {x : Nat} (h : x < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x)) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem rsB_toNat {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 64 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

theorem rsB_toNat32 {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  simp only [BitVec.toNat_ofNat]; omega

end Kraken.Examples.Sbr.Reset
