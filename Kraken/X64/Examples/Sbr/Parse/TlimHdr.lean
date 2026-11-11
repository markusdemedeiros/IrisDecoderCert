import Kraken.X64.Examples.Sbr.Parse.TlimSpec

/-!
# `sbr_make_f_tablelim`: the contract in the header's shape

`read_sbr_header` (`HdrSpec.lean`) takes the callee's contract with the frame and
`bs_limiter_bands` as the logical variable, an abstract footprint `TlT sbr` / `TlT' lb sbr` and a
side condition `TlC lb sbr`. `HdrShape` restates that shape; `hdr_shape` instantiates it from
`TlimSpec`: the footprint hides the decoder values `a` (with the facts `TlimC` asks of them), the
result hides the `Tablelim` successor.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.Tlim

variable [CodeEnv]

/-- The header's form of the callee contract (`HdrSpec.TlimSpec`). -/
abbrev HdrShape (TlT : BitVec 64 → Mem 64 → Prop) (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop)
    (TlC : BitVec 32 → BitVec 64 → Prop) (k : Nat) : Prop :=
  cenv.ProcSpec (entry "sbr_make_f_tablelim")
    (fun (y : (Mem 64 → Prop) × BitVec 32) ra t =>
      CallPre k (cell4 (arg0 t + 0x2c#64) y.2 ⋆ (TlT (arg0 t) ⋆ y.1)) ra t ∧ TlC y.2 (arg0 t))
    (fun y ra t s => CallPost k (cell4 (arg0 t + 0x2c#64) y.2 ⋆ (TlT' y.2 (arg0 t) ⋆ y.1)) ra t s)

/-- `TlimF` without `bs_limiter_bands`. -/
abbrev TlR (a : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x58#64) a.kx1 ⋆ (c4 (s + 0x4c1e0#64) a.n0
    ⋆ (c4 (s + 0x4c1ec#64) a.nlim ⋆ (a.ftLow =@ (s + 0x4c252#64) ⋆ (a.ftLim =@ (s + 0x4c2f2#64)
    ⋆ (c4 (s + 0x4c330#64) a.npatch ⋆ (a.pnum =@ (s + 0x4c334#64) ⋆ Blocks [(BW, 12)]))))))

/-- The facts `TlimC` asks of the values (with `n[0] + num_patches ≥ 1` for every
`bs_limiter_bands`, as on the header's path). -/
def TlA (a : Args) : Prop :=
  a.n0 ≤ 24 ∧ a.npatch ≤ 6 ∧ 1 ≤ a.n0 + a.npatch
  ∧ a.ftLow.length = 50 ∧ a.ftLim.length = 60 ∧ a.pnum.length = 6
  ∧ TabIn a.ftLow a.n0 a.kx1 (a.kx1 + a.m1) ∧ psum a.pnum a.npatch ≤ a.m1 ∧ a.kx1 + a.m1 ≤ 64
  ∧ a.nlim < 2 ^ 32

/-- The footprint before the call: some values `a` with `TlA a`. -/
def TlT (s : BitVec 64) : Mem 64 → Prop := fun m => ∃ a, TlA a ∧ TlR a s m

/-- After the call: a `Tablelim` successor of such values. -/
def TlT' (lb : BitVec 32) (s : BitVec 64) : Mem 64 → Prop :=
  fun m => ∃ a y, TlA a ∧ Tablelim lb.toNat a y ∧ TlR y s m

/-- The side condition on `bs_limiter_bands` and the address. -/
def TlC (lb : BitVec 32) (s : BitVec 64) : Prop := lb.toNat ≤ 3 ∧ s.toNat + 0x4c340 < 2 ^ 64

omit [CodeEnv] in
theorem sep_ex_r {α : Type} {P : Mem 64 → Prop} {Q : α → Mem 64 → Prop} {m : Mem 64}
    (h : (P ⋆ fun m => ∃ a, Q a m) m) : ∃ a, (P ⋆ Q a) m := by
  obtain ⟨u, v, h1, h2, hp, a, hq⟩ := h
  exact ⟨a, u, v, h1, h2, hp, hq⟩

omit [CodeEnv] in
theorem sep_ex_l {α : Type} {Q : α → Mem 64 → Prop} {R : Mem 64 → Prop} {m : Mem 64}
    (h : ((fun m => ∃ a, Q a m) ⋆ R) m) : ∃ a, (Q a ⋆ R) m := by
  obtain ⟨u, v, h1, h2, ⟨a, hq⟩, hr⟩ := h
  exact ⟨a, u, v, h1, h2, hq, hr⟩

omit [CodeEnv] in
theorem sep_mono_r {P Q Q' : Mem 64 → Prop} {m : Mem 64} (hq : ∀ m, Q m → Q' m)
    (h : (P ⋆ Q) m) : (P ⋆ Q') m := by
  obtain ⟨u, v, h1, h2, hp, hv⟩ := h
  exact ⟨u, v, h1, h2, hp, hq v hv⟩

omit [CodeEnv] in
theorem sep_mono_l {P P' Q : Mem 64 → Prop} {m : Mem 64} (hp : ∀ m, P m → P' m)
    (h : (P ⋆ Q) m) : (P' ⋆ Q) m := by
  obtain ⟨u, v, h1, h2, hu, hv⟩ := h
  exact ⟨u, v, h1, h2, hp u hu, hv⟩

/-- Pull the values out of the header's precondition memory. -/
theorem pre_ex {A B C R : Mem 64 → Prop} {s : BitVec 64} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (C ⋆ (TlT s ⋆ R)))) m) : ∃ a, TlA a ∧ (A ⋆ (B ⋆ (C ⋆ (TlR a s ⋆ R)))) m := by
  have h1 := sep_mono_r (fun m (h : (B ⋆ (C ⋆ (TlT s ⋆ R))) m) =>
    sep_ex_r (sep_mono_r (fun m (h : (C ⋆ (TlT s ⋆ R)) m) =>
      sep_ex_r (sep_mono_r (fun m (h : (TlT s ⋆ R) m) =>
        sep_ex_l (Q := fun a m => TlA a ∧ TlR a s m) h) h)) h)) h
  obtain ⟨a, h2⟩ := sep_ex_r h1
  refine ⟨a, ?_, ?_⟩
  · obtain ⟨-, -, -, -, -, ⟨-, -, -, -, -, ⟨-, -, -, -, -, ⟨-, -, -, -, ⟨hA, -⟩, -⟩⟩⟩⟩ := h2
    exact hA
  · exact sep_mono_r (fun m h => sep_mono_r (fun m h => sep_mono_r
      (fun m h => sep_mono_l (fun m h => h.2) h) h) h) h2

theorem tlimF_split (lb : BitVec 32) (a : Args) (t : MachineData) (R : Mem 64 → Prop) :
    TlimF lb a t ⋆ R = cell4 (arg0 t + 0x2c#64) lb ⋆ (TlR a (arg0 t) ⋆ R) :=
  Std.ExtHashMap.sep_assoc _ _ _

/-- `TlimSpec` gives the contract in the header's shape (at the stack `tlimNeed k`). -/
theorem hdr_shape (k : Nat) (h : TlimSpec k) : HdrShape TlT TlT' TlC (tlimNeed k) := by
  rintro ⟨R, lb⟩ ra t ⟨hpre, hlb, hw⟩
  dsimp only at hpre hlb hw
  obtain ⟨a, hA, hm⟩ := pre_ex hpre
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hA
  refine eventually_weaken _ _ _ _ ?_ (h ⟨R, a, lb⟩ ra t ⟨?_, ?_⟩)
  · rintro st ⟨hra, y, hT, hsp, hbp, hsv, hm'⟩
    refine ⟨hra, hsp, hbp, hsv, ?_⟩
    rw [tlimF_split] at hm'
    exact sep_mono_r (fun m h => sep_mono_r (fun m h => sep_mono_r (fun m h =>
      sep_mono_l (fun m h => ⟨a, y, ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hT, h⟩) h) h) h) hm'
  · show CallPre (tlimNeed k) (TlimF lb a t ⋆ R) ra t
    unfold CallPre; rw [tlimF_split]
    exact hm
  · show TlimC lb a t
    exact ⟨hlb, h0, h1, fun _ => h2, h3, h4, h5, h6, h7, h8, h9, hw⟩

end Kraken.Examples.Sbr.Tlim
