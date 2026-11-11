import Kraken.X64.Examples.Sbr.Parse.DecExtSpec

/-!
# `ff_aac_sbr_decode_extension`: more stack for the callees' contracts

`ca_widen`: a contract of the form of `DecExtSpec`'s callee contracts (`CPre need` / `CPost need`
on the logical variable `CA`) holds with any `k ≥ need` bytes of stack: the excess
`k - need` bytes join the caller's memory `c.R` (`Reserve.excess`). The side condition `C` and
the value postcondition `P` must not depend on `c.R` (they do not, for the contracts of
`DecExtSpec`; each instance is `fun _ _ _ _ h => h`, `fun _ _ _ h => h`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

theorem ca_widen {f : Int64} {need k : Nat} {Ext : Mem 64 → Prop}
    {C : CA → Int64 → MachineData → Prop} {P : CA → DS → Prop}
    (h : cenv.ProcSpec f (fun c ra t => CPre need Ext c ra t ∧ C c ra t)
      (fun c ra t s => CPost need Ext c ra t s (P c)))
    (hC : ∀ (c : CA) (R : Mem 64 → Prop) ra t, C c ra t → C { c with R := R } ra t)
    (hP : ∀ (c : CA) (R : Mem 64 → Prop) d, P { c with R := R } d → P c d)
    (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) :
    cenv.ProcSpec f (fun c ra t => CPre k Ext c ra t ∧ C c ra t)
      (fun c ra t s => CPost k Ext c ra t s (P c)) := by
  intro c ra t ⟨⟨hcall, hr, hd⟩, hc⟩
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h { c with R := c.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k) } ra t
      ⟨⟨?_, hr, hd⟩, hC c _ ra t hc⟩)
  · rintro st ⟨hra, d', i', hp, hok, hxk, hi, h1, h2, h3, hm⟩
    refine ⟨hra, d', i', hP c _ d' hp, hok, hxk, hi, h1, h2, h3, ?_⟩
    have hm' : st.1.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
        ⋆ (CF Ext c d' i' ⋆ (c.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)))) := hm
    rw [e]
    exact Mem.ac hm'
  · show t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
        ⋆ (CF Ext c c.d c.i ⋆ (c.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k))))
    unfold CallPre at hcall
    rw [e] at hcall
    exact Mem.ac hcall

/-- `ca_widen` for a `ProcSpecS` contract on a logical variable `a` that holds a `CA` (`cOf a`;
`upd a R` replaces its caller's memory), with a value postcondition that may read the final
state. -/
theorem ca_widenS {α : Type} {stops : Int64 → Prop} {f : Int64} {need k : Nat}
    {Ext : Mem 64 → Prop} (cOf : α → CA) (upd : α → (Mem 64 → Prop) → α)
    (hcu : ∀ a R, cOf (upd a R) = { cOf a with R := R })
    {C : α → Int64 → MachineData → Prop} {P : α → MachineData → DS → Prop}
    (h : Kraken.Examples.Sbr.Parse.ProcSpecS stops f
      (fun a ra t => CPre need Ext (cOf a) ra t ∧ C a ra t)
      (fun a ra t s => CPost need Ext (cOf a) ra t s (P a s)))
    (hC : ∀ a R ra t, C a ra t → C (upd a R) ra t)
    (hP : ∀ a R s d, P (upd a R) s d → P a s d)
    (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) :
    Kraken.Examples.Sbr.Parse.ProcSpecS stops f
      (fun a ra t => CPre k Ext (cOf a) ra t ∧ C a ra t)
      (fun a ra t s => CPost k Ext (cOf a) ra t s (P a s)) := by
  intro a ra t ⟨⟨hcall, hr, hd⟩, hc⟩
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hcall)
  have hpre : CPre need Ext (cOf (upd a ((cOf a).R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)))) ra t ∧ C (upd a ((cOf a).R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k))) ra t := by
    rw [hcu]
    refine ⟨⟨?_, hr, hd⟩, hC a _ ra t hc⟩
    · show t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
          ⋆ (CF Ext (cOf a) (cOf a).d (cOf a).i ⋆ ((cOf a).R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k))))
      unfold CallPre at hcall
      rw [e] at hcall
      exact Mem.ac hcall
  refine eventually_weaken _ _ _ _ ?_ (h (upd a ((cOf a).R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k))) ra t hpre)
  rintro st (⟨hra, hpost⟩ | hs)
  · left
    rw [hcu] at hpost
    obtain ⟨d', i', hp, hok, hxk, hi, h1, h2, h3, hm⟩ := hpost
    refine ⟨hra, d', i', hP a ((cOf a).R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)) _ d' hp, hok, hxk, hi, h1, h2, h3, ?_⟩
    have hm' : st.1.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
        ⋆ (CF Ext (cOf a) d' i' ⋆ ((cOf a).R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)))) := hm
    rw [e]
    exact Mem.ac hm'
  · exact Or.inr hs

/-- For example, `read_sbr_header`'s local contract. -/
example {need k : Nat} {Ext : Mem 64 → Prop} (h : HdrSpec need Ext) (hk : need ≤ k)
    (hk' : k ≤ 2 ^ 64) : HdrSpec k Ext :=
  ca_widen h (fun _ _ _ _ h => h) (fun _ _ _ h => h) hk hk'

example {need k : Nat} {Ext : Mem 64 → Prop} (h : ResetSpec need Ext) (hk : need ≤ k)
    (hk' : k ≤ 2 ^ 64) : ResetSpec k Ext :=
  ca_widen h (fun _ _ _ _ h => h) (fun _ _ _ h => h) hk hk'

/-- `read_sbr_envelope`'s local contract. -/
example {need k : Nat} {Ext : Mem 64 → Prop} (h : EnvSpec need Ext) (hk : need ≤ k)
    (hk' : k ≤ 2 ^ 64) : EnvSpec k Ext :=
  ca_widenS (P := fun c _ d' => d' = c.d) id (fun c R => { c with R := R }) (fun _ _ => rfl) h
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) hk hk'

/-- `read_sbr_grid`'s local contract (logical variable `(c, b)`). -/
example {need k : Nat} {Ext : Mem 64 → Prop} (h : GridSpec need Ext) (hk : need ≤ k)
    (hk' : k ≤ 2 ^ 64) : GridSpec k Ext :=
  Kraken.Examples.Sbr.Parse.ProcSpecS.toA <|
    ca_widenS (fun cb : CA × Bool => cb.1) (fun cb R => ({ cb.1 with R := R }, cb.2))
      (fun _ _ => rfl) (Kraken.Examples.Sbr.Parse.ProcSpecA.toS h) (fun _ _ _ _ h => h)
      (fun _ _ _ _ h => h) hk hk'

end Kraken.Examples.Sbr.DecExt
