import Kraken.X64.Examples.Sbr.SessionBin.Bridge
import Kraken.X64.Examples.Sbr.Parse.DecExtAll
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueC
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueG
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueH
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueN
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueP
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueR
import Kraken.X64.Examples.Sbr.Parse.DecExtNeed
import Kraken.X64.Examples.Sbr.Parse.HdrProc
import Kraken.X64.Examples.Sbr.Parse.ResetProc
import Kraken.X64.Examples.Sbr.Parse.TlimProc
import Kraken.X64.Examples.Sbr.Parse.GridAsm
import Kraken.X64.Examples.Sbr.Parse.DtdfProc
import Kraken.X64.Examples.Sbr.Parse.InvfProc
import Kraken.X64.Examples.Sbr.Parse.EnvProc
import Kraken.X64.Examples.Sbr.Parse.NoiseProc
import Kraken.X64.Examples.Sbr.Parse.PsEntry

/-!
# A decoding session over the binary: `decode_extension` from the routines' own specifications

`decAsm_core`: `DecExtSpec PsInv kc (ExtD e vs vp)` (`ff_aac_sbr_decode_extension`) from the
placement of the parser's texts, the assumed external contracts and data facts, by
`decExtSpec_holds` with each callee's local contract obtained from the routine's own
specification through its adapter (`DecExtGlue*`), framed to `ExtD` and widened to `kc`:
* the leaf contracts on `e.Ext` (`av_log`, `avpriv_request_sample`, `powf`, `log2f`) are framed
  by the parser's tables (`leaf_fw`, `leaf_fw0`);
* `Tlim.TlimSpec` is `Reset.TlimSpec` (`tlim_reset`, the same contract with the logical
  variable packed differently);
* `ps_widen`: `ff_ps_read_data`'s local contract at a larger stack.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-! ## Framing and widening the leaf contracts -/

/-- A leaf contract with a value postcondition `Q`, framed by `A` and at a larger stack. -/
theorem leaf_fw {f : Int64} {need k : Nat} {E : Mem 64 → Prop} (A : Mem 64 → Prop)
    {C : MachineData → Prop} {Q : MachineData → MachineData → Prop}
    (h : cenv.ProcSpec f (LeafPre need (fun _ => E) C)
      (fun R ra t s => LeafPost need (fun _ => E) R ra t s ∧ Q t s))
    (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) :
    cenv.ProcSpec f (LeafPre k (fun _ => A ⋆ E) C)
      (fun R ra t s => LeafPost k (fun _ => A ⋆ E) R ra t s ∧ Q t s) := by
  intro R ra t ⟨hcall, hc⟩
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h (A ⋆ R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)) ra t ⟨?_, hc⟩)
  · rintro st ⟨hra, ⟨h1, h2, h3, hm⟩, hq⟩
    refine ⟨hra, ⟨h1, h2, h3, ?_⟩, hq⟩
    rw [e]; (try dsimp only at hm); (try dsimp only); exact Mem.ac hm
  · unfold CallPre at hcall ⊢
    rw [e] at hcall
    (try dsimp only at hcall); (try dsimp only)
    exact Mem.ac hcall

/-- `leaf_fw` for a leaf contract without a value postcondition (`LeafSpec`). -/
theorem leaf_fw0 {l : Label} {need k : Nat} {E : Mem 64 → Prop} (A : Mem 64 → Prop)
    {C : MachineData → Prop} (h : LeafSpec l need (fun _ => E) C)
    (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) : LeafSpec l k (fun _ => A ⋆ E) C := by
  intro R ra t ⟨hcall, hc⟩
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h (A ⋆ R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)) ra t ⟨?_, hc⟩)
  · rintro st ⟨hra, h1, h2, h3, hm⟩
    refine ⟨hra, h1, h2, h3, ?_⟩
    rw [e]; (try dsimp only at hm); (try dsimp only); exact Mem.ac hm
  · unfold CallPre at hcall ⊢
    rw [e] at hcall
    (try dsimp only at hcall); (try dsimp only)
    exact Mem.ac hcall

/-- `av_log` on `e.Ext`, framed by `A`, at a larger stack. -/
theorem avlog_fw {E : Mem 64 → Prop} {need k : Nat} (A : Mem 64 → Prop) (h : AvLogSpec E need)
    (hk : need ≤ k) (hk' : k ≤ 2 ^ 64) : AvLogSpec (A ⋆ E) k :=
  leaf_fw0 A h hk hk'

/-- `avpriv_request_sample` on `e.Ext`, framed by `A`, at a larger stack. -/
theorem avreq_fw {E : Mem 64 → Prop} {need k : Nat} (A : Mem 64 → Prop)
    (h : DecExt.AvReqSpec E need) (hk : need ≤ k) (hk' : k ≤ 2 ^ 64) :
    DecExt.AvReqSpec (A ⋆ E) k :=
  leaf_fw0 A h hk hk'

theorem powf_fw {E : Mem 64 → Prop} {pw : BitVec 32 → BitVec 32 → BitVec 32}
    {lg : BitVec 32 → BitVec 32} {k : Nat} (A : Mem 64 → Prop) (hk : k ≤ 2 ^ 64)
    (h : Reset.PowfSpec ⟨E, pw, lg⟩ k) : Reset.PowfSpec ⟨A ⋆ E, pw, lg⟩ k :=
  leaf_fw A h (Nat.le_refl _) hk

theorem log2f_fw {E : Mem 64 → Prop} {pw : BitVec 32 → BitVec 32 → BitVec 32}
    {lg : BitVec 32 → BitVec 32} {k : Nat} (A : Mem 64 → Prop) (hk : k ≤ 2 ^ 64)
    (h : Reset.Log2fSpec ⟨E, pw, lg⟩ k) : Reset.Log2fSpec ⟨A ⋆ E, pw, lg⟩ k :=
  leaf_fw A h (Nat.le_refl _) hk

/-- `sbr_make_f_tablelim`'s own statement is the contract `sbr_reset` and the header use. -/
theorem tlim_reset {k : Nat} (h : Tlim.TlimSpec k) : Reset.TlimSpec k :=
  fun a ra t hp => h ⟨a.1, a.2.2, a.2.1⟩ ra t hp

/-- `ff_ps_read_data`'s local contract at a larger stack. -/
theorem ps_widen {PI : List UInt8 → Prop} {need k : Nat} {Ext : Mem 64 → Prop}
    (h : DecExt.PsSpec PI need Ext) (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) :
    DecExt.PsSpec PI k Ext := by
  intro p ra t ⟨hcall, h1, h2, h3, h4, h5⟩
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h { p with R := p.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k) } ra t
      ⟨?_, h1, h2, h3, h4, h5⟩)
  · rintro st ⟨hra, c', i', q1, q2, q3, q4, q5, q6, g1, g2, g3, hm⟩
    refine ⟨hra, c', i', q1, q2, q3, q4, q5, q6, g1, g2, g3, ?_⟩
    rw [e]; (try dsimp only at hm); (try dsimp only); exact Mem.ac hm
  · unfold CallPre at hcall ⊢
    rw [e] at hcall
    (try dsimp only at hcall); (try dsimp only)
    exact Mem.ac hcall

/-- `ca_widen` with a value postcondition that may read the entry state. -/
theorem ca_widenT {f : Int64} {need k : Nat} {Ext : Mem 64 → Prop}
    {C : DecExt.CA → Int64 → MachineData → Prop} {P : DecExt.CA → MachineData → DecExt.DS → Prop}
    (h : cenv.ProcSpec f (fun c ra t => DecExt.CPre need Ext c ra t ∧ C c ra t)
      (fun c ra t s => DecExt.CPost need Ext c ra t s (P c t)))
    (hC : ∀ (c : DecExt.CA) (R : Mem 64 → Prop) ra t, C c ra t → C { c with R := R } ra t)
    (hP : ∀ (c : DecExt.CA) (R : Mem 64 → Prop) t d, P { c with R := R } t d → P c t d)
    (hk : need ≤ k) (_hk' : k ≤ 2 ^ 64) :
    cenv.ProcSpec f (fun c ra t => DecExt.CPre k Ext c ra t ∧ C c ra t)
      (fun c ra t s => DecExt.CPost k Ext c ra t s (P c t)) := by
  intro c ra t ⟨⟨hcall, hr, hd⟩, hc⟩
  have e := Reserve.excess need k (t.regs.get64 .rsp) hk (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h { c with R := c.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k) } ra t
      ⟨⟨?_, hr, hd⟩, hC c _ ra t hc⟩)
  · rintro st ⟨hra, d', i', hp, hok, hxk, hi, h1, h2, h3, hm⟩
    refine ⟨hra, d', i', hP c _ t d' hp, hok, hxk, hi, h1, h2, h3, ?_⟩
    have hm' : st.1.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
        ⋆ (DecExt.CF Ext c d' i' ⋆ (c.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k)))) := hm
    rw [e]
    exact Mem.ac hm'
  · show t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
        ⋆ (DecExt.CF Ext c c.d c.i ⋆ (c.R ⋆ (k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 k))))
    unfold CallPre at hcall
    rw [e] at hcall
    exact Mem.ac hcall

/-! ## The assembly -/

/-- **`decode_extension` from the routines' own specifications** (core form): the stack of the
callees is `sbr_reset`'s need `0x9d0 + k`. -/
theorem decAsm_core (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32)
    (hk : 0x9d0 + k ≤ 2 ^ 32) (hpl : SessPlaced) (has : SessionAssumed k e vs vp pw lg)
    (hal : isAligned 16 (lab "LCPI5_6") = true) :
    DecExt.DecExtSpec Ps.PsInv (0x9d0 + k) (ExtD e vs vp) := by
  have hk1 : k ≤ 2 ^ 32 := by omega
  have hk64 : 0x9d0 + k ≤ 2 ^ 64 := by omega
  -- the leaf contracts on the parser's callee states
  have avP : AvLogSpec (Ps.PsTabs vp ⋆ e.Ext) k :=
    avlog_fw _ has.avLog (Nat.le_refl _) (by omega)
  have avV : AvLogSpec (Vlc.VlcW vs ⋆ (Ps.PsTabs vp ⋆ e.Ext)) k :=
    avlog_fw _ avP (Nat.le_refl _) (by omega)
  -- the routines
  have hT : Reset.TlimSpec k := tlim_reset (Tlim.spec hpl.tlim k hk1 has.memcpyV)
  have hRc : Reset.ResetCallees k ⟨Vlc.VlcW vs ⋆ (Ps.PsTabs vp ⋆ e.Ext), pw, lg⟩ :=
    ⟨avV, powf_fw _ (by omega) (powf_fw _ (by omega) has.powf),
      log2f_fw _ (by omega) (log2f_fw _ (by omega) has.log2f), has.memcpyV, hT⟩
  have hR := DecExt.reset_glue k _ (Reset.spec hpl.reset k hk1 _ hRc) has.bands hal
  have hH := DecExt.hdr_glue (Reset.tlimNeed k) k ⟨Vlc.VlcW vs ⋆ (Ps.PsTabs vp ⋆ e.Ext), pw, lg⟩
    (fun TlT TlT' TlC htl => Hdr.spec hpl.hdr (Reset.tlimNeed k) (by simp only [Reset.tlimNeed]; omega) TlT TlT' TlC htl) hT
  have hG := DecExt.grid_glue k Reset.CstR Reset.BwR (Vlc.VlcW vs) (Ps.PsTabs vp ⋆ e.Ext) hpl.jt
    (Grid.spec hpl.grid k hk1 _ avP has.memsetV)
  have hD := DecExt.dtdf_glue k (ExtD e vs vp) (Dtdf.dtdf_spec hpl.dtdf k)
  have hI := DecExt.invf_glue (ExtD e vs vp) (Invf.spec hpl.invf)
  have hV := DecExt.env_glue k Reset.CstR Reset.BwR (Ps.PsTabs vp ⋆ e.Ext) vs has.vlcS
    (Env.read_sbr_envelope_spec hpl.env k hk1 _ avP)
  have hN := DecExt.noise_glue k Reset.CstR Reset.BwR (Ps.PsTabs vp ⋆ e.Ext) vs has.vlcS
    (Noise.spec hpl.noise k hk1 _ avP ⟨trivial⟩)
  have hP := DecExt.ps_glue k Reset.CstR Reset.BwR (Vlc.VlcW vs) e.Ext vp has.vlcP
    (Ps.spec hpl.ps k hk1 e.Ext has.avLog has.memsetV)
  refine DecExt.decExtSpec_holds Ps.PsInv (0x9d0 + k) hk (ExtD e vs vp)
    (avlog_fw _ (avlog_fw _ avV (Nat.le_refl _) (by omega)) (by omega) hk64)
    ?_ hR ?_ ?_ ?_ ?_ ?_ (ps_widen hP (by simp only [Ps.psNeed]; omega) hk64)
    (avreq_fw _ (avreq_fw _ (avreq_fw _ (avreq_fw _ has.avReq (Nat.le_refl _) (by omega))
      (Nat.le_refl _) (by omega)) (Nat.le_refl _) (by omega)) (by omega) hk64)
    ⟨⟩ hpl.decExt
  · exact DecExt.ca_widen hH (fun _ _ _ _ h => h) (fun _ _ _ h => h)
      (by simp only [Hdr.hdrNeed, Reset.tlimNeed]; omega) hk64
  · exact Kraken.Examples.Sbr.Parse.ProcSpecS.toA <|
      DecExt.ca_widenS (fun cb : DecExt.CA × Bool => cb.1)
        (fun cb R => ({ cb.1 with R := R }, cb.2))
        (fun _ _ => rfl) (Kraken.Examples.Sbr.Parse.ProcSpecA.toS hG) (fun _ _ _ _ h => h)
        (fun _ _ _ _ h => h) (by simp only [Grid.gridNeed]; omega) hk64
  · exact DecExt.ca_widen hD (fun _ _ _ _ h => h) (fun _ _ _ h => h) (by omega) hk64
  · exact ca_widenT hI (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (by omega) hk64
  · exact DecExt.ca_widenS (P := fun c _ d' => d' = c.d) id (fun c R => { c with R := R })
      (fun _ _ => rfl) hV (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (by simp only [Env.envNeed]; omega) hk64
  · exact DecExt.ca_widen hN (fun _ _ _ _ h => h) (fun _ _ _ h => h)
      (by simp only [Noise.noiseNeed]; omega) hk64

/-- **`decode_extension` from the routines' own specifications.** -/
theorem decAsm : DecAsm := fun k e vs vp pw lg hk hpl has =>
  decAsm_core k e vs vp pw lg hk hpl has hpl.lcpi

end Kraken.Examples.Sbr.SessionBin
