import Kraken.X64.Examples.Sbr.SessionBin.DecAsm
import Kraken.X64.Examples.Sbr.SessionBin.BridgeU
import Kraken.X64.Examples.Sbr.Parse.UsacAsm
import Kraken.X64.Examples.Sbr.Parse.UsacGlueL
import Kraken.X64.Examples.Sbr.Parse.UsacGlueH
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# A decoding session over the binary: `decode_usac_data` from the routines' own specifications

`usacAsm`: `UsacSpec (usacK k) e.Ext (OthU vs vp)` from the placement of the parser's texts and
the assumed external contracts and data facts, by `usacSpec_holds` with each callee's contract
obtained from the routine's own specification through its adapter (`UsacGlue*`); the callees'
stack `cneed (usacK k) = 0x9d0 + k` is `sbr_reset`'s need. `read_sbr_grid`'s own specification
is its contract, widened (`grid_widen`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

/-- `read_sbr_grid`'s specification at a larger stack. -/
theorem grid_widen {k K : Nat} {Ext : Mem 64 → Prop}
    (h : ProcSpecA (entry "read_sbr_grid") (Grid.GridPre k Ext) (Grid.GridPost k Ext))
    (hk : k ≤ K) (_hK : 0x30 + K ≤ 2 ^ 64) :
    ProcSpecA (entry "read_sbr_grid") (Grid.GridPre K Ext) (Grid.GridPost K Ext) := by
  intro x ra t ⟨hcall, hc⟩
  have e := Reserve.excess (Grid.gridNeed k) (Grid.gridNeed K) (t.regs.get64 .rsp)
    (by simp only [Grid.gridNeed]; omega) (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h { x with R := x.R ⋆ (Grid.gridNeed K - Grid.gridNeed k) ?@
      (t.regs.get64 .rsp - .ofNat 64 (Grid.gridNeed K)) } ra t ⟨?_, hc⟩)
  · rintro st (⟨hra, gs, ho, h1, h2, h3, hm⟩ | hab)
    · refine Or.inl ⟨hra, gs, ho, h1, h2, h3, ?_⟩
      rw [e]; (try dsimp only at hm); (try dsimp only); exact Mem.ac hm
    · exact Or.inr hab
  · unfold CallPre at hcall ⊢
    rw [e] at hcall
    (try dsimp only at hcall); (try dsimp only)
    exact Mem.ac hcall

/-- **`decode_usac_data` from the routines' own specifications.** -/
theorem usacAsm (k : Nat) (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab)
    (pw : BitVec 32 → BitVec 32 → BitVec 32) (lg : BitVec 32 → BitVec 32)
    (hk : 0x9d0 + k ≤ 2 ^ 32) (hpl : SessPlaced) (has : SessionAssumed k e vs vp pw lg) :
    Usac.UsacSpec (usacK k) e.Ext (OthU vs vp) := by
  have hk1 : k ≤ 2 ^ 32 := by omega
  have hc64 : Usac.cneed (usacK k) ≤ 2 ^ 64 := by
    simp only [Usac.cneed, Grid.gridNeed, usacK]; omega
  have hT : Reset.TlimSpec k := tlim_reset (Tlim.spec hpl.tlim k hk1 has.memcpyV)
  have hRc : Reset.ResetCallees k ⟨e.Ext, pw, lg⟩ :=
    ⟨has.avLog, has.powf, has.log2f, has.memcpyV, hT⟩
  have hO1 : OthU vs vp = Reset.CstR ⋆ (Reset.BwR ⋆ (Vlc.VlcW vs ⋆ Ps.PsTabs vp)) := rfl
  have hO2 : OthU vs vp = Reset.BwR ⋆ (Reset.CstR ⋆ (Vlc.VlcW vs ⋆ Ps.PsTabs vp)) := by
    unfold OthU; rw [Std.ExtHashMap.sep_comm_l]
  have hO3 : OthU vs vp = Vlc.VlcW vs ⋆ (Reset.CstR ⋆ (Reset.BwR ⋆ Ps.PsTabs vp)) := by
    unfold OthU; rw [Std.ExtHashMap.sep_comm_l Reset.BwR, Std.ExtHashMap.sep_comm_l Reset.CstR]
  have hG : Usac.GridSpecA (usacK k) e.Ext :=
    grid_widen (Grid.spec hpl.grid k hk1 e.Ext has.avLog has.memsetV)
      (by simp only [usacK]; omega) (by simp only [usacK]; omega)
  have hH : Usac.HeaderSpec (usacK k) e.Ext (OthU vs vp) :=
    Usac.usac_hdr_glue (usacK k) (Reset.tlimNeed k) k e.Ext (OthU vs vp) _ hO2
      (by simp only [Hdr.hdrNeed, Reset.tlimNeed, Usac.cneed, Grid.gridNeed, usacK]; omega) hc64
      (fun TlT TlT' TlC htl => Hdr.spec hpl.hdr (Reset.tlimNeed k)
        (by simp only [Reset.tlimNeed]; omega) TlT TlT' TlC htl) hT
  have hTl : Usac.TablelimSpec (usacK k) e.Ext (OthU vs vp) :=
    Usac.usac_tlim_glue (usacK k) k e.Ext (OthU vs vp) _ hO2
      (by simp only [Reset.tlimNeed, Usac.cneed, Grid.gridNeed, usacK]; omega) hc64 hT
  have hR : Usac.ResetSpec (usacK k) e.Ext (OthU vs vp) :=
    Usac.usac_reset_glue (usacK k) k ⟨e.Ext, pw, lg⟩ (OthU vs vp) _ hO1
      (by simp only [Reset.resetNeed, Usac.cneed, Grid.gridNeed, usacK]; omega) hc64
      (Reset.spec hpl.reset k hk1 _ hRc) has.bands hpl.lcpi
  have hD := Dtdf.dtdf_spec hpl.dtdf (Usac.cneed (usacK k))
  have hI := Invf.spec hpl.invf
  have hV := Env.read_sbr_envelope_spec hpl.env k hk1 e.Ext has.avLog
  have hN := Noise.spec hpl.noise k hk1 e.Ext has.avLog ⟨trivial⟩
  have hkv : Env.envNeed k ≤ Usac.cneed (usacK k) := by
    simp only [Env.envNeed, Usac.cneed, Grid.gridNeed, usacK]; omega
  have hkn : Noise.noiseNeed k ≤ Usac.cneed (usacK k) := by
    simp only [Noise.noiseNeed, Usac.cneed, Grid.gridNeed, usacK]; omega
  refine Usac.usacSpec_holds (usacK k) (by simp only [usacK]; omega) e.Ext (OthU vs vp)
    ⟨hG, hH, hTl, hR, Usac.usac_dtdf_glue _ 0 (by decide) _ _ hD,
      Usac.usac_dtdf_glue _ 1 (by decide) _ _ hD, Usac.usac_invf_glue _ 0 (by decide) _ _ hI,
      Usac.usac_invf_glue _ 1 (by decide) _ _ hI,
      Usac.usac_env_glue _ k 0 (by decide) _ _ _ vs has.vlcS hO3 hkv hV,
      Usac.usac_env_glue _ k 1 (by decide) _ _ _ vs has.vlcS hO3 hkv hV,
      Usac.usac_noise_glue _ k 0 (by decide) _ _ _ vs has.vlcS hO3 hkn hN,
      Usac.usac_noise_glue _ k 1 (by decide) _ _ _ vs has.vlcS hO3 hkn hN⟩ hpl.usac

end Kraken.Examples.Sbr.SessionBin
