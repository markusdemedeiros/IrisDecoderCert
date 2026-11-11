import SbrClient.FFmpeg.Contracts
import SbrClient.Host.Native

/-! Host-facing FFmpeg rules: a foreign call is an interleaving of verified
x86 instructions. The returned resources can be moved into lock and mailbox
invariants using the ordinary Iris rules of the explicit host language. -/
noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.SessionBin
open Iris Iris.ProgramLogic Iris.BI Iris.Std Iris.ProofMode

variable {hlc : HasLC} {M : SbrClient.Model} {GF : BundledGFunctors}
variable [MachineGS hlc M GF] [CodeEnv]
local bi (IProp GF)

theorem wp_apply (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32)
    {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {t : MachineData}
    (hc : ApplyCall che ac t)
    (hm : CallPre (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) M.halt t)
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (k : CPU → Host.Expr M) {E : CoPset} {Φ : Host.Value → IProp GF} :
    owns t.dmem ∗ ▷ (∀ c,
      abiResources (applyStack S.k) t ∗ ready S che ac ∗
      ownsPred (AcFields ac avctx er ps) ∗ outputs t ∗ ownsPred Rc -∗
      WP (k c) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Host.Expr.native (.run (CPU.ofMachine (t, entry "ff_aac_sbr_apply"))) k)
        @ Stuckness.NotStuck; E {{ Φ }} := by
  have hrun := C.apply hk hc hm
  unfold Ends at hrun
  rw [hcode] at hrun
  have hrun' := eventually_weaken _ _ _ _ (fun st h => h.elim id False.elim) hrun
  iintro ⟨Hp, HK⟩
  iapply Host.wp_native_run hrun' hne k
  iframe Hp
  inext
  iintro %c %p %hpost Hp
  iapply HK $$ %c
  have hresources := apply_resources (GF := GF) S hpost.2
  simp only [CPU.pack] at hresources
  iapply hresources $$ Hp

theorem wp_config (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {t : MachineData}
    (hc : ConfigCall che ac t)
    (hm : CallPre 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) M.halt t)
    (hne : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (k : CPU → Host.Expr M) {E : CoPset} {Φ : Host.Value → IProp GF} :
    owns t.dmem ∗ ▷ (∀ c,
      abiResources 0 t ∗ ready S che ac ∗ ownsPred (AcFields ac avctx er ps) ∗ ownsPred Rc -∗
      WP (k c) @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Host.Expr.native (.run (CPU.ofMachine (t, entry "ff_aac_sbr_config_usac"))) k)
        @ Stuckness.NotStuck; E {{ Φ }} := by
  have hrun := C.config hc hm
  unfold Ends at hrun
  rw [hcode] at hrun
  have hrun' := eventually_weaken _ _ _ _ (fun st h => h.elim id False.elim) hrun
  iintro ⟨Hp, HK⟩
  iapply Host.wp_native_run hrun' hne k
  iframe Hp
  inext
  iintro %c %p %hpost Hp
  iapply HK $$ %c
  have hresources := config_resources (GF := GF) S hpost.2.2
  simp only [CPU.pack] at hresources
  iapply hresources $$ Hp

/-- Entry resources are existentially hidden in the Iris assertion, allowing
this rule to consume a decoder invariant opened by a lock acquisition. -/
theorem wp_apply_owned (S : Setup) (C : Calls S) (hcode : cenv = M.code)
    (hk : 0x9d0 + S.k ≤ 2 ^ 32) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ApplyCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_apply")
    (hne : entry "ff_aac_sbr_apply" ≠ M.halt)
    (k : CPU → Host.Expr M) {E : CoPset} {Φ : Host.Value → IProp GF} :
    ownsPred (fun p => CallPre (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs (c.pack ∅).1 ⋆ Rc)))
      M.halt (c.pack p).1) ∗ ▷ (∀ c',
      abiResources (applyStack S.k) (c.pack ∅).1 ∗ ready S che ac ∗
      ownsPred (AcFields ac avctx er ps) ∗ outputs (c.pack ∅).1 ∗ ownsPred Rc -∗
      WP (k c') @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Host.Expr.native (.run c) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨HP, HK⟩
  iunfold ownsPred at HP
  icases HP with ⟨%p, %hp, Hp⟩
  have hcall : ApplyCall che ac (c.pack p).1 := ⟨hc.args, hc.elem, hc.out, hc.align⟩
  have hcpu : CPU.ofMachine ((c.pack p).1, entry "ff_aac_sbr_apply") = c := by
    rw [← hpc]
    exact CPU.ofMachine_pack c p
  have hspec := wp_apply (GF := GF) S C hcode hk hcall hp hne k (E := E) (Φ := Φ)
  simp only [hcpu] at hspec
  iapply hspec
  simp only [CPU.pack, abiResources, outputs, OutBufs, arg3, arg4]
  iframe Hp
  iexact HK

theorem wp_config_owned (S : Setup) (C : Calls S) (hcode : cenv = M.code) (c : CPU)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {Rc : Mem 64 → Prop}
    (hc : ConfigCall che ac (c.pack ∅).1)
    (hpc : c.pc = entry "ff_aac_sbr_config_usac")
    (hne : entry "ff_aac_sbr_config_usac" ≠ M.halt)
    (k : CPU → Host.Expr M) {E : CoPset} {Φ : Host.Value → IProp GF} :
    ownsPred (fun p => CallPre 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc))
      M.halt (c.pack p).1) ∗ ▷ (∀ c',
      abiResources 0 (c.pack ∅).1 ∗ ready S che ac ∗
      ownsPred (AcFields ac avctx er ps) ∗ ownsPred Rc -∗
      WP (k c') @ Stuckness.NotStuck; E {{ Φ }}) ⊢
      WP (Host.Expr.native (.run c) k) @ Stuckness.NotStuck; E {{ Φ }} := by
  iintro ⟨HP, HK⟩
  iunfold ownsPred at HP
  icases HP with ⟨%p, %hp, Hp⟩
  have hcall : ConfigCall che ac (c.pack p).1 := ⟨hc.args⟩
  have hcpu : CPU.ofMachine ((c.pack p).1, entry "ff_aac_sbr_config_usac") = c := by
    rw [← hpc]
    exact CPU.ofMachine_pack c p
  have hspec := wp_config (GF := GF) S C hcode hcall hp hne k (E := E) (Φ := Φ)
  simp only [hcpu] at hspec
  iapply hspec
  simp only [CPU.pack, abiResources]
  iframe Hp
  iexact HK

end SbrClient.SbrAPI
