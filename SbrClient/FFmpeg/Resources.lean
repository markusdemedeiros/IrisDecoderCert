import SbrClient.Machine.Resources
import Kraken.X64.Examples.Sbr.SessionSpec

/-! The public SBR predicates denote ordinary, exclusive Iris byte ownership.
In particular, returning from apply makes the two output buffers independently
transferable, while retaining the decoder and its reusable stack reservation. -/
noncomputable section
namespace SbrClient.SbrAPI
open Kraken Kraken.SysV Mem Kraken.Examples.Sbr Kraken.Examples.Sbr.SessionBin
open Iris Iris.BI Iris.Std Iris.ProofMode

variable [CodeEnv]
variable {GF : BundledGFunctors} [genHeapGS (BitVec 64) UInt8 GF ByteMap]
local bi (IProp GF)

def live (S : Setup) (che ac : BitVec 64) : IProp GF := ownsPred (Live S che ac)
def ready (S : Setup) (che ac : BitVec 64) : IProp GF := ownsPred (Ready S che ac)
def outputs (t : MachineData) : IProp GF := ownsPred (OutBufs t)
def buffer (a : BitVec 64) : IProp GF := ownsPred (Block a 8192)
def abiResources (d : Nat) (t : MachineData) : IProp GF :=
  iprop(ownsPred (8 ?@ (t.regs.get64 .rsp)) ∗ ownsPred (Reserve d (t.regs.get64 .rsp)))

omit [CodeEnv] in
theorem outputs_split (t : MachineData) :
    outputs (GF := GF) t ⊢ buffer (arg3 t) ∗ buffer (arg4 t) :=
  ownsPred_sep

omit [CodeEnv] in
theorem outputs_join (t : MachineData) :
    buffer (GF := GF) (arg3 t) ∗ buffer (arg4 t) ⊢ outputs t :=
  ownsPred_sep_intro

omit [CodeEnv] in
/-- Recover all resources from the original SysV postcondition. Register
restoration stays a pure fact in `CallPost`; bytes become transferable Iris
resources, with no semantic reinterpretation of the external predicate. -/
theorem callPost_resources {d : Nat} {R : Mem 64 → Prop} {ra : Int64}
    {t s : MachineData} (h : CallPost d R ra t s) :
    owns (GF := GF) s.dmem ⊢ abiResources d t ∗ ownsPred R := by
  have hm := h.2.2.2
  iintro Hm
  ihave HP : ownsPred (8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve d (t.regs.get64 .rsp) ⋆ R)) $$ [Hm]
  · unfold ownsPred
    iexists s.dmem
    iframe Hm
    ipureintro
    exact hm
  icases ownsPred_sep $$ HP with ⟨Hret, Hrest⟩
  icases ownsPred_sep $$ Hrest with ⟨Hstack, HR⟩
  iunfold abiResources
  iframe

theorem apply_resources (S : Setup) {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t s : MachineData}
    (h : CallPost (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t s) :
    owns (GF := GF) s.dmem ⊢
      abiResources (applyStack S.k) t ∗ ready S che ac ∗
      ownsPred (AcFields ac avctx er ps) ∗ outputs t ∗ ownsPred Rc := by
  iintro Hm
  icases callPost_resources h $$ Hm with ⟨Habi, HR⟩
  icases ownsPred_sep $$ HR with ⟨Hready, HR⟩
  icases ownsPred_sep $$ HR with ⟨Hac, HR⟩
  icases ownsPred_sep $$ HR with ⟨Hout, HR⟩
  iunfold ready
  iunfold outputs
  iframe

theorem config_resources (S : Setup) {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t s : MachineData}
    (h : CallPost 0 (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t s) :
    owns (GF := GF) s.dmem ⊢
      abiResources 0 t ∗ ready S che ac ∗ ownsPred (AcFields ac avctx er ps) ∗ ownsPred Rc := by
  iintro Hm
  icases callPost_resources h $$ Hm with ⟨Habi, HR⟩
  icases ownsPred_sep $$ HR with ⟨Hready, HR⟩
  icases ownsPred_sep $$ HR with ⟨Hac, HR⟩
  iunfold ready
  iframe

end SbrClient.SbrAPI
