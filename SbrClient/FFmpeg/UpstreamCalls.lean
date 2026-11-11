import Kraken.X64.Examples.Sbr.SessionBin.SApply
import Kraken.X64.Examples.Sbr.SessionBin.SConfig

/-! Exact source excerpts from zrlk/kraken commit b60a6f97373dbb537d0576fd40b8b7c2520b4de3:
TopDefs.lean (element splitting) and TopCalls.lean (separation helpers and
config/apply wrappers). Generated/checked by scripts/extract-public-calls.py.
The original instruction and session proofs are imported unchanged. Unused
parser imports and wrappers are omitted; no theorem body is adapted. -/
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.ParseModel hiding Live
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse
open Kraken.Examples.Sbr.SessionBin
namespace SbrClient.Upstream
section
theorem tAt_arg0 (che ac : BitVec 64) : arg0 (tAt che ac) = ac := by
  simp [tAt, arg0]

theorem tAt_arg1 (che ac : BitVec 64) : arg1 (tAt che ac) = che := by
  simp [tAt, arg1]

variable [CodeEnv]

/-! ## The element -/

/-- `SessW` is the element and the caller's `ac` fields. -/
theorem sessW_split (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (t : MachineData) : SessW e vs vp σ t = (ElemAt e vs vp σ (arg1 t) (arg0 t)
      ⋆ AcFields (arg0 t) σ.1.avctx σ.1.extRate σ.1.ps) := by
  have hs : sbrA (tAt (arg1 t) (arg0 t)) = sbrA t := by simp only [sbrA, tAt_arg1]
  have h1 : PsRest σ.1 (tAt (arg1 t) (arg0 t)) = PsRest σ.1 t := by unfold PsRest; rw [hs]
  have h2 : ArrW (tAt (arg1 t) (arg0 t)) = ArrW t := by unfold ArrW; rw [hs]
  have h3 : DspW e (tAt (arg1 t) (arg0 t)) = DspW e t := by unfold DspW; rw [hs]
  have h4 : FnW e σ.1 (tAt (arg1 t) (arg0 t)) = FnW e σ.1 t := by unfold FnW; rw [hs]
  unfold SessW ElemAt AcW AcFields
  simp only [h1, h2, h3, h4, hs]
  generalize DecExt.SbrF (toDS σ) (sbrA t) = A
  generalize PsRest σ.1 t = B
  generalize ArrW t = C
  generalize DspW e t = D
  generalize FnW e σ.1 t = F
  generalize CstW ⋆ PStat vs vp = G
  simp only [c8]
  generalize Int.toBytes 8 σ.1.avctx.toInt =@ (arg0 t + 0x8#64) = X1
  generalize Int.toBytes 8 σ.1.fdsp.toInt =@ (arg0 t + 0x2550#64) = X2
  generalize cell4 (arg0 t + 0x57f4#64) σ.1.extRate = X3
  generalize cell4 (arg0 t + 0x5800#64) σ.1.ps = X4
  ac_rfl

/-- The element does not read the caller's `ac` fields or memory. -/
theorem elemAt_frame (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    (R : Mem 64 → Prop) (a : BitVec 64) (er ps : BitVec 32) (che ac : BitVec 64) :
    ElemAt e vs vp ({ σ.1 with R := R, avctx := a, extRate := er, ps := ps }, σ.2) che ac
      = ElemAt e vs vp σ che ac := rfl

/-! ## Runs -/

/-! ## Stack reservations -/

/-! ## The calls' objects and obligations -/

end
section
theorem sep_mono3 {A B P Q C : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ (B ⋆ (P ⋆ C))) m) : (A ⋆ (B ⋆ (Q ⋆ C))) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, p, q, hu3, hi3, hp, hq⟩ := hm
  exact ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, p, q, hu3, hi3, h p hp, hq⟩

theorem sep_ex3 {α : Type} {A B C : Mem 64 → Prop} {P : α → Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ (B ⋆ ((fun m => ∃ x, P x m) ⋆ C))) m) : ∃ x, (A ⋆ (B ⋆ (P x ⋆ C))) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, p, q, hu3, hi3, ⟨x, hp⟩, hq⟩ := hm
  exact ⟨x, a, b, hu, hi, ha, c, d, hu2, hi2, hc, p, q, hu3, hi3, hp, hq⟩

theorem sep_pure3 {φ : Prop} {A B X C : Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ (B ⋆ ((fun m => φ ∧ X m) ⋆ C))) m) : φ ∧ (A ⋆ (B ⋆ (X ⋆ C))) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, p, q, hu3, hi3, ⟨hφ, hp⟩, hq⟩ := hm
  exact ⟨hφ, a, b, hu, hi, ha, c, d, hu2, hi2, hc, p, q, hu3, hi3, hp, hq⟩

theorem sep_eq3 {A B P Q : Mem 64 → Prop} (h : P = Q) {m : Mem 64}
    (hm : (A ⋆ (B ⋆ P)) m) : (A ⋆ (B ⋆ Q)) m := h ▸ hm

/-- The caller's frame step: the `ac` fields at the caller's values. -/
def withAc (σ : SV) (a : BitVec 64) (er ps : BitVec 32) : SV :=
  ({ σ.1 with avctx := a, extRate := er, ps := ps }, σ.2)

theorem sreach_withAc {i : InitIn} {σ : SV} {ok : Bool} (h : SReach (σInit i) σ ok)
    (a : BitVec 64) (er ps : BitVec 32) : SReach (σInit i) (withAc σ a er ps) ok :=
  SReach.step .frame h (fun h => nomatch h) (fun _ => rfl) (Step.frame ok rfl)

variable [CodeEnv]

/-! ## Opening and closing `Live` -/

/-- The element at the caller's `ac` fields is `SessW`. -/
theorem sessW_withAc (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (σ : SV)
    {che ac : BitVec 64} (a : BitVec 64) (er ps : BitVec 32) {t : MachineData}
    (h0 : arg0 t = ac) (h1 : arg1 t = che) :
    SessW e vs vp (withAc σ a er ps) t = (ElemAt e vs vp σ che ac ⋆ AcFields ac a er ps) := by
  rw [sessW_split, h0, h1]; rfl

/-- `Live` opened at a call: the values, the environment, the memory with the gap. -/
theorem live_open {S : Setup} {che ac : BitVec 64} {A B C : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (Live S che ac ⋆ C))) m) : ∃ (ok : Bool) (e : Env) (i : InitIn) (σ : SV),
      EnvOK S e ∧ SReach (σInit i) σ ok
      ∧ (A ⋆ (B ⋆ ((ElemAt e S.vs S.vp σ che ac ⋆ Init.InitGap che) ⋆ C))) m := by
  unfold Live at h
  obtain ⟨ok, h⟩ := sep_ex3 h
  unfold ElemState at h
  obtain ⟨e, h⟩ := sep_ex3 h
  obtain ⟨i, h⟩ := sep_ex3 h
  obtain ⟨σ, h⟩ := sep_ex3 h
  obtain ⟨he, h⟩ := sep_pure3 h
  obtain ⟨hσ, h⟩ := sep_pure3 h
  exact ⟨ok, e, i, σ, he, hσ, h⟩

/-- `ElemState` opened at a call. -/
theorem elem_open {S : Setup} {che ac : BitVec 64} {ok : Bool} {A B C : Mem 64 → Prop}
    {m : Mem 64} (h : (A ⋆ (B ⋆ (ElemState S che ac ok ⋆ C))) m) :
    ∃ (e : Env) (i : InitIn) (σ : SV), EnvOK S e ∧ SReach (σInit i) σ ok
      ∧ (A ⋆ (B ⋆ ((ElemAt e S.vs S.vp σ che ac ⋆ Init.InitGap che) ⋆ C))) m := by
  unfold ElemState at h
  obtain ⟨e, h⟩ := sep_ex3 h
  obtain ⟨i, h⟩ := sep_ex3 h
  obtain ⟨σ, h⟩ := sep_ex3 h
  obtain ⟨he, h⟩ := sep_pure3 h
  obtain ⟨hσ, h⟩ := sep_pure3 h
  exact ⟨e, i, σ, he, hσ, h⟩

/-- Closing `ElemState` after a call. -/
theorem elem_close {S : Setup} {che ac : BitVec 64} {ok : Bool} {e : Env} {i : InitIn}
    {σ : SV} (he : EnvOK S e) (hσ : SReach (σInit i) σ ok) {A B C : Mem 64 → Prop}
    {m : Mem 64} (h : (A ⋆ (B ⋆ ((ElemAt e S.vs S.vp σ che ac ⋆ Init.InitGap che) ⋆ C))) m) :
    (A ⋆ (B ⋆ (ElemState S che ac ok ⋆ C))) m :=
  sep_mono3 (fun _ hm => ⟨e, i, σ, he, hσ, hm⟩) h

theorem ready_live {S : Setup} {che ac : BitVec 64} {A B C : Mem 64 → Prop} {m : Mem 64}
    {ok : Bool} (h : (A ⋆ (B ⋆ (ElemState S che ac ok ⋆ C))) m) :
    (A ⋆ (B ⋆ (Live S che ac ⋆ C))) m :=
  sep_mono3 (fun _ hm => ⟨ok, hm⟩) h

/-! ## Memory regroupings -/

omit [CodeEnv] in
theorem elemOK_elemC {che : BitVec 64} {t : MachineData} (h1 : arg1 t = che) (h : ElemOK che) :
    ElemC t := by
  simp only [ElemC, sbrA, h1]; exact h


omit [CodeEnv] in
theorem cfg_mem (E G F Rc : Mem 64 → Prop) : ((E ⋆ G) ⋆ (F ⋆ Rc)) = ((E ⋆ F) ⋆ (G ⋆ Rc)) := by
  ac_rfl

omit [CodeEnv] in
theorem out_split (t : MachineData) {n : Nat} (hn : n ≤ 8192) :
    OutBufs t = (Blocks [(arg3 t, n), (arg4 t, n)]
      ⋆ ((8192 - n) ?@ (arg3 t + .ofNat 64 n) ⋆ (8192 - n) ?@ (arg4 t + .ofNat 64 n))) := by
  unfold OutBufs
  simp only [Blocks]
  rw [Block.split_at (arg3 t) 8192 n hn (by decide), Block.split_at (arg4 t) 8192 n hn (by decide)]
  generalize n ?@ arg3 t = X1
  generalize n ?@ arg4 t = X2
  generalize (8192 - n) ?@ (arg3 t + .ofNat 64 n) = X3
  generalize (8192 - n) ?@ (arg4 t + .ofNat 64 n) = X4
  ac_rfl

omit [CodeEnv] in
theorem apply_mem (E G F W T Rc : Mem 64 → Prop) :
    ((E ⋆ G) ⋆ (F ⋆ ((W ⋆ T) ⋆ Rc))) = ((E ⋆ F) ⋆ (W ⋆ (T ⋆ (G ⋆ Rc)))) := by
  ac_rfl


theorem config_top (B : SessPlaced) (S : Setup)
    {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hc : ConfigCall che ac t)
    (hm : CallPre 0 (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t) :
    Ends "ff_aac_sbr_config_usac" t ra (fun s => ret32 s = 0#32
      ∧ CallPost 0 (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ Rc)) ra t s) NoStops := by
  obtain ⟨h0, h1⟩ := hc.args
  obtain ⟨ok, e, ii, σ, ⟨has, hsl⟩, hσ, hm⟩ := live_open hm
  have hfr : ConfigFrame e S.vs S.vp (withAc σ avctx er ps) (Init.InitGap che ⋆ Rc) ra t :=
    { own := by
        refine sep_eq3 ?_ hm
        rw [sessW_withAc e S.vs S.vp σ avctx er ps h0 h1]
        exact cfg_mem _ _ _ Rc }
  refine eventually_weaken _ _ _ _ (fun st hr => Or.inl ?_)
    (session_config B e S.vs S.vp ii (sreach_withAc hσ avctx er ps) hfr)
  obtain ⟨hra, σ', hσ', ⟨hav, her, hps⟩, hrax, c1, c2, c3, hm'⟩ := hr
  refine ⟨hra, hrax, c1, c2, c3, ?_⟩
  simp only [withAc] at hav her hps
  rw [sessW_split, h0, h1, hav, her, hps] at hm'
  exact elem_close ⟨has, hsl⟩ hσ' (sep_eq3 (cfg_mem _ _ _ Rc).symm hm')

/-- `ff_aac_sbr_apply` on a ready element. -/
theorem apply_top (B : SessPlaced) (S : Setup) (hk : 0x9d0 + S.k ≤ 2 ^ 32)
    {che ac avctx : BitVec 64} {er ps : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hc : ApplyCall che ac t)
    (hm : CallPre (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t) :
    Ends "ff_aac_sbr_apply" t ra (fun s => CallPost (applyStack S.k)
      (Ready S che ac ⋆ (AcFields ac avctx er ps ⋆ (OutBufs t ⋆ Rc))) ra t s) NoStops := by
  obtain ⟨h0, h1⟩ := hc.args
  obtain ⟨e, ii, σ, ⟨has, hsl⟩, hσ, hm⟩ := elem_open hm
  have hn : 8192 >>> dsN (withAc σ avctx er ps).1 ≤ 8192 := Nat.shiftRight_le _ _
  rw [out_split t hn] at hm
  have hfr : ApplyFrame S.k e S.vs S.vp (withAc σ avctx er ps)
      (_ ⋆ (Init.InitGap che ⋆ Rc)) ra t :=
    { own := by
        refine sep_eq3 ?_ hm
        rw [sessW_withAc e S.vs S.vp σ avctx er ps h0 h1]
        exact apply_mem _ _ _ _ _ Rc
      elem := elemOK_elemC h1 hc.elem
      align := hc.align
      out := hc.out }
  refine eventually_weaken _ _ _ _ (fun st hr => Or.inl ?_)
    (session_apply B S.k (by omega) e S.vs S.vp S.pw S.lg hsl has ii
      (sreach_withAc hσ avctx er ps) hfr)
  obtain ⟨hra, σ', hσ', ⟨hav, her, hps⟩, c1, c2, c3, hm'⟩ := hr
  refine ⟨hra, c1, c2, c3, ?_⟩
  simp only [withAc] at hav her hps
  rw [sessW_split, h0, h1, hav, her, hps] at hm'
  have hm'' := sep_eq3 (apply_mem _ _ _ _ _ Rc).symm hm'
  unfold OutW at hm''
  rw [← out_split t hn] at hm''
  exact elem_close ⟨has, hsl⟩ hσ' hm''

end
end SbrClient.Upstream
