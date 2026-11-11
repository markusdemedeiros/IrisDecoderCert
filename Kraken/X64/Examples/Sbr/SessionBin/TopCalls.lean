import Kraken.X64.Examples.Sbr.SessionBin.TopDefs
import Kraken.X64.Examples.Sbr.SessionBin.Main

/-!
# A decoding session over the binary: the four calls in the headline's terms

Each entry point restated with `Live`/`Ready`, `AcFields` and the plain call obligations
(`TopDefs`), from the session theorems `session_dec`, `session_usac`, `session_config`,
`session_apply`. The proofs open `Live` (the reachable values `σ`), apply the caller's frame step
(the `ac` fields as the caller holds them), and close the result again.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Separation helpers -/

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
theorem dec_mem (E G F : Mem 64 → Prop) (b : Rdr) (a : BitVec 64) (Rc : Mem 64 → Prop)
    (i : BitVec 32) (t : MachineData) :
    ((E ⋆ G) ⋆ (F ⋆ DecObj b a Rc i t)) = ((E ⋆ F) ⋆ DecObj b a (G ⋆ Rc) i t) := by
  unfold DecObj
  generalize RdrW (arg2 t) b i = X1
  generalize Blocks [(b.r.buf, b.r.L)] = X2
  generalize AcX (arg0 t) a = X3
  ac_rfl

omit [CodeEnv] in
theorem usac_mem (E G F : Mem 64 → Prop) (u : UsacIn) (che ac : BitVec 64)
    (Rc : Mem 64 → Prop) (i : BitVec 32) :
    ((E ⋆ G) ⋆ (F ⋆ UsacObjects u che ac Rc i)) = ((E ⋆ F) ⋆ UsacObj (u.q che ac (G ⋆ Rc)) i) := by
  have hg : Usac.GbU (u.q che ac (G ⋆ Rc)) i = Usac.GbU (u.q che ac Rc) i := rfl
  unfold UsacObjects UsacObj
  rw [hg]
  show _ = (_ ⋆ _) ⋆ (_ ⋆ (_ ⋆ (_ ⋆ (G ⋆ Rc))))
  simp only [UsacIn.q]
  generalize Usac.GbU (u.q che ac Rc) i = X1
  generalize Blocks [(u.buf, u.L)] = X2
  generalize u.uev =@ (u.ue + 0xc#64) = X3
  ac_rfl

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

/-! ## The four calls -/

/-- `ff_aac_sbr_decode_extension` on a live element. -/
theorem dec_top (B : SessPlaced) (S : Setup) (hk : 0x9d0 + S.k ≤ 2 ^ 32)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {b : Rdr} {i : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hc : DecCall che ac b i t)
    (hm : CallPre (decStack S.k)
      (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ DecObj b avctx Rc i t)) ra t) :
    Ends "ff_aac_sbr_decode_extension" t ra (fun s => ∃ (i' : BitVec 32) (er' : BitVec 32),
      i'.toNat ≤ b.r.p8.toNat ∧ ret32 s = (arg4 t).setWidth 32
      ∧ CallPost (decStack S.k)
        (Ready S che ac ⋆ (AcFields ac avctx er' ps ⋆ DecObj b avctx Rc i' t)) ra t s) Traps := by
  obtain ⟨h0, h1⟩ := hc.args
  obtain ⟨ok, e, ii, σ, ⟨has, hsl⟩, hσ, hm⟩ := live_open hm
  have hfr : DecFrame (decKc S.k) e S.vs S.vp (withAc σ avctx er ps) b i
      (Init.InitGap che ⋆ Rc) ra t :=
    { own := by
        refine sep_eq3 ?_ hm
        rw [sessW_withAc e S.vs S.vp σ avctx er ps h0 h1]
        exact dec_mem _ _ _ b avctx Rc i t
      rd := hc.rd
      elem := elemOK_elemC h1 hc.elem
      align := hc.align }
  refine eventually_weaken _ _ _ _ (fun st h => h.imp (fun hr => ?_) id)
    (session_dec B S.k hk e S.vs S.vp S.pw S.lg has ii (sreach_withAc hσ avctx er ps) hfr)
  obtain ⟨hra, σ', i', hσ', ⟨hav, hps⟩, hi', hrax, c1, c2, c3, hm'⟩ := hr
  refine ⟨hra, i', σ'.1.extRate, hi', hrax, c1, c2, c3, ?_⟩
  simp only [withAc] at hav hps
  rw [sessW_split, h0, h1, hav, hps] at hm'
  exact elem_close ⟨has, hsl⟩ hσ' (sep_eq3 (dec_mem _ _ _ b avctx Rc i' t).symm hm')

/-- `ff_aac_sbr_decode_usac_data` on a live element. -/
theorem usac_top (B : SessPlaced) (S : Setup) (hk : 0x9d0 + S.k ≤ 2 ^ 32)
    {che ac avctx : BitVec 64} {er ps : BitVec 32} {u : UsacIn} {i : BitVec 32}
    {Rc : Mem 64 → Prop} {ra : Int64} {t : MachineData} (hc : UsacCall che ac u i t)
    (hm : CallPre (usacStack S.k)
      (Live S che ac ⋆ (AcFields ac avctx er ps ⋆ UsacObjects u che ac Rc i)) ra t) :
    Ends "ff_aac_sbr_decode_usac_data" t ra (fun s => ∃ i' : BitVec 32,
      i'.toNat ≤ u.p8.toNat
      ∧ CallPost (usacStack S.k) (ElemState S che ac (decide (ret32 s = 0#32))
        ⋆ (AcFields ac avctx er ps ⋆ UsacObjects u che ac Rc i')) ra t s) Traps := by
  obtain ⟨h0, h1, h2, h3⟩ := hc.args
  obtain ⟨ok, e, ii, σ, ⟨has, hsl⟩, hσ, hm⟩ := live_open hm
  have hfr : UsacFrame (usacK S.k) e S.vs S.vp (withAc σ avctx er ps)
      (u.q che ac (Init.InitGap che ⋆ Rc)) i ra t :=
    { own := by
        refine sep_eq3 ?_ hm
        rw [sessW_withAc e S.vs S.vp σ avctx er ps h0 h1]
        exact usac_mem _ _ _ u che ac Rc i
      args := ⟨h0, h1, h2, h3⟩
      rd := ⟨hc.rd.1, hc.rd.2⟩
      ue := hc.ue
      uev3 := hc.uev3
      elem := elemOK_elemC h1 hc.elem
      align := hc.align }
  refine eventually_weaken _ _ _ _ (fun st h => h.imp (fun hr => ?_) id)
    (session_usac B S.k hk e S.vs S.vp S.pw S.lg has ii false (sreach_withAc hσ avctx er ps) hfr)
  obtain ⟨hra, σ', i', hσ', ⟨hav, her, hps⟩, hi', c1, c2, c3, hm'⟩ := hr
  refine ⟨hra, i', hi', c1, c2, c3, ?_⟩
  simp only [withAc] at hav her hps
  rw [sessW_split, h0, h1, hav, her, hps] at hm'
  exact elem_close ⟨has, hsl⟩ hσ' (sep_eq3 (usac_mem _ _ _ u che ac Rc i').symm hm')

/-- `ff_aac_sbr_config_usac` on a live element. -/
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

end Kraken.Examples.Sbr.SessionBin
