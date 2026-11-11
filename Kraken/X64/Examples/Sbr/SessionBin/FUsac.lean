import Kraken.X64.Examples.Sbr.SessionBin.BridgeU
import Kraken.X64.Examples.Sbr.SessionBin.FCfg

/-!
# Footprint conversion for `ff_aac_sbr_decode_usac_data` (F-usac)

`fUsac`: the element `SessW` with the call's objects (`UsacObj`: the reader `*gb`, the bitstream,
`ue->sbr`, the caller's rest) is `Usac.UF` with a frame. The frame is `Carve` (the bytes of
`X_low` that `fCfg` lends to `UF`, here unused) and `QR` (what `SessW` owns and `UF` does not).
`RdU`'s bitstream and `ue->sbr` come from `UsacObj`; `ceil_log2`, the jump table, `e.Ext` and the
other callee state `OthU` from the element's static data. Back, `inter_tes` (raw in `UF`) gets
some value, and the fields outside `UF` that the frame reads are kept (`UKeep`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Usac

namespace Kraken.Examples.Sbr.SessionBin

variable [CodeEnv]

omit [CodeEnv] in
/-- An item in front of the caller's rest moves out of `QR`. -/
theorem fu_perm_qr (A B C D E F G H X R : Mem 64 → Prop) :
    A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ (G ⋆ (H ⋆ (X ⋆ R))))))))
      = X ⋆ (A ⋆ (B ⋆ (C ⋆ (D ⋆ (E ⋆ (F ⋆ (G ⋆ (H ⋆ R)))))))) := by
  ac_rfl

theorem fu_qr (e : Env) (x : Args) (t : MachineData) (X R : Mem 64 → Prop) :
    QR e x t (X ⋆ R) = X ⋆ QR e x t R :=
  fu_perm_qr _ _ _ _ _ _ _ _ _ _

theorem fu_qr_obj (e : Env) (x : Args) (t : MachineData) (q : UQ) (i : BitVec 32) :
    QR e x t (UsacObj q i)
      = GbU q i ⋆ (Blocks [(q.buf, q.L)] ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ QR e x t q.R)) := by
  rw [UsacObj, fu_qr, fu_qr, fu_qr]

omit [CodeEnv] in
theorem fu_perm (Z SH TW D0 R0 D1 R1 Ac Gb Bk Ce Jt Uv Ex Cs Bw Vw Pt Cv Q : Mem 64 → Prop) :
    (Z ⋆ SH) ⋆ (TW ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ (Ac ⋆ (Gb ⋆ ((Bk ⋆ Ce)
      ⋆ (Jt ⋆ (Uv ⋆ (Ex ⋆ (Cs ⋆ (Bw ⋆ (Vw ⋆ Pt)))))))))))))) ⋆ (Cv ⋆ Q)
    = Z ⋆ ((SH ⋆ (TW ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ Ac))))))
      ⋆ (Cv ⋆ ((Jt ⋆ (Ce ⋆ (Ex ⋆ (Vw ⋆ (Pt ⋆ (Cs ⋆ Bw))))))
      ⋆ (Gb ⋆ (Bk ⋆ (Uv ⋆ Q)))))) := by
  ac_rfl

/-- The frame of the call. -/
abbrev RU (e : Env) (x : Args) (t : MachineData) (Rq : Mem 64 → Prop) : Mem 64 → Prop :=
  Carve (sbrA t) ⋆ QR e x t Rq

/-- `UF` with the frame `RU`, in the shape of `fc_sess` with the call's objects. -/
theorem fu_uf (e : Env) (vs : Nat → Vlc.VlcTab) (vp : Nat → Ps.VlcTab) (x : Args)
    (t : MachineData) (Rq : Mem 64 → Prop) (ue g buf : BitVec 64) (p8 : BitVec 32) (L : Nat)
    (uev : List UInt8) (E O : Mem 64 → Prop) (st : USt) :
    UF (uq e vs vp ⟨Rq, arg0 t, arg1 t, ue, g, buf, p8, L, uev, E, O⟩ (RU e x t Rq)) st
      ⋆ RU e x t Rq
      = 4 ?@ (sbrA t + 0x14#64)
        ⋆ (UCore (arg1 t) (arg0 t) st.x st.u st.amp st.h.lb st.sp
        ⋆ (Carve (sbrA t) ⋆ (Stat e vs vp
          ⋆ QR e x t (UsacObj ⟨Rq, arg0 t, arg1 t, ue, g, buf, p8, L, uev, E, O⟩ st.i)))) := by
  rw [UF, fc_shw, RdU, fu_qr_obj]
  simp only [uq, OthU, Stat, Oth, UCore, RU]
  exact fu_perm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **F-usac.** -/
theorem fUsac : FUsac := by
  intro e vs vp σ q i t m ha hc h
  obtain ⟨Rq, a, c, ue, g, buf, p8, L, uev, E, O⟩ := q
  dsimp only at ha hc
  subst ha hc
  rw [fc_sess] at h
  refine ⟨RU e σ.1 t Rq, ?_, ?_⟩
  · rw [fu_uf]
    exact fa_cell4_blk h
  · intro st m' hk hsp h3
    rw [fu_uf] at h3
    obtain ⟨it, h4⟩ := fa_blk_cell4 h3
    refine ⟨it, ?_⟩
    rw [fc_sess]
    show (cell4 (sbrA t + 0x14#64) it
        ⋆ (UCore (arg1 t) (arg0 t) st.x st.u st.amp st.h.lb (spBytes (withSp st.x st.sp))
        ⋆ (Carve (sbrA t) ⋆ (Stat e vs vp ⋆ QR e (withSp st.x st.sp) t
          (UsacObj ⟨Rq, arg0 t, arg1 t, ue, g, buf, p8, L, uev, E, O⟩ st.i))))) m'
    rw [spBytes_withSp _ hsp.1, fc_qr e σ.1 st.x st.sp t _ hk]
    exact h4

end Kraken.Examples.Sbr.SessionBin
