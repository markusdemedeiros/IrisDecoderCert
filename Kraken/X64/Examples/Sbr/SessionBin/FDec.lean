import Kraken.X64.Examples.Sbr.SessionBin.Bridge
import Kraken.X64.Examples.Sbr.SessionBin.Inv
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueN

/-!
# A decoding session over the binary: F-dec

`fDecPre`: at a call of `ff_aac_sbr_decode_extension`, the element `SessW` and the call's objects
`DecObj` are `DecF` (with `Ext = ExtD`, for some value `sr` of `oc[1].m4ac.sample_rate`, raw in
`AcX`) and `DecRest`. The regrouping: `FnW` is `FnWx ⋆ e.Ext`; `AcW` gives `ac->avctx` (`AvW`),
`ac->fdsp` (to `DecRest`) and the `AcF` cells `ext_sample_rate`, `ps`; `AcX` the other `AcF`
cells; `PStat` gives the jump table, `ceil_log2` (to `BufW`) and the tables of `ExtD`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Session Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## Existentials through `⋆` -/

theorem exL {α : Type} (P : α → Mem 64 → Prop) (K : Mem 64 → Prop) :
    ((fun m => ∃ v, P v m) ⋆ K) = fun m => ∃ v, (P v ⋆ K) m := by
  funext m; apply propext; constructor
  · rintro ⟨m1, m2, hd, hu, ⟨v, hv⟩, hK⟩; exact ⟨v, m1, m2, hd, hu, hv, hK⟩
  · rintro ⟨v, m1, m2, hd, hu, hv, hK⟩; exact ⟨m1, m2, hd, hu, ⟨v, hv⟩, hK⟩

theorem exR {α : Type} (P : α → Mem 64 → Prop) (K : Mem 64 → Prop) :
    (K ⋆ (fun m => ∃ v, P v m)) = fun m => ∃ v, (K ⋆ P v) m := by
  funext m; apply propext; constructor
  · rintro ⟨m1, m2, hd, hu, hK, ⟨v, hv⟩⟩; exact ⟨v, m1, m2, hd, hu, hK, hv⟩
  · rintro ⟨v, m1, m2, hd, hu, hK, hv⟩; exact ⟨m1, m2, hd, hu, hK, ⟨v, hv⟩⟩

/-- Four raw bytes are a 32-bit cell of some value. -/
theorem blk4_eq (a : BitVec 64) : (4 ?@ a) = fun m => ∃ v : BitVec 32, cell4 a v m := by
  funext m; apply propext; constructor
  · exact DecExt.blk4_cell
  · rintro ⟨v, hv⟩; exact DecExt.cell4_blk hv

theorem toDS_a (σ : SV) : (toDS σ).a = σ.1 := rfl

/-- The F-dec regrouping on abstract cells (`ac_rfl` on the concrete cells recurses too deep). -/
theorem fdec_perm (S F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 F17 F18 Ext av fd er ps
    CW JT cl VW PT CR bw r1 r2 r3 r4 r5 L sr a4 b4 Rc : Mem 64 → Prop) :
    (S ⋆ (F1 ⋆ (F2 ⋆ (F3 ⋆ (F4 ⋆ (F5 ⋆ (F6 ⋆ (F7 ⋆ (F8 ⋆ (F9 ⋆ (F10 ⋆ (F11 ⋆ (F12 ⋆ (F13 ⋆ (F14 ⋆
      (F15 ⋆ (F16 ⋆ (F17 ⋆ (F18 ⋆ (Ext ⋆ (av ⋆ (fd ⋆ (er ⋆ (ps ⋆ (CW ⋆ (JT ⋆ (cl ⋆ (VW ⋆ (PT ⋆ (CR ⋆
      (bw ⋆ (r1 ⋆ (r2 ⋆ (r3 ⋆ (r4 ⋆ (r5 ⋆ (L ⋆ (sr ⋆ (a4 ⋆ (b4 ⋆
      Rc))))))))))))))))))))))))))))))))))))))))
    = (S ⋆ (r1 ⋆ (r2 ⋆ (r3 ⋆ (r4 ⋆ (r5 ⋆ (av ⋆ (sr ⋆ (er ⋆ (ps ⋆ (a4 ⋆ (b4 ⋆ (L ⋆ (cl ⋆ (JT ⋆ (CR ⋆
      (bw ⋆ (VW ⋆ (PT ⋆ (Ext ⋆ (F1 ⋆ (F2 ⋆ (F3 ⋆ (F4 ⋆ (F5 ⋆ (F6 ⋆ (F7 ⋆ (F8 ⋆ (F9 ⋆ (F10 ⋆ (F11 ⋆
      (F12 ⋆ (F13 ⋆ (F14 ⋆ (F15 ⋆ (F16 ⋆ (F17 ⋆ (F18 ⋆ (fd ⋆ (CW ⋆
      Rc)))))))))))))))))))))))))))))))))))))))) := by
  ac_rfl

variable [CodeEnv]

/-- **F-dec, at the call.** -/
theorem fDecPre : FDecPre := by
  intro e vs vp σ b i Rc t m h
  simp only [SessW, DecObj, AcX] at h
  rw [blk4_eq (arg0 t + 0x57e0#64)] at h
  simp only [exL, exR] at h
  obtain ⟨sr, h⟩ := h
  refine ⟨sr, ?_⟩
  simp only [PStat, FnW, AcW, RdrW, Blocks, Apply.c8] at h
  simp only [DecExt.DecF, DecExt.GhW, xaOf, DecExt.AvW, DecExt.AcF, DecExt.BufW, ExtD, DecRest,
    FnWx, Blocks, Apply.c8]
  simp only [toDS_a, Std.ExtHashMap.sep_assoc] at h ⊢
  rw [fdec_perm] at h
  exact h

omit [CodeEnv] in
/-- `SbrF` does not read `spLo`/`spHi` nor `Hid.start`/`Hid.xover`; the bytes read back. -/
theorem sbrF_ofDS {d : DecExt.DS} (hl : d.sp.length = 6) (s : BitVec 64) :
    DecExt.SbrF (toDS (ofDS d)) s = DecExt.SbrF d s := by
  show DecExt.SbrF ⟨withSp d.a d.sp, hidOf (ofDS d), d.usac, d.amp, spBytes (withSp d.a d.sp),
    d.it⟩ s = _
  rw [spBytes_withSp _ hl]
  rfl

omit [CodeEnv] in
theorem psRest_withSp (x : Args) (sp : List UInt8) (t : MachineData) :
    PsRest (withSp x sp) t = PsRest x t := rfl

omit [CodeEnv] in
theorem psRest_congr {x y : Args} (h : y.psh = x.psh) (t : MachineData) :
    PsRest x t = PsRest y t := by
  unfold PsRest; rw [h]

/-- **F-dec, at the return.** -/
theorem fDecPost : FDecPost := by
  intro e vs vp x d b i sr R Rc t m hk hl h
  obtain ⟨-, hfd, hana, hsyn, hpsh, -, -⟩ := hk
  simp only [SessW, DecObj, AcX]
  rw [sbrF_ofDS hl, blk4_eq (arg0 t + 0x57e0#64)]
  simp only [exL, exR]
  refine ⟨sr, ?_⟩
  simp only [PStat, FnW, AcW, RdrW, Blocks, Apply.c8, ofDS, psRest_withSp]
  simp only [withSp]
  simp only [DecExt.DecF, DecExt.GhW, xaOf, DecExt.AvW, DecExt.AcF, DecExt.BufW, ExtD, DecRest,
    FnWx, Blocks, Apply.c8] at h
  rw [← hfd, ← hana, ← hsyn, psRest_congr hpsh] at h
  simp only [Std.ExtHashMap.sep_assoc] at h ⊢
  rw [fdec_perm]
  exact h

end Kraken.Examples.Sbr.SessionBin
