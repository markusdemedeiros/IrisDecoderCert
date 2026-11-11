import Kraken.X64.Examples.Sbr.Parse.UsacSpec
import Kraken.X64.Examples.Sbr.Parse.DtdfSpec
import Kraken.X64.Examples.Sbr.Parse.InvfSpec
import Kraken.X64.Examples.Sbr.Parse.NoiseSpec
import Kraken.X64.Examples.Sbr.Parse.EnvSpec

/-!
# `ff_aac_sbr_decode_usac_data`: the leaf callees' adapters

The local contracts of `UsacSpec` for `read_sbr_dtdf`, `read_sbr_invf`, `read_sbr_noise` and
`read_sbr_envelope` follow from the routines' own statements.

* `uf_flat`: `UF` with the caller's rest is a flat list of cells (`UFM`), with the channel `ch`
  first; each adapter permutes it into the routine's footprint and a frame.
* `gl_pre`, `gl_post`: a footprint equation moves a `CallPre`/`CallPost` from the caller's
  `cneed k` to the routine's (smaller) need; the excess joins the frame.
* `read_sbr_envelope` types two raw cells of `UF`: `bs_amp_res` and `inter_tes` take the values
  the bytes hold.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse Kraken.Examples.Sbr.Vlc

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

/-! ## Moving a call's convention through a footprint equation -/

omit [CodeEnv] in
theorem gl_perm_cp (Rc Rs X H1 R1 H2 R2 : Mem 64 → Prop) (e : H1 ⋆ R1 = H2 ⋆ R2) :
    Rc ⋆ ((Rs ⋆ X) ⋆ (H1 ⋆ R1)) = Rc ⋆ (Rs ⋆ (H2 ⋆ (R2 ⋆ X))) := by
  rw [e]; ac_rfl

omit [CodeEnv] in
theorem gl_need {need : Nat} {H : Mem 64 → Prop} {ra : Int64} {t : MachineData}
    (h : CallPre need H ra t) : need ≤ (t.regs.get64 .rsp).toNat :=
  CallPre.le h

omit [CodeEnv] in
/-- The excess of the caller's stack below the routine's need. -/
abbrev Exc (need need' : Nat) (t : MachineData) : Mem 64 → Prop :=
  (need - need') ?@ (t.regs.get64 .rsp - .ofNat 64 need)

omit [CodeEnv] in
theorem gl_pre {need need' : Nat} (hk : need' ≤ need) {H1 R1 H2 R2 : Mem 64 → Prop}
    {ra : Int64} {t : MachineData} (e : H1 ⋆ R1 = H2 ⋆ R2) (h : CallPre need (H1 ⋆ R1) ra t) :
    CallPre need' (H2 ⋆ (R2 ⋆ Exc need need' t)) ra t := by
  have hw := gl_need h
  unfold CallPre at h ⊢
  rw [Reserve.excess need' need _ hk hw, gl_perm_cp _ _ _ _ _ _ _ e] at h
  exact h

omit [CodeEnv] in
theorem gl_post {need need' : Nat} {t s : MachineData} (hk : need' ≤ need)
    (hw : need ≤ (t.regs.get64 .rsp).toNat) {H1 R1 H2 R2 : Mem 64 → Prop} {ra : Int64}
    (e : H1 ⋆ R1 = H2 ⋆ R2)
    (h : CallPost need' (H2 ⋆ (R2 ⋆ Exc need need' t)) ra t s) :
    CallPost need (H1 ⋆ R1) ra t s := by
  obtain ⟨h1, h2, h3, hm⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  rw [Reserve.excess need' need _ hk hw, gl_perm_cp _ _ _ _ _ _ _ e]
  exact hm

/-! ## `UF` as a flat list of cells -/

omit [CodeEnv] in
theorem gl_cut (a b : BitVec 64) (i j : Nat) (hb : b = a + BitVec.ofNat 64 i)
    (hw : i + j ≤ 2 ^ 64) : (i + j) ?@ a = i ?@ a ⋆ j ?@ b := by
  subst hb; exact Block.split a i j hw

omit [CodeEnv] in
theorem gl_blk11 (d : BitVec 64) : 11 ?@ (d + 0x1c#64) = 9 ?@ (d + 0x1c#64) ⋆ 2 ?@ (d + 0x25#64) :=
  gl_cut _ _ 9 2 (by rw [BitVec.add_assoc]; rfl) (by omega)

omit [CodeEnv] in
theorem gl_blk16 (d : BitVec 64) :
    16 ?@ (d + 0x15a50#64) = 15 ?@ (d + 0x15a50#64) ⋆ 1 ?@ (d + 0x15a5f#64) :=
  gl_cut _ _ 15 1 (by rw [BitVec.add_assoc]; rfl) (by omega)

/-- `DSc` but `bs_num_env`, `bs_num_noise`, `bs_amp_res`, `bs_invf_mode`, `bs_freq_res`. -/
abbrev DScL (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (48 ?@ (d + 0x31#64) ⋆ (cell4 (d + 0x3900#64) v.vOff
    ⋆ (4 ?@ (d + 0x3904#64) ⋆ (4 ?@ (d + 0x3908#64) ⋆ (c4 (d + 0x7920#64) v.ypos
    ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64)))))))))

omit [CodeEnv] in
theorem gl_dscD (v : DV) (d : BitVec 64) :
    (4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (4 ?@ (d + 0x3904#64)
    ⋆ (4 ?@ (d + 0x3908#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64)))))))))))))))
    = c4 (d + 8#64) v.nenv ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (4 ?@ (d + 0x64#64)
      ⋆ (v.invf =@ (d + 0x27#64) ⋆ (v.freqRes =@ (d + 0xc#64) ⋆ DScL v d)))) := by
  simp only [DScL]; ac_rfl

omit [CodeEnv] in
theorem gl_dsc (c : BitVec 64) (ch : Nat) (v : DV) :
    DSc c ch v = c4 (dAc c ch + 8#64) v.nenv ⋆ (c4 (dAc c ch + 0x18#64) v.nnoise
      ⋆ (4 ?@ (dAc c ch + 0x64#64) ⋆ (v.invf =@ (dAc c ch + 0x27#64)
      ⋆ (v.freqRes =@ (dAc c ch + 0xc#64) ⋆ DScL v (dAc c ch))))) :=
  gl_dscD v (dAc c ch)

/-- `DRaw` but the pieces the routines own. -/
abbrev DRR (d : BitVec 64) : Mem 64 → Prop :=
  3 ?@ (d + 0x15#64) ⋆ (3 ?@ (d + 0x61#64) ⋆ (24 ?@ (d + 0x68#64) ⋆ (9216 ?@ (d + 0x80#64)
    ⋆ (5248 ?@ (d + 0x2480#64) ⋆ (20 ?@ (d + 0x390c#64) ⋆ (16384 ?@ (d + 0x3920#64)
    ⋆ (12 ?@ (d + 0x7924#64) ⋆ (38936 ?@ (d + 0x7930#64) ⋆ (8040 ?@ (d + 0x11148#64)
    ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ (432 ?@ (d + 0x15030#64) ⋆ (1728 ?@ (d + 0x15390#64)
    ⋆ (1 ?@ (d + 0x15a5f#64) ⋆ (60 ?@ (d + 0x15a60#64) ⋆ 3 ?@ (d + 0x15aa9#64)))))))))))))))

omit [CodeEnv] in
theorem gl_drawD (d : BitVec 64) :
    Blocks [(d + 0x15#64, 3), (d + 0x1c#64, 11), (d + 0x61#64, 3), (d + 0x68#64, 24),
      (d + 0x80#64, 9216), (d + 0x2480#64, 5248), (d + 0x390c#64, 20),
      (d + 0x3920#64, 16384), (d + 0x7924#64, 12), (d + 0x7930#64, 38936),
      (d + 0x11148#64, 8040), (d + 0x130b0#64, 8064), (d + 0x15030#64, 432),
      (d + 0x151e0#64, 432), (d + 0x15390#64, 1728), (d + 0x15a50#64, 16),
      (d + 0x15a60#64, 60), (d + 0x15aa9#64, 3), (d + 0x15ab4#64, 12)]
    = 9 ?@ (d + 0x1c#64) ⋆ (2 ?@ (d + 0x25#64) ⋆ (15 ?@ (d + 0x15a50#64)
      ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (12 ?@ (d + 0x15ab4#64) ⋆ DRR d)))) := by
  simp only [Blocks, DRR, gl_blk11, gl_blk16]; ac_rfl

omit [CodeEnv] in
theorem gl_draw (c : BitVec 64) (ch : Nat) :
    DRaw c ch = 9 ?@ (dAc c ch + 0x1c#64) ⋆ (2 ?@ (dAc c ch + 0x25#64)
      ⋆ (15 ?@ (dAc c ch + 0x15a50#64) ⋆ (432 ?@ (dAc c ch + 0x151e0#64)
      ⋆ (12 ?@ (dAc c ch + 0x15ab4#64) ⋆ DRR (dAc c ch))))) :=
  gl_drawD (dAc c ch)

/-- `SHW` but `usac`, `inter_tes`, `bs_coupling`. -/
abbrev SHR (c : BitVec 64) (st : USt) : Mem 64 → Prop :=
  cell4 (sA c) st.x.sampleRate ⋆ (cell4 (sA c + 0x4#64) st.x.start
    ⋆ (cell4 (sA c + 0x8#64) st.x.ready ⋆ (cell4 (sA c + 0xc#64) st.x.idAac
    ⋆ (cell4 (sA c + 0x18#64) st.x.reset ⋆ (st.sp.take 4 =@ (sA c + 0x1c#64)
    ⋆ (st.sp.drop 4 =@ (sA c + 0x20#64) ⋆ (2 ?@ (sA c + 0x22#64)
    ⋆ (cell4 (sA c + 0x24#64) st.amp ⋆ (4 ?@ (sA c + 0x28#64)
    ⋆ (cell4 (sA c + 0x2c#64) (BitVec.ofNat 32 st.h.lb) ⋆ (c4 (sA c + 0x30#64) st.x.limGains
    ⋆ (cell4 (sA c + 0x34#64) st.x.interpol ⋆ (cell4 (sA c + 0x38#64) st.x.smooth
    ⋆ (c4 (sA c + 0x40#64) st.x.k0 ⋆ (16 ?@ (sA c + 0x44#64)
    ⋆ (c4 (sA c + 0x54#64) st.x.kx0 ⋆ (c4 (sA c + 0x58#64) st.x.kx1
    ⋆ (c4 (sA c + 0x5c#64) st.x.m0 ⋆ (c4 (sA c + 0x60#64) st.x.m1
    ⋆ (cell4 (sA c + 0x64#64) st.x.pushed ⋆ 24 ?@ (sA c + 0x68#64)))))))))))))))))))))

omit [CodeEnv] in
theorem gl_shw (c : BitVec 64) (st : USt) :
    SHW c st = cell4 (sA c + 0x10#64) st.u ⋆ (4 ?@ (sA c + 0x14#64)
      ⋆ (cell4 (sA c + 0x3c#64) st.x.coupling ⋆ SHR c st)) := by
  simp only [SHW, SHR]; generalize sA c = s; ac_rfl

/-- `TWc` but `n[0]`, `n[1]`, `n_q`. -/
abbrev TWR (c : BitVec 64) (x : Args) : Mem 64 → Prop :=
  c4 (sA c + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (sA c + 0x4c1f0#64) ⋆ (x.ftLow =@ (sA c + 0x4c252#64)
    ⋆ (x.ftHigh =@ (sA c + 0x4c284#64) ⋆ (x.ftNoise =@ (sA c + 0x4c2e6#64)
    ⋆ (x.ftLim =@ (sA c + 0x4c2f2#64) ⋆ (2 ?@ (sA c + 0x4c32e#64)
    ⋆ (c4 (sA c + 0x4c330#64) x.npatch ⋆ (x.pnum =@ (sA c + 0x4c334#64)
    ⋆ x.pstart =@ (sA c + 0x4c33a#64)))))))))

omit [CodeEnv] in
theorem gl_twc (c : BitVec 64) (x : Args) :
    TWc c x = c4 (sA c + 0x4c1e0#64) x.n0 ⋆ (c4 (sA c + 0x4c1e4#64) x.n1
      ⋆ (c4 (sA c + 0x4c1e8#64) x.nq ⋆ TWR c x)) := by
  simp only [TWc, TWR]

/-- The other channel, `ceil_log2`, the jump table, `ue->sbr`. -/
abbrev Oc (q : UQ) (st : USt) (ch : Nat) : Mem 64 → Prop :=
  DSc q.c (1 - ch) (st.x.d (1 - ch)) ⋆ (DRaw q.c (1 - ch) ⋆ (Blocks [(lab "ceil_log2", 6)]
    ⋆ (Grid.JtW ⋆ q.uev =@ (q.ue + 0xc#64))))

omit [CodeEnv] in
theorem gl_perm_c0 (S T D0 R0 D1 R1 A G B C J U E O : Mem 64 → Prop) :
    S ⋆ (T ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ (A ⋆ (G ⋆ ((B ⋆ C) ⋆ (J ⋆ (U ⋆ (E ⋆ O)))))))))))
    = D0 ⋆ (R0 ⋆ (S ⋆ (T ⋆ (A ⋆ (G ⋆ (B ⋆ ((D1 ⋆ (R1 ⋆ (C ⋆ (J ⋆ U)))) ⋆ (E ⋆ O)))))))) := by
  ac_rfl

omit [CodeEnv] in
theorem gl_perm_c1 (S T D0 R0 D1 R1 A G B C J U E O : Mem 64 → Prop) :
    S ⋆ (T ⋆ (D0 ⋆ (R0 ⋆ (D1 ⋆ (R1 ⋆ (A ⋆ (G ⋆ ((B ⋆ C) ⋆ (J ⋆ (U ⋆ (E ⋆ O)))))))))))
    = D1 ⋆ (R1 ⋆ (S ⋆ (T ⋆ (A ⋆ (G ⋆ (B ⋆ ((D0 ⋆ (R0 ⋆ (C ⋆ (J ⋆ U)))) ⋆ (E ⋆ O)))))))) := by
  ac_rfl

theorem gl_uf (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) :
    UF q st = DSc q.c ch (st.x.d ch) ⋆ (DRaw q.c ch ⋆ (SHW q.c st ⋆ (TWc q.c st.x
      ⋆ (AcU q.a st.x ⋆ (GbU q st.i ⋆ (Blocks [(q.buf, q.L)] ⋆ (Oc q st ch
      ⋆ (q.Ext ⋆ q.Oth)))))))) := by
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  · exact gl_perm_c0 _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · exact gl_perm_c1 _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `UF` with the caller's rest `R`, flat, channel `ch` first. -/
abbrev UFM (q : UQ) (st : USt) (ch : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  let d := dAc q.c ch
  let v := st.x.d ch
  let s := sA q.c
  c4 (d + 8#64) v.nenv ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (4 ?@ (d + 0x64#64)
  ⋆ (v.invf =@ (d + 0x27#64) ⋆ (v.freqRes =@ (d + 0xc#64) ⋆ (DScL v d
  ⋆ (9 ?@ (d + 0x1c#64) ⋆ (2 ?@ (d + 0x25#64) ⋆ (15 ?@ (d + 0x15a50#64)
  ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (12 ?@ (d + 0x15ab4#64) ⋆ (DRR d
  ⋆ (cell4 (s + 0x10#64) st.u ⋆ (4 ?@ (s + 0x14#64) ⋆ (cell4 (s + 0x3c#64) st.x.coupling
  ⋆ (SHR q.c st ⋆ (c4 (s + 0x4c1e0#64) st.x.n0 ⋆ (c4 (s + 0x4c1e4#64) st.x.n1
  ⋆ (c4 (s + 0x4c1e8#64) st.x.nq ⋆ (TWR q.c st.x
  ⋆ (Int.toBytes 8 st.x.avctx.toInt =@ (q.a + 0x8#64) ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
  ⋆ (GbU q st.i ⋆ (Blocks [(q.buf, q.L)] ⋆ (Oc q st ch
  ⋆ (q.Ext ⋆ (q.Oth ⋆ R))))))))))))))))))))))))))

theorem uf_flat (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) (R : Mem 64 → Prop) :
    UF q st ⋆ R = UFM q st ch R := by
  rw [gl_uf q st ch hch, gl_dsc, gl_draw, gl_shw, gl_twc, AcU]
  simp only [UFM, Std.ExtHashMap.sep_assoc]

/-! ## `read_sbr_dtdf` -/

/-- `read_sbr_dtdf`'s logical variable. -/
abbrev dx (q : UQ) (st : USt) (ch : Nat) (R : Mem 64 → Prop) : Dtdf.DArgs :=
  ⟨R, st.x.d ch, q.buf, st.i, q.p8, q.L⟩

/-- The caller's part at the `read_sbr_dtdf` call. -/
abbrev FrD (q : UQ) (st : USt) (ch : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  let d := dAc q.c ch
  let v := st.x.d ch
  let s := sA q.c
  4 ?@ (d + 0x64#64)
  ⋆ (v.invf =@ (d + 0x27#64) ⋆ (v.freqRes =@ (d + 0xc#64) ⋆ (DScL v d
  ⋆ (15 ?@ (d + 0x15a50#64)
  ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (12 ?@ (d + 0x15ab4#64) ⋆ (DRR d
  ⋆ (cell4 (s + 0x10#64) st.u ⋆ (4 ?@ (s + 0x14#64) ⋆ (cell4 (s + 0x3c#64) st.x.coupling
  ⋆ (SHR q.c st ⋆ (c4 (s + 0x4c1e0#64) st.x.n0 ⋆ (c4 (s + 0x4c1e4#64) st.x.n1
  ⋆ (c4 (s + 0x4c1e8#64) st.x.nq ⋆ (TWR q.c st.x
  ⋆ (Int.toBytes 8 st.x.avctx.toInt =@ (q.a + 0x8#64) ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
  ⋆ (Oc q st ch ⋆ (q.Ext ⋆ (q.Oth ⋆ R))))))))))))))))))))

omit [CodeEnv] in
theorem perm_d (N Q A I F S K9 K2 K15 K4 K12 DR U T C SR N0 N1 Nq TR Av Er G B O E Ot R :
    Mem 64 → Prop) :
    N ⋆ (Q ⋆ (A ⋆ (I ⋆ (F ⋆ (S ⋆ (K9 ⋆ (K2 ⋆ (K15 ⋆ (K4 ⋆ (K12 ⋆ (DR ⋆ (U ⋆ (T ⋆ (C ⋆ (SR
      ⋆ (N0 ⋆ (N1 ⋆ (Nq ⋆ (TR ⋆ (Av ⋆ (Er ⋆ (G ⋆ (B ⋆ (O ⋆ (E ⋆ (Ot
      ⋆ R))))))))))))))))))))))))))
    = (N ⋆ (Q ⋆ ((K9 ⋆ K2) ⋆ (G ⋆ B)))) ⋆ (A ⋆ (I ⋆ (F ⋆ (S ⋆ (K15 ⋆ (K4 ⋆ (K12 ⋆ (DR ⋆ (U
      ⋆ (T ⋆ (C ⋆ (SR ⋆ (N0 ⋆ (N1 ⋆ (Nq ⋆ (TR ⋆ (Av ⋆ (Er ⋆ (O ⋆ (E ⋆ (Ot
      ⋆ R))))))))))))))))))))) := by
  ac_rfl

theorem dtdf_eq (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) (R Rx : Mem 64 → Prop)
    (t : MachineData) (h1 : arg1 t = q.g) (h2 : arg2 t = dAc q.c ch) :
    UF q st ⋆ R = Dtdf.DtdfF (dx q st ch Rx) t st.i ⋆ FrD q st ch R := by
  rw [uf_flat q st ch hch]
  simp only [Dtdf.DtdfF, h1, h2, gl_blk11]
  exact perm_d _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

omit [CodeEnv] in
theorem ch_dwf {x : Args} {h : Hid} {ch : Nat} (hch : ch < 2) (hm : MI (x, h)) :
    DWF False (x.d ch) := by
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl
  · exact hm.1.2.2.1
  · exact hm.1.2.2.2.1

/-- **`read_sbr_dtdf`'s adapter.** -/
theorem usac_dtdf_glue (k ch : Nat) (hch : ch < 2) (Ext Oth : Mem 64 → Prop)
    (hD : cenv.ProcSpec (entry "read_sbr_dtdf") (Dtdf.DtdfPre (Usac.cneed k))
      (Dtdf.DtdfPost (Usac.cneed k))) :
    Usac.DtdfSpec k ch Ext Oth := by
  rintro ⟨q, st⟩ ra t ⟨⟨hcall, -⟩, -, h1, h2, hw, hi, hg⟩
  have hn := gl_need hcall
  have e := dtdf_eq q st ch hch q.R (FrD q st ch q.R ⋆ Exc (cneed k) (cneed k) t) t h1 h2
  have hpre : Dtdf.DtdfPre (cneed k) (dx q st ch (FrD q st ch q.R ⋆ Exc (cneed k) (cneed k) t))
      ra t :=
    ⟨gl_pre (Nat.le_refl _) e hcall,
      hw.2.2.2.2.1, hw.2.2.2.2.2.2.1, hi, hg.1, hg.2.1, hg.2.2⟩
  refine eventually_weaken _ _ _ _ (fun s hs => Or.inl ⟨hs.1, ?_⟩) (hD _ ra t hpre)
  obtain ⟨i, hi', hm⟩ := hs.2
  refine ⟨{ st with i := i }, ⟨rfl, hi'⟩, gl_post (Nat.le_refl _) hn
    (dtdf_eq q { st with i := i } ch hch q.R
      (FrD q st ch q.R ⋆ Exc (cneed k) (cneed k) t) t h1 h2) hm⟩

/-! ## `read_sbr_invf` -/

/-- `read_sbr_invf`'s logical variable. -/
abbrev ix (q : UQ) (st : USt) (ch : Nat) (R : Mem 64 → Prop) : Invf.IArgs :=
  ⟨R, st.x.nq, (st.x.d ch).invf, q.buf, st.i, q.p8, q.L⟩

/-- The caller's part at the `read_sbr_invf` call. -/
abbrev FrI (q : UQ) (st : USt) (ch : Nat) (R : Mem 64 → Prop) : Mem 64 → Prop :=
  let d := dAc q.c ch
  let v := st.x.d ch
  let s := sA q.c
  c4 (d + 8#64) v.nenv ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (4 ?@ (d + 0x64#64)
  ⋆ (v.freqRes =@ (d + 0xc#64) ⋆ (DScL v d
  ⋆ (9 ?@ (d + 0x1c#64) ⋆ (2 ?@ (d + 0x25#64) ⋆ (15 ?@ (d + 0x15a50#64)
  ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (12 ?@ (d + 0x15ab4#64) ⋆ (DRR d
  ⋆ (cell4 (s + 0x10#64) st.u ⋆ (4 ?@ (s + 0x14#64) ⋆ (cell4 (s + 0x3c#64) st.x.coupling
  ⋆ (SHR q.c st ⋆ (c4 (s + 0x4c1e0#64) st.x.n0 ⋆ (c4 (s + 0x4c1e4#64) st.x.n1
  ⋆ (TWR q.c st.x
  ⋆ (Int.toBytes 8 st.x.avctx.toInt =@ (q.a + 0x8#64) ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
  ⋆ (Oc q st ch ⋆ (q.Ext ⋆ (q.Oth ⋆ R))))))))))))))))))))))

omit [CodeEnv] in
theorem perm_i (N Q A I F S K9 K2 K15 K4 K12 DR U T C SR N0 N1 Nq TR Av Er G B O E Ot R :
    Mem 64 → Prop) :
    N ⋆ (Q ⋆ (A ⋆ (I ⋆ (F ⋆ (S ⋆ (K9 ⋆ (K2 ⋆ (K15 ⋆ (K4 ⋆ (K12 ⋆ (DR ⋆ (U ⋆ (T ⋆ (C ⋆ (SR
      ⋆ (N0 ⋆ (N1 ⋆ (Nq ⋆ (TR ⋆ (Av ⋆ (Er ⋆ (G ⋆ (B ⋆ (O ⋆ (E ⋆ (Ot
      ⋆ R))))))))))))))))))))))))))
    = (Nq ⋆ (I ⋆ (G ⋆ B))) ⋆ (N ⋆ (Q ⋆ (A ⋆ (F ⋆ (S ⋆ (K9 ⋆ (K2 ⋆ (K15 ⋆ (K4 ⋆ (K12 ⋆ (DR
      ⋆ (U ⋆ (T ⋆ (C ⋆ (SR ⋆ (N0 ⋆ (N1 ⋆ (TR ⋆ (Av ⋆ (Er ⋆ (O ⋆ (E ⋆ (Ot
      ⋆ R))))))))))))))))))))))) := by
  ac_rfl

theorem invf_eq (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) (R Rx : Mem 64 → Prop)
    (t : MachineData) (h0 : arg0 t = sA q.c) (h1 : arg1 t = q.g) (h2 : arg2 t = dAc q.c ch) :
    UF q st ⋆ R = Invf.IF (ix q st ch Rx) t (st.x.d ch).invf st.i ⋆ FrI q st ch R := by
  rw [uf_flat q st ch hch]
  simp only [Invf.IF, h0, h1, h2]
  exact perm_i _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The values after `read_sbr_invf` with the values `vals`, index `i`. -/
abbrev stInvf (st : USt) (ch : Nat) (vals : Nat → Nat) (i : BitVec 32) : USt :=
  { st with x := if ch = 0 then { st.x with d0 := invfRead st.x.nq st.x.d0 vals }
                 else { st.x with d1 := invfRead st.x.nq st.x.d1 vals }, i := i }

theorem invf_post_eq (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) (R Rx : Mem 64 → Prop)
    (t : MachineData) (vals : Nat → Nat) (i : BitVec 32) (h0 : arg0 t = sA q.c)
    (h1 : arg1 t = q.g) (h2 : arg2 t = dAc q.c ch) :
    UF q (stInvf st ch vals i) ⋆ R
      = Invf.IF (ix q st ch Rx) t (Invf.invfNew st.x.nq (st.x.d ch).invf vals) i
        ⋆ FrI q st ch R := by
  rw [invf_eq q _ ch hch R Rx t h0 h1 h2]
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl <;> rfl

/-- **`read_sbr_invf`'s adapter.** -/
theorem usac_invf_glue (k ch : Nat) (hch : ch < 2) (Ext Oth : Mem 64 → Prop)
    (hI : Invf.InvfSpec) : Usac.InvfSpec k ch Ext Oth := by
  rintro ⟨q, st⟩ ra t ⟨⟨hcall, -⟩, h0, h1, h2, hs, hw, hi, hg⟩
  have hn := gl_need hcall
  have e := invf_eq q st ch hch q.R (FrI q st ch q.R ⋆ Exc (cneed k) 0 t) t h0 h1 h2
  have hpre : Invf.InvfPre (ix q st ch (FrI q st ch q.R ⋆ Exc (cneed k) 0 t)) ra t :=
    ⟨gl_pre (Nat.zero_le _) e hcall,
      hs.2.2.2.2.2.2.2.2.2.1, hw.2.1, hi, hg.1, hg.2.1, hg.2.2⟩
  refine eventually_weaken _ _ _ _ (fun s hs => Or.inl ⟨hs.1, ?_⟩) (hI _ ra t hpre)
  obtain ⟨vals, i, -, hi', hm⟩ := hs.2
  refine ⟨stInvf st ch vals i, ⟨vals, rfl, hi'⟩, gl_post (Nat.zero_le _) hn
    (invf_post_eq q st ch hch q.R (FrI q st ch q.R ⋆ Exc (cneed k) 0 t) t vals i h0 h1 h2) hm⟩

/-! ## Raw bytes at a value -/

/-- Four raw bytes hold some 32-bit value. -/
theorem gl_b4 (a : BitVec 64) : (4 ?@ a) = fun m => ∃ v : BitVec 32, cell4 a v m :=
  block_eq_exists a 4 (by decide)

/-! ## `read_sbr_noise` -/

/-- `read_sbr_noise`'s logical variable. -/
abbrev nx (q : UQ) (st : USt) (ch : Nat) (v : Nat → VlcTab) (R : Mem 64 → Prop) : Noise.NArgs :=
  ⟨R, st.x.coupling, st.x.nq, (st.x.d ch).nnoise, st.x.avctx, q.buf, st.i, q.p8, q.L, v⟩

/-- The caller's part at the `read_sbr_noise` call. -/
abbrev FrN (q : UQ) (st : USt) (ch : Nat) (O R : Mem 64 → Prop) : Mem 64 → Prop :=
  let d := dAc q.c ch
  let v := st.x.d ch
  let s := sA q.c
  c4 (d + 8#64) v.nenv ⋆ (4 ?@ (d + 0x64#64) ⋆ (v.invf =@ (d + 0x27#64)
  ⋆ (v.freqRes =@ (d + 0xc#64) ⋆ (DScL v d ⋆ (9 ?@ (d + 0x1c#64)
  ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (12 ?@ (d + 0x15ab4#64) ⋆ (DRR d
  ⋆ (cell4 (s + 0x10#64) st.u ⋆ (4 ?@ (s + 0x14#64)
  ⋆ (SHR q.c st ⋆ (c4 (s + 0x4c1e0#64) st.x.n0 ⋆ (c4 (s + 0x4c1e4#64) st.x.n1
  ⋆ (TWR q.c st.x ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
  ⋆ (Oc q st ch ⋆ (O ⋆ R)))))))))))))))))

omit [CodeEnv] in
theorem perm_n (N Q A I F S K9 K2 K15 K4 K12 DR U T C SR N0 N1 Nq TR Av Er G B O E Vw Ow R :
    Mem 64 → Prop) :
    N ⋆ (Q ⋆ (A ⋆ (I ⋆ (F ⋆ (S ⋆ (K9 ⋆ (K2 ⋆ (K15 ⋆ (K4 ⋆ (K12 ⋆ (DR ⋆ (U ⋆ (T ⋆ (C ⋆ (SR
      ⋆ (N0 ⋆ (N1 ⋆ (Nq ⋆ (TR ⋆ (Av ⋆ (Er ⋆ (G ⋆ (B ⋆ (O ⋆ (E ⋆ ((Vw ⋆ Ow)
      ⋆ R))))))))))))))))))))))))))
    = (C ⋆ (Nq ⋆ (Q ⋆ (K2 ⋆ (K15 ⋆ (Av ⋆ (G ⋆ (B ⋆ (Vw ⋆ E))))))))) ⋆ (N ⋆ (A ⋆ (I ⋆ (F ⋆ (S
      ⋆ (K9 ⋆ (K4 ⋆ (K12 ⋆ (DR ⋆ (U ⋆ (T ⋆ (SR ⋆ (N0 ⋆ (N1 ⋆ (TR ⋆ (Er ⋆ (O ⋆ (Ow
      ⋆ R)))))))))))))))))) := by
  ac_rfl

theorem noise_eq (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) (Ext O R Rx : Mem 64 → Prop)
    (v : Nat → VlcTab) (t : MachineData) (hE : q.Ext = Ext) (hO : q.Oth = VlcW v ⋆ O)
    (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c) (h2 : arg2 t = q.g) (h3 : arg3 t = dAc q.c ch) :
    UF q st ⋆ R = Noise.NoiseF Ext (nx q st ch v Rx) t st.i ⋆ FrN q st ch O R := by
  rw [uf_flat q st ch hch]
  simp only [UFM, Noise.NoiseF, hE, hO, h0, h1, h2, h3]
  exact perm_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **`read_sbr_noise`'s adapter.** -/
theorem usac_noise_glue (k kn ch : Nat) (hch : ch < 2) (Ext Oth O : Mem 64 → Prop)
    (v : Nat → VlcTab) (hv : VlcC v) (hO : Oth = VlcW v ⋆ O)
    (hk : Noise.noiseNeed kn ≤ Usac.cneed k)
    (hN : Noise.NoiseSpec kn Ext) : Usac.EnvNoiseSpec "read_sbr_noise" k ch Ext Oth := by
  rintro ⟨q, st⟩ ra t ⟨⟨hcall, hqE, hqO⟩, h0, h1, h2, h3, -, hm, -, hi, hg, -⟩
  have hO' : q.Oth = VlcW v ⋆ O := hqO.trans hO
  have hn := gl_need hcall
  have e := noise_eq q st ch hch Ext O q.R
    (FrN q st ch O q.R ⋆ Exc (cneed k) (Noise.noiseNeed kn) t) v t hqE hO' h0 h1 h2 h3
  have hpre : Noise.NoisePre kn Ext
      (nx q st ch v (FrN q st ch O q.R ⋆ Exc (cneed k) (Noise.noiseNeed kn) t)) ra t :=
    ⟨gl_pre hk e hcall, (ch_dwf hch hm).2.2.2.2.2.2.1, hm.1.1.2.2.2.2.2.2.2.2.2.1, hv, hi,
      hg.1, hg.2.1, hg.2.2⟩
  refine eventually_weaken _ _ _ _ (fun s hs => Or.inl ⟨hs.1, ?_⟩) (hN _ ra t hpre)
  obtain ⟨i, hi', -, hm'⟩ := hs.2
  exact ⟨{ st with i := i }, ⟨rfl, hi'⟩, gl_post hk hn
    (noise_eq q { st with i := i } ch hch Ext O q.R
      (FrN q st ch O q.R ⋆ Exc (cneed k) (Noise.noiseNeed kn) t) v t hqE hO' h0 h1 h2 h3) hm'⟩

/-! ## `read_sbr_envelope` -/

/-- `read_sbr_envelope`'s footprint at index `i`, with `bs_amp_res` as `A`, `inter_tes` as
`T`. -/
abbrev EH (A T : Mem 64 → Prop) (q : UQ) (st : USt) (ch : Nat) (Ext : Mem 64 → Prop)
    (v : Nat → VlcTab) (i : BitVec 32) : Mem 64 → Prop :=
  (c4 (dAc q.c ch + 8#64) (st.x.d ch).nenv ⋆ ((st.x.d ch).freqRes =@ (dAc q.c ch + 0xc#64)
    ⋆ (9 ?@ (dAc q.c ch + 0x1c#64) ⋆ (A ⋆ (432 ?@ (dAc q.c ch + 0x151e0#64)
    ⋆ 12 ?@ (dAc q.c ch + 0x15ab4#64))))))
  ⋆ ((cell4 (sA q.c + 0x10#64) st.u ⋆ (T ⋆ (cell4 (sA q.c + 0x3c#64) st.x.coupling
    ⋆ (c4 (sA q.c + 0x4c1e0#64) st.x.n0 ⋆ c4 (sA q.c + 0x4c1e4#64) st.x.n1))))
  ⋆ (GbU q i ⋆ (Int.toBytes 8 st.x.avctx.toInt =@ (q.a + 0x8#64)
    ⋆ (Blocks [(q.buf, q.L)] ⋆ (VlcW v ⋆ Ext)))))

/-- `EH` with the two cells raw, as `UF` holds them. -/
abbrev EHr (q : UQ) (st : USt) (ch : Nat) (Ext : Mem 64 → Prop) (v : Nat → VlcTab)
    (i : BitVec 32) : Mem 64 → Prop :=
  EH (4 ?@ (dAc q.c ch + 0x64#64)) (4 ?@ (sA q.c + 0x14#64)) q st ch Ext v i

/-- The caller's part at the `read_sbr_envelope` call. -/
abbrev FrE (q : UQ) (st : USt) (ch : Nat) (O R : Mem 64 → Prop) : Mem 64 → Prop :=
  let d := dAc q.c ch
  let v := st.x.d ch
  let s := sA q.c
  c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (DScL v d
  ⋆ (2 ?@ (d + 0x25#64) ⋆ (15 ?@ (d + 0x15a50#64) ⋆ (DRR d
  ⋆ (SHR q.c st ⋆ (c4 (s + 0x4c1e8#64) st.x.nq ⋆ (TWR q.c st.x
  ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate ⋆ (Oc q st ch ⋆ (O ⋆ R)))))))))))

omit [CodeEnv] in
theorem perm_e (N Q A I F S K9 K2 K15 K4 K12 DR U T C SR N0 N1 Nq TR Av Er G B O E Vw Ow R :
    Mem 64 → Prop) :
    N ⋆ (Q ⋆ (A ⋆ (I ⋆ (F ⋆ (S ⋆ (K9 ⋆ (K2 ⋆ (K15 ⋆ (K4 ⋆ (K12 ⋆ (DR ⋆ (U ⋆ (T ⋆ (C ⋆ (SR
      ⋆ (N0 ⋆ (N1 ⋆ (Nq ⋆ (TR ⋆ (Av ⋆ (Er ⋆ (G ⋆ (B ⋆ (O ⋆ (E ⋆ ((Vw ⋆ Ow)
      ⋆ R))))))))))))))))))))))))))
    = ((N ⋆ (F ⋆ (K9 ⋆ (A ⋆ (K4 ⋆ K12))))) ⋆ ((U ⋆ (T ⋆ (C ⋆ (N0 ⋆ N1)))) ⋆ (G ⋆ (Av ⋆ (B
      ⋆ (Vw ⋆ E)))))) ⋆ (Q ⋆ (I ⋆ (S ⋆ (K2 ⋆ (K15 ⋆ (DR ⋆ (SR ⋆ (Nq ⋆ (TR ⋆ (Er ⋆ (O ⋆ (Ow
      ⋆ R)))))))))))) := by
  ac_rfl

theorem env_eq (q : UQ) (st : USt) (ch : Nat) (hch : ch < 2) (Ext O R : Mem 64 → Prop)
    (v : Nat → VlcTab) (hE : q.Ext = Ext) (hO : q.Oth = VlcW v ⋆ O) :
    UF q st ⋆ R = EHr q st ch Ext v st.i ⋆ FrE q st ch O R := by
  rw [uf_flat q st ch hch]
  simp only [UFM, hE, hO]
  exact perm_e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `read_sbr_envelope`'s logical variable, with `bs_amp_res = amp`, `inter_tes = it`. -/
abbrev ex (q : UQ) (st : USt) (ch : Nat) (v : Nat → VlcTab) (R : Mem 64 → Prop)
    (amp it : BitVec 32) : Env.EArgs :=
  ⟨R, st.x.d ch, st.x.n0, st.x.n1, st.x.coupling, amp, st.u, it, st.x.avctx, q.buf, st.i, q.p8,
    q.L, v⟩

theorem ef_eq (q : UQ) (st : USt) (ch : Nat) (Ext R : Mem 64 → Prop) (v : Nat → VlcTab)
    (amp it i : BitVec 32) (t : MachineData) (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c)
    (h2 : arg2 t = q.g) (h3 : arg3 t = dAc q.c ch) :
    Env.EF Ext (ex q st ch v R amp it) t i
      = EH (cell4 (dAc q.c ch + 0x64#64) amp) (cell4 (sA q.c + 0x14#64) it) q st ch Ext v i := by
  simp only [Env.EF, Env.ChE, Env.SbrE, Env.GbE, Env.InE, h0, h1, h2, h3]
  rfl

theorem gl_ex2 {Rc Rs N F K9 W1 U W2 Z Fr : Mem 64 → Prop} {a b : BitVec 64} {m : Mem 64}
    (h : m =⋆ Rc ⋆ (Rs ⋆ (((N ⋆ (F ⋆ (K9 ⋆ (4 ?@ a ⋆ W1)))) ⋆ ((U ⋆ (4 ?@ b ⋆ W2)) ⋆ Z))
      ⋆ Fr))) :
    ∃ v w : BitVec 32, m =⋆ Rc ⋆ (Rs ⋆ (((N ⋆ (F ⋆ (K9 ⋆ (cell4 a v ⋆ W1))))
      ⋆ ((U ⋆ (cell4 b w ⋆ W2)) ⋆ Z)) ⋆ Fr)) := by
  rw [gl_b4 a, gl_b4 b] at h
  simp only [sep_ex_l, sep_ex_r] at h
  obtain ⟨v, w, h⟩ := h
  first | exact ⟨v, w, h⟩ | exact ⟨w, v, h⟩

theorem gl_fg2 {Rc Rs N F K9 W1 U W2 Z Fr : Mem 64 → Prop} {a b : BitVec 64} {m : Mem 64}
    {v w : BitVec 32}
    (h : m =⋆ Rc ⋆ (Rs ⋆ (((N ⋆ (F ⋆ (K9 ⋆ (cell4 a v ⋆ W1))))
      ⋆ ((U ⋆ (cell4 b w ⋆ W2)) ⋆ Z)) ⋆ Fr))) :
    m =⋆ Rc ⋆ (Rs ⋆ (((N ⋆ (F ⋆ (K9 ⋆ (4 ?@ a ⋆ W1)))) ⋆ ((U ⋆ (4 ?@ b ⋆ W2)) ⋆ Z))
      ⋆ Fr)) := by
  rw [gl_b4 a, gl_b4 b]
  simp only [sep_ex_l, sep_ex_r]
  first | exact ⟨v, w, h⟩ | exact ⟨w, v, h⟩

omit [CodeEnv] in
theorem gl_al {c : BitVec 64} {ch : Nat} (hch : ch < 2) (hal : (sA c).toNat % 32 = 0) :
    (dAc c ch).toNat % 32 = 0 := by
  simp only [dAc]
  generalize sA c = s at hal ⊢
  rcases (by omega : ch = 0 ∨ ch = 1) with rfl | rfl <;>
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] <;> omega

/-- **`read_sbr_envelope`'s adapter.** -/
theorem usac_env_glue (k ke ch : Nat) (hch : ch < 2) (Ext Oth O : Mem 64 → Prop)
    (v : Nat → VlcTab) (hv : VlcC v) (hO : Oth = VlcW v ⋆ O) (hk : Env.envNeed ke ≤ Usac.cneed k)
    (hE : ProcSpecS Env.envStops (entry "read_sbr_envelope") (Env.EnvPre ke Ext)
      (Env.EnvPost ke Ext)) :
    Usac.EnvNoiseSpec "read_sbr_envelope" k ch Ext Oth := by
  rintro ⟨q, st⟩ ra t ⟨⟨hcall, hqE, hqO⟩, h0, h1, h2, h3, -, hm, -, hi, hg, hal⟩
  have hO' : q.Oth = VlcW v ⋆ O := hqO.trans hO
  have hn := gl_need hcall
  have e := env_eq q st ch hch Ext O q.R v hqE hO'
  obtain ⟨amp, it, hc⟩ := gl_ex2 (gl_pre hk e hcall)
  have hpre : Env.EnvPre ke Ext
      (ex q st ch v (FrE q st ch O q.R ⋆ Exc (cneed k) (Env.envNeed ke) t) amp it) ra t := by
    refine ⟨?_, ch_dwf hch hm, hm.1.1.2.2.2.2.2.2.2.1, hm.1.1.2.2.2.2.2.2.2.2.1, hi, hg.1,
      hg.2.1, hg.2.2, hv, ?_⟩
    · unfold CallPre
      rw [ef_eq q st ch Ext _ v amp it st.i t h0 h1 h2 h3]
      exact hc
    · rw [h3]; exact gl_al hch hal
  refine eventually_weaken _ _ _ _
    (fun s hs => hs.imp (fun h => ⟨h.1, ?_⟩) (fun h => Or.inr h)) (hE _ ra t hpre)
  obtain ⟨i, ⟨hi', -⟩, hr1, hr2, hr3, hm'⟩ := h.2
  refine ⟨{ st with i := i }, ⟨rfl, hi'⟩, gl_post hk hn
    (env_eq q { st with i := i } ch hch Ext O q.R v hqE hO') ⟨hr1, hr2, hr3, ?_⟩⟩
  rw [ef_eq q st ch Ext _ v amp it i t h0 h1 h2 h3] at hm'
  exact gl_fg2 hm'

end Kraken.Examples.Sbr.Usac
