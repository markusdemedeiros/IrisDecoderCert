import Kraken.X64.Examples.Sbr.Parse.DecExtGlueN
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueH

/-!
# `ff_aac_sbr_decode_extension`: the `read_sbr_grid` adapter

`grid_glue`: `read_sbr_grid`'s statement (`Grid.GridPre`/`GridPost`, a `ProcSpecA`; `Ext = E`)
with the jump table's layout `Grid.JtC` gives the local `GridSpec (gridNeed k)` for a caller's
`Ext = A ⋆ (B ⋆ (V ⋆ E))`.

* The routine's state `Grid.GSt` of the channel values `v` is `gst v` (`bs_num_env`,
  `bs_num_noise` as 32-bit cells: `c4_cell`, below `2^31` by `DWF`).
* `DataF` is `Grid.ChW` (with `e_a[2]` as one 8-byte block) and `DataG`.
* At the return, the channel's values are `dvGrid` of the state left.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

omit [CodeEnv] in
theorem c4_cell (a : BitVec 64) (n : Nat) (h : n < 2 ^ 31) :
    cell4 a (BitVec.ofNat 32 n) = c4 a n := by
  show (Int.toBytes 4 (BitVec.ofNat 32 n).toInt =@ a) = (Int.toBytes 4 (n : Int) =@ a)
  have : (BitVec.ofNat 32 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
    omega
  rw [this]

omit [CodeEnv] in
theorem blk8 (d : BitVec 64) :
    8 ?@ (d + 0x3904#64) = 4 ?@ (d + 0x3904#64) ⋆ 4 ?@ (d + 0x3908#64) :=
  blk_cut _ _ 4 4 (by rw [BitVec.add_assoc]; rfl) (by omega)

/-- `read_sbr_grid`'s state of the channel values `v`, reader index `i`. -/
abbrev gst (v : DV) (i : BitVec 32) : Grid.GSt :=
  ⟨i, BitVec.ofNat 32 v.nenv, v.freqRes, BitVec.ofNat 32 v.nnoise, v.te, v.tq⟩

/-- `DataF` but `Grid.ChW`. -/
abbrev DataG (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ (d + 0x4#64) ⋆ (3 ?@ (d + 0x15#64) ⋆ (11 ?@ (d + 0x1c#64) ⋆ (v.invf =@ (d + 0x27#64)
  ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64) ⋆ (0x3898 ?@ (d + 0x68#64)
  ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (0x4014 ?@ (d + 0x390c#64) ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ (0xe178 ?@ (d + 0x7924#64) ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx
  ⋆ 12 ?@ (d + 0x15ab4#64)))))))))))))

omit [CodeEnv] in
theorem dataF_g (v : DV) (d : BitVec 64) (i : BitVec 32) (h1 : v.nenv < 2 ^ 31)
    (h2 : v.nnoise < 2 ^ 31) : DataF v d = Grid.ChW d (gst v i) ⋆ DataG v d := by
  simp only [DataF, DataG, Grid.ChW, gst, c4_cell _ _ h1, c4_cell _ _ h2, blk8]; ac_rfl

/-- `SbrS` but `usac`, `bs_amp_res_header`. -/
abbrev ScG (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 s d.a.sampleRate ⋆ (cell4 (s + 0x4#64) d.a.start ⋆ (cell4 (s + 0x8#64) d.a.ready
  ⋆ (cell4 (s + 0xc#64) d.a.idAac ⋆ (cell4 (s + 0x14#64) d.it ⋆ (cell4 (s + 0x18#64) d.a.reset
  ⋆ (d.sp =@ (s + 0x1c#64) ⋆ (2 ?@ (s + 0x22#64) ⋆ (4 ?@ (s + 0x28#64) ⋆ (c4 (s + 0x2c#64) d.h.lb
  ⋆ (c4 (s + 0x30#64) d.a.limGains ⋆ (cell4 (s + 0x34#64) d.a.interpol
  ⋆ (cell4 (s + 0x38#64) d.a.smooth ⋆ (cell4 (s + 0x3c#64) d.a.coupling ⋆ (c4 (s + 0x40#64) d.a.k0
  ⋆ (16 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x54#64) d.a.kx0 ⋆ (c4 (s + 0x58#64) d.a.kx1
  ⋆ (c4 (s + 0x5c#64) d.a.m0 ⋆ (c4 (s + 0x60#64) d.a.m1 ⋆ (cell4 (s + 0x64#64) d.a.pushed
  ⋆ 0x18 ?@ (s + 0x68#64)))))))))))))))))))))

omit [CodeEnv] in
theorem sbrS_g (d : DS) (s : BitVec 64) :
    SbrS d s = (cell4 (s + 0x10#64) d.usac ⋆ cell4 (s + 0x24#64) d.amp) ⋆ ScG d s := by
  simp only [SbrS, ScG]; ac_rfl

/-- The caller's part at the `read_sbr_grid` call. -/
abbrev FrG (A B V : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) : Mem 64 → Prop :=
  DataG (chV d b) (chA c.s b) ⋆ (ScG d c.s ⋆ (DataF (chV d !b) (chA c.s !b)
    ⋆ (d.a.psc =@ (c.s + 0x2b600#64) ⋆ (TabF d.a c.s ⋆ (A ⋆ (B ⋆ (V ⋆ c.R)))))))

/-- `Grid.GF` at the caller's addresses and values. -/
abbrev GCan (E : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) (st : Grid.GSt) : Mem 64 → Prop :=
  Grid.ChW (chA c.s b) st ⋆ (GbR c.g c.r st.i ⋆ (cell4 (c.s + 0x10#64) d.usac
    ⋆ (cell4 (c.s + 0x24#64) d.amp ⋆ (AvW c.ac d.a ⋆ (BufW c.r ⋆ (Grid.JtW ⋆ E))))))

omit [CodeEnv] in
theorem perm_g (CW DG Us Am ScG Do Ps TF Gb Bf Av Jt A B V E R : Mem 64 → Prop) :
    (((CW ⋆ DG) ⋆ (((Us ⋆ Am) ⋆ ScG) ⋆ (Do ⋆ (Ps ⋆ TF))))
      ⋆ (Gb ⋆ (Bf ⋆ (Av ⋆ (Jt ⋆ (A ⋆ (B ⋆ (V ⋆ E)))))))) ⋆ R
    = (CW ⋆ (Gb ⋆ (Us ⋆ (Am ⋆ (Av ⋆ (Bf ⋆ (Jt ⋆ E)))))))
      ⋆ (DG ⋆ (ScG ⋆ (Do ⋆ (Ps ⋆ (TF ⋆ (A ⋆ (B ⋆ (V ⋆ R)))))))) := by
  ac_rfl

theorem cfg_eq (A B V E : Mem 64 → Prop) (c : CA) (d : DS) (i : BitVec 32) (b : Bool)
    (h1 : (chV d b).nenv < 2 ^ 31) (h2 : (chV d b).nnoise < 2 ^ 31) :
    CF (A ⋆ (B ⋆ (V ⋆ E))) c d i ⋆ c.R = GCan E c d b (gst (chV d b) i) ⋆ FrG A B V c d b := by
  simp only [CF, FrG, GCan]
  rw [sbrF_ch d c.s b, dataF_g _ _ i h1 h2, SbrO, sbrS_g]
  exact perm_g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `read_sbr_grid`'s logical variable at the call. -/
abbrev gxOf (A B V : Mem 64 → Prop) (c : CA) (b : Bool) : Grid.GArgs :=
  ⟨FrG A B V c c.d b, chV c.d b, c.d.usac, c.d.amp, c.d.a.avctx, c.r.buf, c.i, c.r.p8, c.r.L⟩

theorem gf_eq (A B V E : Mem 64 → Prop) (c : CA) (b : Bool) (t : MachineData) (st : Grid.GSt)
    (h0 : arg0 t = c.ac) (h1 : arg1 t = c.s) (h2 : arg2 t = c.g) (h3 : arg3 t = chA c.s b) :
    Grid.GF E (gxOf A B V c b) t st ⋆ FrG A B V c c.d b = GCan E c c.d b st ⋆ FrG A B V c c.d b := by
  simp only [Grid.GF, Grid.InW, h0, h1, h2, h3]

omit [CodeEnv] in
theorem chV_set (d : DS) (b : Bool) (v : DV) : chV (d.setCh b v) b = v := by
  cases b <;> rfl

omit [CodeEnv] in
theorem frG_grid (A B V : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) (n : Nat) (fr : List UInt8)
    (nn : Nat) (te tq : List UInt8) :
    FrG A B V c (d.setCh b (dvGrid (chV d b) n fr nn te tq)) b = FrG A B V c d b := by
  cases b <;> rfl

theorem gcan_set (E : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) (v : DV) (st : Grid.GSt) :
    GCan E c (d.setCh b v) b st = GCan E c d b st := by
  cases b <;> rfl

omit [CodeEnv] in
theorem gst_eq (v : DV) (st : Grid.GSt) :
    gst (dvGrid v st.n.toNat st.fr st.nn.toNat st.te st.tq) st.i = st := by
  obtain ⟨i, n, fr, nn, te, tq⟩ := st
  simp only [gst, ofNat_toNat32]

/-- **`read_sbr_grid`'s adapter.** -/
theorem grid_glue (k : Nat) (A B V E : Mem 64 → Prop) (hJ : Grid.JtC)
    (hG : Kraken.Examples.Sbr.Parse.ProcSpecA (entry "read_sbr_grid")
      (fun x ra t => Grid.GridPre k E x ra t) (fun x ra t s => Grid.GridPost k E x ra t s)) :
    GridSpec (Grid.gridNeed k) (A ⋆ (B ⋆ (V ⋆ E))) := by
  intro cb ra t hp
  obtain ⟨c, b⟩ := cb
  obtain ⟨⟨hcall, hrok, hdok⟩, h0, h1, h2, h3, hw, hte⟩ := hp
  have hw0 : DWF False (chV c.d b) := hw
  have hn1 : (chV c.d b).nenv < 2 ^ 31 := by have : (chV c.d b).nenv ≤ 8 := hw0.2.2.2.2.1; omega
  have hn2 : (chV c.d b).nnoise < 2 ^ 31 := by
    have : (chV c.d b).nnoise ≤ 2 := hw0.2.2.2.2.2.2.1; omega
  have hpre : Grid.GridPre k E (gxOf A B V c b) ra t := by
    refine ⟨?_, by unfold Grid.GridC; exact ⟨hw, hte, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2, hJ⟩⟩
    have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF (A ⋆ (B ⋆ (V ⋆ E))) c c.d c.i ⋆ c.R)) := hcall
    rw [cfg_eq A B V E c c.d c.i b hn1 hn2, ← gf_eq A B V E c b t _ h0 h1 h2 h3] at hm
    exact hm
  have hpost : ∀ s, Grid.GridPost k E (gxOf A B V c b) ra t s →
      CPost (Grid.gridNeed k) (A ⋆ (B ⋆ (V ⋆ E))) c ra t s fun d' => ∃ n fr nn te tq,
        d' = c.d.setCh b (dvGrid (chV c.d b) n fr nn te tq)
        ∧ GridV (dvGrid (chV c.d b) n fr nn te tq) ((s.regs.get64 .rax).setWidth 32) := by
    intro s hs
    obtain ⟨st, ho, hsr, hbp, hsv, hm⟩ := hs
    obtain ⟨hwf, hte', hret, hlive, hi⟩ := ho
    have hwf' : DWF False (dvGrid (chV c.d b) st.n.toNat st.fr st.nn.toNat st.te st.tq) := hwf
    have m1 : st.n.toNat < 2 ^ 31 := by have : st.n.toNat ≤ 8 := hwf'.2.2.2.2.1; omega
    have m2 : st.nn.toNat < 2 ^ 31 := by have : st.nn.toNat ≤ 2 := hwf'.2.2.2.2.2.2.1; omega
    refine ⟨c.d.setCh b (dvGrid (chV c.d b) st.n.toNat st.fr st.nn.toNat st.te st.tq), st.i,
      ⟨st.n.toNat, st.fr, st.nn.toNat, st.te, st.tq, rfl,
        by unfold GridV; exact ⟨hwf', hte', hret, hlive⟩⟩, ?_, ?_, hi, hsr, hbp, hsv, ?_⟩
    · cases b <;> exact hdok
    · cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · show s.dmem =⋆ _ ⋆ (_ ⋆ (CF (A ⋆ (B ⋆ (V ⋆ E))) c
        (c.d.setCh b (dvGrid (chV c.d b) st.n.toNat st.fr st.nn.toNat st.te st.tq)) st.i ⋆ c.R))
      rw [cfg_eq A B V E c _ st.i b (by rw [chV_set]; exact m1) (by rw [chV_set]; exact m2),
        chV_set, gst_eq, gcan_set, frG_grid]
      have hm' : s.dmem =⋆ _ ⋆ (_ ⋆ (Grid.GF E (gxOf A B V c b) t st ⋆ FrG A B V c c.d b)) := hm
      rw [gf_eq A B V E c b t st h0 h1 h2 h3] at hm'
      exact hm'
  exact eventually_weaken _ _ _ _ (fun st hst => hst.imp (fun h => ⟨h.1, hpost _ h.2⟩) id)
    (hG _ ra t hpre)

end Kraken.Examples.Sbr.DecExt
