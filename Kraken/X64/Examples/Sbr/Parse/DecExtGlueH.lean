import Kraken.X64.Examples.Sbr.Parse.DecExtGlueR

/-!
# `ff_aac_sbr_decode_extension`: the `read_sbr_header` adapter

`hdr_glue`: `read_sbr_header`'s own statement for every callee footprint (`Hdr.HdrSpec`; with
`sbr->usac` a value at entry: `HdrSpecU`, `hdrU_of`) and
`sbr_make_f_tablelim`'s contract (`Reset.TlimSpec`) give the local contract `HdrSpec`.

* `tlim_glue`: at fixed values `a`, `Reset.TlimSpec` is `read_sbr_header`'s callee hypothesis
  `Hdr.TlimSpec (TlC0 a) (TlP a) (TlCs a)`: the footprint `TlC0 a` (the tables
  `sbr_make_f_tablelim` holds, at the values `a`), the result `TlP a lb` (some new `f_tablelim`,
  `n_lim` with `Tablelim`), the side condition `TlCs a` (`TlimC`).
* The caller's `CF` at `sbr` is `HFU` (with `TlC0 c.d.a`) and the frame `FrH`, passed as the
  header's `R` (`cfh_eq`). At the return, the values are `hdrVals` of the tables left, and
  `hdr_hi` gives `HI`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

/-! ## `sbr_make_f_tablelim` as `read_sbr_header` sees it -/

/-- The tables `sbr_make_f_tablelim` holds, but `bs_limiter_bands`, at the values `a`. -/
abbrev TlC0 (a : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x58#64) a.kx1 ⋆ (c4 (s + 0x4c1e0#64) a.n0
    ⋆ (c4 (s + 0x4c1ec#64) a.nlim ⋆ (a.ftLow =@ (s + 0x4c252#64) ⋆ (a.ftLim =@ (s + 0x4c2f2#64)
    ⋆ (c4 (s + 0x4c330#64) a.npatch ⋆ (a.pnum =@ (s + 0x4c334#64) ⋆ Reset.BwR))))))

/-- New `f_tablelim`, `n_lim`. -/
abbrev limSet (a : Args) (fl : List UInt8) (nl : Nat) : Args := { a with ftLim := fl, nlim := nl }

/-- The tables after `sbr_make_f_tablelim` with `bs_limiter_bands = lb`. -/
def TlP (a : Args) (lb : BitVec 32) (s : BitVec 64) (m : Mem 64) : Prop :=
  ∃ fl nl, Tablelim lb.toNat a (limSet a fl nl) ∧ TlC0 (limSet a fl nl) s m

/-- `TlimC` at `sbr = s`. -/
def TlCs (a : Args) (lb : BitVec 32) (s : BitVec 64) : Prop :=
  lb.toNat ≤ 3 ∧ a.n0 ≤ 24 ∧ a.npatch ≤ 6 ∧ (0 < lb.toNat → 1 ≤ a.n0 + a.npatch)
  ∧ a.ftLow.length = 50 ∧ a.ftLim.length = 60 ∧ a.pnum.length = 6
  ∧ TabIn a.ftLow a.n0 a.kx1 (a.kx1 + a.m1) ∧ psum a.pnum a.npatch ≤ a.m1 ∧ a.kx1 + a.m1 ≤ 64
  ∧ a.nlim < 2 ^ 32 ∧ s.toNat + 0x4c340 < 2 ^ 64

omit [CodeEnv] in
theorem tablelim_keep {lb : Nat} {a y : Args} (h : Tablelim lb a y) :
    ∃ fl nl, y = limSet a fl nl := by
  cases h <;> exact ⟨_, _, rfl⟩

omit [CodeEnv] in
theorem tablelim_hv {lb : Nat} {a y : Args} (st : Hdr.HSt) (h : Tablelim lb a y) :
    Tablelim lb (hdrVals a st) (hdrVals y st) := by
  cases h with
  | zero h0 => exact Tablelim.zero h0
  | pos h1 h2 h3 h4 => exact Tablelim.pos h1 h2 h3 h4

/-- **`sbr_make_f_tablelim`'s adapter**: tlim's contract (`Reset.TlimSpec`) at fixed values `a`
is `read_sbr_header`'s callee hypothesis. -/
theorem tlim_glue (kt : Nat) (a : Args) (hT : Reset.TlimSpec kt) :
    Hdr.TlimSpec (TlC0 a) (TlP a) (TlCs a) (Reset.tlimNeed kt) := by
  apply ProcSpec.adapt hT
  intro ⟨R, lb⟩ ra t ⟨hc, hC⟩
  refine ⟨(R, lb, a), ⟨?_, hC⟩, ?_⟩
  · have e : Reset.TlimF lb a t ⋆ R = cell4 (arg0 t + 0x2c#64) lb ⋆ (TlC0 a (arg0 t) ⋆ R) := by
      simp only [Reset.TlimF, Std.ExtHashMap.sep_assoc]
    show _ =⋆ _ ⋆ (_ ⋆ (Reset.TlimF lb a t ⋆ R))
    rw [e]; exact hc
  · intro s ⟨y, hy, hsr, hbp, hsv, hm⟩
    obtain ⟨fl, nl, rfl⟩ := tablelim_keep hy
    refine ⟨hsr, hbp, hsv, sepM (fun _ h => h) (sepM (fun _ h => h) ?_) _ hm⟩
    intro m hm2
    have e : Reset.TlimF lb (limSet a fl nl) t ⋆ R
        = cell4 (arg0 t + 0x2c#64) lb ⋆ (TlC0 (limSet a fl nl) (arg0 t) ⋆ R) := by
      simp only [Reset.TlimF, Std.ExtHashMap.sep_assoc]
    rw [e] at hm2
    exact sepM (fun _ h => h) (sepM (fun _ h => ⟨fl, nl, hy, h⟩) (fun _ h => h)) _ hm2

/-! ## `read_sbr_header` -/

/-- `Hdr.SbW` with `usac` a value. -/
abbrev SbU (s : BitVec 64) (u : BitVec 32) (st : Hdr.HSt) : Mem 64 → Prop :=
  cell4 (s + 0x4#64) st.start ⋆ (cell4 (s + 0x8#64) st.ready ⋆ (cell4 (s + 0x10#64) u
    ⋆ (cell4 (s + 0x18#64) st.reset ⋆ (st.sp =@ (s + 0x1c#64) ⋆ (cell4 (s + 0x24#64) st.amp
    ⋆ (cell4 (s + 0x2c#64) st.lb ⋆ (cell4 (s + 0x30#64) st.lg ⋆ (cell4 (s + 0x34#64) st.ip
    ⋆ cell4 (s + 0x38#64) st.sm))))))))

/-- `Hdr.HF` with `usac = u`. -/
abbrev HFU (x : Hdr.HArgs) (u : BitVec 32) (t : MachineData) (st : Hdr.HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  SbU (arg0 t) u st ⋆ (Hdr.GbW (arg1 t) x st.i ⋆ (Blocks [(x.buf, x.L)] ⋆ Tl))

abbrev HdrPreU (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (y : Hdr.HArgs × BitVec 32) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (Hdr.hdrNeed k) (HFU y.1 y.2 t y.1.st (TlT (arg0 t)) ⋆ y.1.R) ra t ∧ Hdr.HdrC TlC y.1 t

abbrev HdrPostU (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (y : Hdr.HArgs × BitVec 32) (ra : Int64)
    (t s : MachineData) : Prop :=
  ∃ st, Hdr.HdrOut y.1 ((arg2 t).setWidth 32) st ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (Hdr.hdrNeed k)
      (HFU y.1 ((arg2 t).setWidth 32) t st (Hdr.TlOut TlT TlT' y.1 t st) ⋆ y.1.R) ra t s

/-- `Hdr.HdrSpec` with `sbr->usac` a value `u` at entry and `is_usac` at the return. -/
abbrev HdrSpecU (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop) :
    Prop :=
  cenv.ProcSpec (entry "read_sbr_header") (HdrPreU k TlT TlC) (HdrPostU k TlT TlT')

/-- `read_sbr_header`'s own contract gives `HdrSpecU`: at entry the `usac` cell is a block. -/
theorem hdrU_of {k : Nat} {TlT : BitVec 64 → Mem 64 → Prop}
    {TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop} {TlC : BitVec 32 → BitVec 64 → Prop}
    (h : Hdr.HdrSpec k TlT TlT' TlC) : HdrSpecU k TlT TlT' TlC := by
  apply ProcSpec.adapt h
  intro ⟨x, u⟩ ra t ⟨hc, hC⟩
  refine ⟨x, ⟨?_, hC⟩, fun s hs => hs⟩
  have ec : Mem.Entails (cell4 (arg0 t + 0x10#64) u ⋆ (cell4 (arg0 t + 0x18#64) x.st.reset
      ⋆ (x.st.sp =@ (arg0 t + 0x1c#64) ⋆ (cell4 (arg0 t + 0x24#64) x.st.amp
      ⋆ (cell4 (arg0 t + 0x2c#64) x.st.lb ⋆ (cell4 (arg0 t + 0x30#64) x.st.lg
      ⋆ (cell4 (arg0 t + 0x34#64) x.st.ip ⋆ cell4 (arg0 t + 0x38#64) x.st.sm)))))))
      (4 ?@ (arg0 t + 0x10#64) ⋆ (cell4 (arg0 t + 0x18#64) x.st.reset
      ⋆ (x.st.sp =@ (arg0 t + 0x1c#64) ⋆ (cell4 (arg0 t + 0x24#64) x.st.amp
      ⋆ (cell4 (arg0 t + 0x2c#64) x.st.lb ⋆ (cell4 (arg0 t + 0x30#64) x.st.lg
      ⋆ (cell4 (arg0 t + 0x34#64) x.st.ip ⋆ cell4 (arg0 t + 0x38#64) x.st.sm))))))) :=
    fun _ hm => Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
  have e : Mem.Entails (HFU x u t x.st (TlT (arg0 t)) ⋆ x.R)
      (Hdr.HF x t x.st (TlT (arg0 t)) ⋆ x.R) :=
    sepM (sepM (sepM (fun _ h => h) (sepM (fun _ h => h) ec)) (fun _ h => h)) (fun _ h => h)
  exact sepM (fun _ h => h) (sepM (fun _ h => h) e) _ hc

omit [CodeEnv] in
/-- Consequence with a callee contract that depends on the caller's logical variable. -/
theorem ProcSpec.adaptD {e : Kraken.Executable Directive} {l : Int64} {α β : Type}
    {Pre : β → α → Int64 → MachineData → Prop}
    {Post : β → α → Int64 → MachineData → MachineData → Prop}
    {Pre' : β → Int64 → MachineData → Prop} {Post' : β → Int64 → MachineData → MachineData → Prop}
    (hs : ∀ y, e.ProcSpec l (Pre y) (Post y))
    (h : ∀ y ra t, Pre' y ra t → ∃ x, Pre y x ra t ∧ ∀ s, Post y x ra t s → Post' y ra t s) :
    e.ProcSpec l Pre' Post' := by
  intro y ra t hp
  obtain ⟨x, hx, himp⟩ := h y ra t hp
  exact eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, himp _ hst.2⟩) (hs y x ra t hx)

/-- The scalars of `*sbr` `read_sbr_header` does not hold. -/
abbrev ScH (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 s d.a.sampleRate ⋆ (cell4 (s + 0xc#64) d.a.idAac ⋆ (cell4 (s + 0x14#64) d.it
  ⋆ (2 ?@ (s + 0x22#64) ⋆ (4 ?@ (s + 0x28#64) ⋆ (cell4 (s + 0x3c#64) d.a.coupling
  ⋆ (c4 (s + 0x40#64) d.a.k0 ⋆ (16 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x54#64) d.a.kx0
  ⋆ (c4 (s + 0x5c#64) d.a.m0 ⋆ (c4 (s + 0x60#64) d.a.m1
  ⋆ (cell4 (s + 0x64#64) d.a.pushed ⋆ 0x18 ?@ (s + 0x68#64))))))))))))

/-- The tables neither `read_sbr_header` nor `sbr_make_f_tablelim` holds. -/
abbrev TabH (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq ⋆ (98 ?@ (s + 0x4c1f0#64)
  ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
  ⋆ (2 ?@ (s + 0x4c32e#64) ⋆ x.pstart =@ (s + 0x4c33a#64))))))

/-- The caller's part at the `read_sbr_header` call. -/
abbrev FrH (e : Reset.REnv) (c : CA) (d : DS) : Mem 64 → Prop :=
  ScH d c.s ⋆ (DataF d.a.d0 (c.s + 0x80#64) ⋆ (DataF d.a.d1 (c.s + 0x15b40#64)
  ⋆ (d.a.psc =@ (c.s + 0x2b600#64) ⋆ (TabH d.a c.s ⋆ (Block (lab "ceil_log2") 6
  ⋆ (AvW c.ac d.a ⋆ (Grid.JtW ⋆ (Reset.CstR ⋆ (e.Ext ⋆ c.R)))))))))

/-- The header fields of the values `d`, index `i`. -/
def stOf (d : DS) (i : BitVec 32) : Hdr.HSt :=
  ⟨i, d.a.start, d.a.ready, d.a.reset, d.sp, d.amp, BitVec.ofNat 32 d.h.lb,
    BitVec.ofNat 32 d.a.limGains, d.a.interpol, d.a.smooth⟩

/-- `read_sbr_header`'s logical variable at the call. -/
def hxOf (e : Reset.REnv) (c : CA) : Hdr.HArgs :=
  ⟨FrH e c c.d, c.d.a.start, c.d.a.ready, c.d.a.reset, c.d.sp, c.d.amp,
    BitVec.ofNat 32 c.d.h.lb, BitVec.ofNat 32 c.d.a.limGains, c.d.a.interpol, c.d.a.smooth,
    c.r.buf, c.i, c.r.p8, c.r.L⟩

omit [CodeEnv] in
theorem sbrS_h (d : DS) (s : BitVec 64) (i : BitVec 32) (hlb : d.h.lb ≤ 3)
    (hlg : d.a.limGains ≤ 3) :
    SbrS d s = SbU s d.usac (stOf d i) ⋆ (c4 (s + 0x58#64) d.a.kx1 ⋆ ScH d s) := by
  simp only [SbrS, SbU, stOf, ScH, lb_cell _ _ hlb, lb_cell _ _ hlg]
  ac_rfl

omit [CodeEnv] in
theorem tabF_h (x : Args) (s : BitVec 64) :
    TabF x s = (c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1ec#64) x.nlim
      ⋆ (x.ftLow =@ (s + 0x4c252#64) ⋆ (x.ftLim =@ (s + 0x4c2f2#64)
      ⋆ (c4 (s + 0x4c330#64) x.npatch ⋆ x.pnum =@ (s + 0x4c334#64)))))) ⋆ TabH x s := by
  simp only [TabF, TabH]; ac_rfl

omit [CodeEnv] in
theorem perm_h (SU K1 SH D0 D1 Ps N0 NL FL FM NP PN TH Gb Bb Bc Av Jt Cs Bw Ex R :
    Mem 64 → Prop) :
    ((SU ⋆ (K1 ⋆ SH)) ⋆ (D0 ⋆ (D1 ⋆ (Ps ⋆ ((N0 ⋆ (NL ⋆ (FL ⋆ (FM ⋆ (NP ⋆ PN))))) ⋆ TH)))))
      ⋆ (Gb ⋆ ((Bb ⋆ Bc) ⋆ (Av ⋆ (Jt ⋆ (Cs ⋆ (Bw ⋆ Ex)))))) ⋆ R
    = (SU ⋆ (Gb ⋆ (Bb ⋆ (K1 ⋆ (N0 ⋆ (NL ⋆ (FL ⋆ (FM ⋆ (NP ⋆ (PN ⋆ Bw))))))))))
      ⋆ (SH ⋆ (D0 ⋆ (D1 ⋆ (Ps ⋆ (TH ⋆ (Bc ⋆ (Av ⋆ (Jt ⋆ (Cs ⋆ (Ex ⋆ R)))))))))) := by
  ac_rfl

theorem cfh_eq (e : Reset.REnv) (c : CA) (d : DS) (i : BitVec 32) (hlb : d.h.lb ≤ 3)
    (hlg : d.a.limGains ≤ 3) :
    CF (ExtR e) c d i ⋆ c.R = SbU c.s d.usac (stOf d i) ⋆ (Hdr.GbW c.g (hxOf e c) i
      ⋆ (Blocks [(c.r.buf, c.r.L)] ⋆ TlC0 d.a c.s)) ⋆ FrH e c d := by
  simp only [CF, SbrF, ExtR, BufW, Blocks]
  rw [sbrS_h d c.s i hlb hlg, tabF_h]
  exact perm_h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

omit [CodeEnv] in
theorem tablelim_len {lb : Nat} {a y : Args} (h : Tablelim lb a y) : y.ftLim.length = 60 := by
  cases h <;> simp only [mk16_length]

theorem ex_tl {A B C D E F : Mem 64 → Prop} {a : Args} {lb : BitVec 32} {s0 : BitVec 64}
    {m : Mem 64} (h : m =⋆ A ⋆ (B ⋆ ((C ⋆ (D ⋆ (E ⋆ TlP a lb s0))) ⋆ F))) :
    ∃ fl nl, Tablelim lb.toNat a (limSet a fl nl)
      ∧ m =⋆ A ⋆ (B ⋆ ((C ⋆ (D ⋆ (E ⋆ TlC0 (limSet a fl nl) s0))) ⋆ F)) := by
  obtain ⟨m1, m2, hd, hu, hA, m3, m4, hd2, hu2, hB, m5, m6, hd3, hu3,
    ⟨m7, m8, hd4, hu4, hC, m9, m10, hd5, hu5, hD, m11, m12, hd6, hu6, hE, fl, nl, ht, hz⟩,
    hF⟩ := h
  exact ⟨fl, nl, ht, m1, m2, hd, hu, hA, m3, m4, hd2, hu2, hB, m5, m6, hd3, hu3,
    ⟨m7, m8, hd4, hu4, hC, m9, m10, hd5, hu5, hD, m11, m12, hd6, hu6, hE, hz⟩, hF⟩

omit [CodeEnv] in
theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x :=
  BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt)

omit [CodeEnv] in
theorem stOf_eq (x : Args) (st : Hdr.HSt) (it : BitVec 32) (h1 : st.start = 1#32)
    (h2 : st.ready = 0#32) :
    stOf ⟨hdrVals x st, hidOf st.sp st.lb.toNat, 0#32, st.amp, st.sp, it⟩ st.i = st := by
  obtain ⟨i, a, b, r, sp, am, lb, lg, ip, sm⟩ := st
  simp only at h1 h2
  subst h1 h2
  simp only [stOf, ofNat_toNat32]
  rfl

/-- **`read_sbr_header`'s adapter.** -/
theorem hdr_glue (k kt : Nat) (e : Reset.REnv)
    (hH : ∀ TlT TlT' TlC, Hdr.TlimSpec TlT TlT' TlC (Reset.tlimNeed kt) →
      Hdr.HdrSpec k TlT TlT' TlC)
    (hT : Reset.TlimSpec kt) : HdrSpec (Hdr.hdrNeed k) (ExtR e) := by
  refine ProcSpec.adaptD (Pre := fun c : CA => HdrPreU k (TlC0 c.d.a) (TlCs c.d.a))
    (Post := fun c : CA => HdrPostU k (TlC0 c.d.a) (TlP c.d.a))
    (fun c => hdrU_of (hH _ _ _ (tlim_glue kt c.d.a hT))) ?_
  intro c ra t ⟨⟨hcall, hrok, hdok⟩, h0, h1, h2, hmi, hr0, hnw, hlb⟩
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hdok.2.2.2
  have hA : AI c.d.a := hmi.1
  have hI : I1 c.d.a c.d.h := hmi.2
  have hsc : Scal c.d.a := hA.1
  have hlg : c.d.a.limGains ≤ 3 := hsc.2.2.2.2.2.2.1
  refine ⟨(hxOf e c, c.d.usac), ⟨?_, ?_⟩, ?_⟩
  · have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF (ExtR e) c c.d c.i ⋆ c.R)) := hcall
    rw [cfh_eq e c c.d c.i hlb hlg] at hm
    show t.dmem =⋆ _ ⋆ (_ ⋆ (HFU (hxOf e c) c.d.usac t (stOf c.d c.i) (TlC0 c.d.a (arg0 t))
      ⋆ FrH e c c.d))
    simp only [HFU, h0, h1]
    exact hm
  · refine ⟨hdok.1, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2, fun _ hs lb hl _ => ?_⟩
    have hst : c.d.a.start ≠ 0 := by
      intro h; have := hI h
      have e1 : u8 c.d.sp 0 = 255 := by rw [← hdok.2.1]; exact this
      change u8 c.d.sp 0 < 16 at hs
      omega
    obtain ⟨w1, -, -, w4, w5, -, -, -, w9, -, -, -, w13, -, -, -, -, -, -, -, w21⟩ :=
      (hA.2.1 hst).1
    have n1 := (hA.2.1 hst).2.1
    obtain ⟨-, -, -, s4, -, -, -, s8, -, -, s11, s12⟩ := hsc
    refine ⟨by omega, s8, s12, fun _ => by omega, w1, w4, w5, ⟨w9, w13⟩, w21, s4, by omega, ?_⟩
    rw [h0]; omega
  · intro s ⟨st, hout, hsr, hbp, hsv, hm⟩
    rw [h2] at hout hm
    suffices H : ∃ fl nl, (if st.called (hxOf e c)
          then Tablelim st.lb.toNat (hdrVals c.d.a st) (hdrVals (limSet c.d.a fl nl) st)
          else hdrVals (limSet c.d.a fl nl) st = hdrVals c.d.a st) ∧ fl.length = 60
        ∧ s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (Hdr.hdrNeed k) (t.regs.get64 .rsp)
          ⋆ (HFU (hxOf e c) 0#32 t st (TlC0 (limSet c.d.a fl nl) (arg0 t)) ⋆ FrH e c c.d)) by
      obtain ⟨fl, nl, hy, hfl, hmem⟩ := H
      have hlbN : (hxOf e c).lb.toNat = c.d.h.lb := by
        show (BitVec.ofNat 32 c.d.h.lb).toNat = c.d.h.lb
        rw [BitVec.toNat_ofNat]; omega
      obtain ⟨hhi, hid⟩ := hdr_hi hmi hr0 rfl hdok.2.1 hlbN hout hy
      obtain ⟨o1, o2, o3, -, -, -, -, o8, o9, -, -, o12, o13, -, -, -, o17, -⟩ := hout
      let d' : DS := ⟨hdrVals (limSet c.d.a fl nl) st, hidOf st.sp st.lb.toNat, 0#32, st.amp,
        st.sp, c.d.it⟩
      refine ⟨d', st.i, ⟨hhi, hid, rfl, rfl, rfl, rfl, rfl, o8, o9, o12⟩,
        ⟨o3, rfl, rfl, l1, l2, l3, hfl, l5, l6, l7⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, o17,
        hsr, hbp, hsv, ?_⟩
      show s.dmem =⋆ _ ⋆ (_ ⋆ (CF (ExtR e) c d' st.i ⋆ c.R))
      rw [cfh_eq e c d' st.i (by show st.lb.toNat ≤ 3; omega) (by show st.lg.toNat ≤ 3; omega),
        stOf_eq _ _ _ o1 o2]
      simp only [HFU, h0, h1] at hmem
      exact hmem
    by_cases hc : st.called (hxOf e c)
    · have hm' : s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (Hdr.hdrNeed k) (t.regs.get64 .rsp)
          ⋆ (HFU (hxOf e c) 0#32 t st (TlP c.d.a st.lb (arg0 t)) ⋆ FrH e c c.d)) := by
        have := hm; simp only [Hdr.TlOut, if_pos hc] at this; exact this
      obtain ⟨fl, nl, ht, hz⟩ := ex_tl hm'
      exact ⟨fl, nl, by rw [if_pos hc]; exact tablelim_hv st ht, tablelim_len ht, hz⟩
    · refine ⟨c.d.a.ftLim, c.d.a.nlim, by rw [if_neg hc], l4, ?_⟩
      have := hm; simp only [Hdr.TlOut, if_neg hc] at this; exact this

end Kraken.Examples.Sbr.DecExt
