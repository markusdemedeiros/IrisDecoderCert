import Kraken.X64.Examples.Sbr.Parse.DecExtGlue
import Kraken.X64.Examples.Sbr.Parse.DtdfSpec
import Kraken.X64.Examples.Sbr.Parse.InvfSpec

/-!
# `ff_aac_sbr_decode_extension`: the channel callees' adapters

The local contracts of `DecExtSpec` for the routines that read one channel `ch_data` (at
`sbr + 0x80` or `sbr + 0x15b40`, `chA`) follow from the routines' own statements.

* `cf_ch`: the caller's `CF` is the channel's `DataF` and the rest; `DataF` splits into the
  cells a callee owns and the rest.
* `dtdf_glue`: `read_sbr_dtdf`'s statement (`Dtdf.DtdfPre`/`DtdfPost`, at stack need `k`) gives
  the local `DtdfSpec k`.
* `invf_glue`: `read_sbr_invf`'s statement (`Invf.InvfSpec`, stack need 0) gives the local
  `InvfSpec 0`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

/-! ## The channel -/

/-- The decoder state but `sbr->data[b]`. -/
abbrev SbrO (d : DS) (s : BitVec 64) (b : Bool) : Mem 64 → Prop :=
  SbrS d s ⋆ (DataF (chV d !b) (chA s !b) ⋆ (d.a.psc =@ (s + 0x2b600#64) ⋆ TabF d.a s))

omit [CodeEnv] in
theorem sbrF_ch (d : DS) (s : BitVec 64) (b : Bool) :
    SbrF d s = DataF (chV d b) (chA s b) ⋆ SbrO d s b := by
  cases b <;> simp only [SbrF, SbrO, chV, chA, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte] <;> ac_rfl

/-! ## `read_sbr_dtdf` -/

/-- `DataF` but `bs_num_env`, `bs_num_noise`, `bs_df_env ++ bs_df_noise`. -/
abbrev DataD (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (v.freqRes =@ (d + 0xc#64)
  ⋆ (3 ?@ (d + 0x15#64) ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64)
  ⋆ (4 ?@ (d + 0x64#64) ⋆ (0x3898 ?@ (d + 0x68#64) ⋆ (cell4 (d + 0x3900#64) v.vOff
  ⋆ (4 ?@ (d + 0x3904#64) ⋆ (4 ?@ (d + 0x3908#64) ⋆ (0x4014 ?@ (d + 0x390c#64)
  ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ (0xe178 ?@ (d + 0x7924#64) ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
  ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx ⋆ 12 ?@ (d + 0x15ab4#64)))))))))))))))))))

omit [CodeEnv] in
theorem dataF_d (v : DV) (d : BitVec 64) :
    DataF v d = (c4 (d + 8#64) v.nenv ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ 11 ?@ (d + 0x1c#64)))
      ⋆ DataD v d := by
  simp only [DataF, DataD]; ac_rfl

/-- The caller's part at the `read_sbr_dtdf` call. -/
abbrev FrD (Ext : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) : Mem 64 → Prop :=
  DataD (chV d b) (chA c.s b) ⋆ (SbrO d c.s b ⋆ (Block (lab "ceil_log2") 6
    ⋆ (AvW c.ac d.a ⋆ (Grid.JtW ⋆ (Ext ⋆ c.R)))))

omit [CodeEnv] in
theorem perm_d (N Q F D O Gb Bb Bc Av Jt Ex R : Mem 64 → Prop) :
    (((N ⋆ (Q ⋆ F)) ⋆ D) ⋆ O) ⋆ (Gb ⋆ ((Bb ⋆ Bc) ⋆ (Av ⋆ (Jt ⋆ Ex)))) ⋆ R
      = (N ⋆ (Q ⋆ (F ⋆ (Gb ⋆ Bb)))) ⋆ (D ⋆ (O ⋆ (Bc ⋆ (Av ⋆ (Jt ⋆ (Ex ⋆ R)))))) := by
  ac_rfl

theorem cfd_eq (Ext : Mem 64 → Prop) (c : CA) (d : DS) (i : BitVec 32) (b : Bool) :
    CF Ext c d i ⋆ c.R = (c4 (chA c.s b + 8#64) (chV d b).nenv
      ⋆ (c4 (chA c.s b + 0x18#64) (chV d b).nnoise ⋆ (11 ?@ (chA c.s b + 0x1c#64)
      ⋆ (GbR c.g c.r i ⋆ Blocks [(c.r.buf, c.r.L)])))) ⋆ FrD Ext c d b := by
  simp only [CF, BufW, Blocks, FrD]
  rw [sbrF_ch d c.s b, dataF_d]
  exact perm_d _ _ _ _ _ _ _ _ _ _ _ _

/-- `read_sbr_dtdf`'s logical variable at the call. -/
abbrev dxOf (Ext : Mem 64 → Prop) (c : CA) (b : Bool) : Dtdf.DArgs :=
  ⟨FrD Ext c c.d b, chV c.d b, c.r.buf, c.i, c.r.p8, c.r.L⟩

omit [CodeEnv] in
theorem ch_of {s a : BitVec 64} (h : a = s + 0x80#64 ∨ a = s + 0x15b40#64) :
    ∃ b, a = chA s b := by
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

/-- **`read_sbr_dtdf`'s adapter.** -/
theorem dtdf_glue (k : Nat) (Ext : Mem 64 → Prop)
    (hD : cenv.ProcSpec (entry "read_sbr_dtdf") (Dtdf.DtdfPre k) (Dtdf.DtdfPost k)) :
    DtdfSpec k Ext := by
  intro c ra t ⟨⟨hcall, hrok, hdok⟩, _, h1, h2, _, n0, q0, n1, q1⟩
  obtain ⟨b, hb⟩ := ch_of h2
  have hpre : Dtdf.DtdfPre k (dxOf Ext c b) ra t := by
    refine ⟨?_, ?_, ?_, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2⟩
    · have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF Ext c c.d c.i ⋆ c.R)) := hcall
      rw [cfd_eq Ext c c.d c.i b] at hm
      show t.dmem =⋆ _ ⋆ (_ ⋆ (Dtdf.DtdfF (dxOf Ext c b) t c.i ⋆ FrD Ext c c.d b))
      simp only [Dtdf.DtdfF, hb, h1]
      exact hm
    · cases b <;> assumption
    · cases b <;> assumption
  refine eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, ?_⟩) (hD _ ra t hpre)
  obtain ⟨i', hi, hsr, hbp, hsv, hm⟩ := hst.2
  refine ⟨c.d, i', rfl, hdok, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hi, hsr, hbp, hsv, ?_⟩
  show st.1.dmem =⋆ _ ⋆ (_ ⋆ (CF Ext c c.d i' ⋆ c.R))
  rw [cfd_eq Ext c c.d i' b]
  simp only [Dtdf.DtdfF, hb, h1] at hm
  exact hm

/-! ## `read_sbr_invf` -/

/-- `DataF` but `bs_invf_mode`. -/
abbrev DataI (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
  ⋆ (3 ?@ (d + 0x15#64) ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (11 ?@ (d + 0x1c#64)
  ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64)
  ⋆ (4 ?@ (d + 0x64#64) ⋆ (0x3898 ?@ (d + 0x68#64) ⋆ (cell4 (d + 0x3900#64) v.vOff
  ⋆ (4 ?@ (d + 0x3904#64) ⋆ (4 ?@ (d + 0x3908#64) ⋆ (0x4014 ?@ (d + 0x390c#64)
  ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ (0xe178 ?@ (d + 0x7924#64) ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
  ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx ⋆ 12 ?@ (d + 0x15ab4#64)))))))))))))))))))))

omit [CodeEnv] in
theorem dataF_i (v : DV) (d : BitVec 64) :
    DataF v d = v.invf =@ (d + 0x27#64) ⋆ DataI v d := by
  simp only [DataF, DataI]; ac_rfl

/-- `TabF` but `n_q`. -/
abbrev TabQ (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1
  ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (x.ftLow =@ (s + 0x4c252#64)
  ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
  ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (2 ?@ (s + 0x4c32e#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
  ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64)))))))))))

omit [CodeEnv] in
theorem tabF_q (x : Args) (s : BitVec 64) :
    TabF x s = c4 (s + 0x4c1e8#64) x.nq ⋆ TabQ x s := by
  simp only [TabF, TabQ]; ac_rfl

/-- The caller's part at the `read_sbr_invf` call. -/
abbrev FrI (Ext : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) : Mem 64 → Prop :=
  DataI (chV d b) (chA c.s b) ⋆ (SbrS d c.s ⋆ (DataF (chV d !b) (chA c.s !b)
    ⋆ (d.a.psc =@ (c.s + 0x2b600#64) ⋆ (TabQ d.a c.s ⋆ (Block (lab "ceil_log2") 6
    ⋆ (AvW c.ac d.a ⋆ (Grid.JtW ⋆ (Ext ⋆ c.R))))))))

omit [CodeEnv] in
theorem perm_i (I D Sc Do Ps Nq TQ Gb Bb Bc Av Jt Ex R : Mem 64 → Prop) :
    ((I ⋆ D) ⋆ (Sc ⋆ (Do ⋆ (Ps ⋆ (Nq ⋆ TQ))))) ⋆ (Gb ⋆ ((Bb ⋆ Bc) ⋆ (Av ⋆ (Jt ⋆ Ex)))) ⋆ R
      = (Nq ⋆ (I ⋆ (Gb ⋆ Bb))) ⋆ (D ⋆ (Sc ⋆ (Do ⋆ (Ps ⋆ (TQ ⋆ (Bc ⋆ (Av ⋆ (Jt ⋆ (Ex ⋆ R))))))))) := by
  ac_rfl

theorem cfi_eq (Ext : Mem 64 → Prop) (c : CA) (d : DS) (i : BitVec 32) (b : Bool) :
    CF Ext c d i ⋆ c.R = (c4 (c.s + 0x4c1e8#64) d.a.nq ⋆ ((chV d b).invf =@ (chA c.s b + 0x27#64)
      ⋆ (GbR c.g c.r i ⋆ Blocks [(c.r.buf, c.r.L)]))) ⋆ FrI Ext c d b := by
  simp only [CF, BufW, Blocks, FrI]
  rw [sbrF_ch d c.s b, dataF_i, SbrO, tabF_q]
  exact perm_i _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `DS.invf` on the channel `b`. -/
abbrev DS.invfB (d : DS) (b : Bool) (vals : Nat → Nat) : DS := d.invf (if b then 1 else 0) vals

theorem frI_invf (Ext : Mem 64 → Prop) (c : CA) (d : DS) (b : Bool) (vals : Nat → Nat) :
    FrI Ext c (d.invfB b vals) b = FrI Ext c d b := by
  cases b <;> rfl

omit [CodeEnv] in
theorem chV_invf (d : DS) (b : Bool) (vals : Nat → Nat) :
    chV (d.invfB b vals) b = invfRead d.a.nq (chV d b) vals := by
  cases b <;> rfl

omit [CodeEnv] in
theorem nq_invf (d : DS) (b : Bool) (vals : Nat → Nat) : (d.invfB b vals).a.nq = d.a.nq := by
  cases b <;> rfl

omit [CodeEnv] in
theorem ch_sel {s a : BitVec 64} {b : Bool} (h : a = chA s b) :
    (if a = s + 0x80#64 then 0 else 1) = (if b then 1 else 0) := by
  cases b
  · simp [h]
  · have : ¬ (s + 0x15b40#64 = s + 0x80#64) := by bv_omega
    simp [h, this]

/-- `read_sbr_invf`'s logical variable at the call. -/
abbrev ixOf (Ext : Mem 64 → Prop) (c : CA) (b : Bool) : Invf.IArgs :=
  ⟨FrI Ext c c.d b, c.d.a.nq, (chV c.d b).invf, c.r.buf, c.i, c.r.p8, c.r.L⟩

/-- **`read_sbr_invf`'s adapter.** -/
theorem invf_glue (Ext : Mem 64 → Prop) (hI : Invf.InvfSpec) : InvfSpec 0 Ext := by
  intro c ra t ⟨⟨hcall, hrok, hdok⟩, h0, h1, h2, hnq, l0, l1⟩
  obtain ⟨b, hb⟩ := ch_of h2
  have hpre : Invf.InvfPre (ixOf Ext c b) ra t := by
    refine ⟨?_, hnq, ?_, hrok.1, hrok.2.1, hrok.2.2.1, hrok.2.2.2⟩
    · have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF Ext c c.d c.i ⋆ c.R)) := hcall
      rw [cfi_eq Ext c c.d c.i b] at hm
      show t.dmem =⋆ _ ⋆ (_ ⋆ (Invf.IF (ixOf Ext c b) t (chV c.d b).invf c.i ⋆ FrI Ext c c.d b))
      simp only [Invf.IF, hb, h0, h1]
      exact hm
    · cases b <;> assumption
  refine eventually_weaken _ _ _ _ (fun st hst => ⟨hst.1, ?_⟩) (hI _ ra t hpre)
  obtain ⟨vals, i', -, hi, hsr, hbp, hsv, hm⟩ := hst.2
  refine ⟨c.d.invfB b vals, i', ⟨vals, by rw [ch_sel hb]⟩, ?_, ?_, hi, hsr, hbp, hsv, ?_⟩
  · cases b <;> exact hdok
  · cases b <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show st.1.dmem =⋆ _ ⋆ (_ ⋆ (CF Ext c (c.d.invfB b vals) i' ⋆ c.R))
    rw [cfi_eq Ext c _ i' b, frI_invf, chV_invf, nq_invf, ← Invf.invf_model]
    simp only [Invf.IF, hb, h0, h1] at hm
    exact hm

end Kraken.Examples.Sbr.DecExt
