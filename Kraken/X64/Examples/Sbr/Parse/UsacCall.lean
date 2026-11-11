import Kraken.X64.Examples.Sbr.Parse.UsacGrd2
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the call of `sbr_reset`

`ResetSpec`'s conclusion from `HI` gives `MI` (as `ParseModel.reset_step`). -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- The reset contract's conclusion from `HI`: `Inv`, `MI`, `id_aac` kept, `usac` kept or `0`. -/
theorem reset_ok {A : UA} {st st' : USt} (hI : Inv A st) (hh : HI (st.x, st.h))
    (hpost : Scal st'.x ∧ ∃ y, TFrame st.x y ∧ UKeep st.x y
      ∧ ((st'.x = y.turnoff ∧ st'.h = st.h.turnoff ∧ st'.u = 0#32)
        ∨ (st'.x = y ∧ st'.h = st.h ∧ st'.u = st.u ∧ TabWF y ∧ 1 ≤ y.n0 ∧ 1 ≤ y.npatch))
      ∧ st' = { st with x := st'.x, h := st'.h, sp := st'.sp, u := st'.u } ∧ SpOk st') :
    Inv A st' ∧ MI (st'.x, st'.h) ∧ st'.x.idAac = st.x.idAac
      ∧ (st'.u = st.u ∨ st'.u = 0#32) := by
  obtain ⟨sc, y, ht, hk, hc, hst, hsp⟩ := hpost
  obtain ⟨-, -, -, a4, a5, a6, a7, i1⟩ := hh
  obtain ⟨d0, d1⟩ := dwf_tframe ht a4 a5
  have hg := gridInv_tframe ht a7
  obtain ⟨-, -, -, hzs, hzid, hzpc, hzph, -, -, -, -, -⟩ := ht
  have hi : st'.i = st.i := by rw [hst]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hk
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ := hI.1
  have hk' : UKeep A.2.x y :=
    ⟨k1.trans j1, k2.trans j2, k3.trans j3, k4.trans j4, k5.trans j5, k6.trans j6, k7.trans j7,
      k8.trans j8⟩
  have hp : PsWF y.psc y.psh := by rw [hzpc, hzph]; exact a6
  rcases hc with ⟨hx, hh', hu⟩ | ⟨hx, hh', hu, tz, n1, n2⟩
  · rw [hx] at sc
    refine ⟨⟨?_, hsp, hi ▸ hI.2.2⟩, ?_, ?_, Or.inr hu⟩
    · rw [hx]; exact hk'
    · rw [hx, hh']
      exact ⟨⟨sc, fun h => absurd rfl h, d0, d1, hp, hg⟩, fun _ => rfl⟩
    · rw [hx]; exact hzid
  · rw [hx] at sc
    refine ⟨⟨?_, hsp, hi ▸ hI.2.2⟩, ?_, ?_, Or.inl hu⟩
    · rw [hx]; exact hk'
    · rw [hx, hh']
      exact ⟨⟨sc, fun _ => ⟨tz, n1, n2⟩, d0, d1, hp, hg⟩, fun h0 => i1 (hzs ▸ h0)⟩
    · rw [hx]; exact hzid

omit [CodeEnv] in
/-- The call's return slot at `r - 0x50` is 16-byte aligned plus 8. -/
theorem al_usac (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) :
    isAligned 16 (r - 80#64 + 8#64) = true := by
  simp only [isAligned, beq_iff_eq] at *
  have e : r - 80#64 + 8#64 = (r + 8#64) - 80#64 := by bv_omega
  rw [e, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

/-- `sbr_reset(ac, sbr)` with a reset pending. -/
theorem blk_L35ea (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : ResetSpec k A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35ea" := by
  cfg_block
  measure_hb "L35ea"
    intro n
    simp only [tbl_L35ea, var_L35ea, tbl_L35f5, var_L35f5]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, ⟨⟨hhi, hid, hu, hw⟩, hz⟩, hm⟩, h15⟩,
      rfl⟩ :=
      hs₀
    simp only [UM] at hm
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) st)
      "sbr_reset" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    have hrsp := hF.2.2.2.2.2
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h12, h13, hz, hhi.2.2.1 hz, hhi.1, hI.2.1,
      (hw hz).1,
      (hw hz).2, hF.1.2.2.2.2.2.2.1, ?_⟩, fun s' hpost => ?_⟩,
        fun _ => Or.inr (Or.inr (Or.inl trivial)),
      hld⟩
    · rw [e50]; exact hpush _
    · rw [e50]; exact al_usac _ hrsp
    · obtain ⟨st', hrel, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      obtain ⟨hI', hmi', hid', hu'⟩ := reset_ok hI hhi hrel
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', hI',
        ⟨hmi', hid'.trans hid, hu'.imp (fun h => h.trans hu) id⟩,
        hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [h15']; exact h15

omit [CodeEnv] in
/-- No change of the default header (`reset = 0`): the decoder was started, its tables are
`TabWF`; `Scal` with the new `bs_limiter_gains`. -/
theorem dhr_tab {A : UA} {t₀ : MachineData} {st₀ : USt} (hI : Inv A st₀) (hS : S1 t₀ st₀)
    (hue : UeC A.1) (hr : (dhR A.1 st₀).x.reset = 0#32) :
    Scal (dhR A.1 st₀).x ∧ TabWF (dhR A.1 st₀).x ∧ 1 ≤ (dhR A.1 st₀).x.n0
      ∧ 1 ≤ (dhR A.1 st₀).x.npatch := by
  obtain ⟨hl, hs0, -, -⟩ := hI.2.1
  have hmi := hS.1.1
  have he : dsp A.1 st₀ = st₀.sp := by
    by_cases h : dsp A.1 st₀ = st₀.sp
    · exact h
    · simp only [dhR, h, ↓reduceIte] at hr; exact absurd hr (by decide)
  have h0 : u8 (dsp A.1 st₀) 0 = u8 A.1.uev 1 := by
    simp only [dsp, u8, ub, List.getD_eq_getElem?_getD, List.getElem?_set, hl]
    simp
  have hst : st₀.h.start < 16 := by
    rw [← hs0, ← he, h0]; exact hue.2.1
  have hx : st₀.x.start ≠ 0 := fun h => by
    have h' : st₀.h.start = 255 := hmi.2 h
    omega
  obtain ⟨tw, n1, n2⟩ := hmi.1.2.1 hx
  obtain ⟨b1, b2, b3, b4, b5, b6, -, b8, b9, b10, b11, b12⟩ := hmi.1.1
  exact ⟨⟨b1, b2, b3, b4, b5, b6, by show u8 A.1.uev 7 ≤ 3; have := hue.2.2.2.1; omega,
    b8, b9, b10, b11, b12⟩, tw, n1, n2⟩

/-- `sbr_make_f_tablelim(sbr)`: `bs_limiter_bands` changed, no reset. -/
theorem blk_L359b (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : TablelimSpec k A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L359b" := by
  cfg_block
  measure_hb "L359b"
    intro n
    simp only [tbl_L359b, var_L359b, tbl_L35a3, var_L35a3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st₀, hI, hS, hr, hlb, hm⟩, h15⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    obtain ⟨sc, tw, n1, n2⟩ := dhr_tab hI hS hF.1.2.2.2.2.1 hr
    have e50 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 80#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 = _; bv_omega
    have e72 : s₀.regs.get64 .rsp - Width.W64.bytesv + 8 = t₀.regs.get64 .rsp - 72#64 := by
      rw [hsp]; show _ - 72#64 - 8#64 + 8#64 = _; bv_omega
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - Width.W64.bytesv) 8).isSome = true := by
      rw [e50]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen [call_procA_spec_at (cA A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (dhR A.1 st₀))
      "sbr_make_f_tablelim" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    have hU := hF.1.2.2.2.2.1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h13, sc, tw, n1, n2,
      (by show u8 A.1.uev 6 ≤ 3; have := hU.2.2.1; omega), hI.2.1.2.2.2.2, hF.1.2.2.2.2.2.2.1⟩,
      fun s' hpost => ?_⟩, fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · obtain ⟨st', ⟨y, hy, hst', hLy⟩, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50, hst'] at hm'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st₀, y, hI, hS, hr, hlb, hy, hLy, hm'⟩, ?_⟩,
        Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [h15']; exact h15

end Kraken.Examples.Sbr.Usac
