import Kraken.X64.Examples.Sbr.Parse.UsacCall
import Kraken.X64.Examples.Sbr.Parse.UsacBlk25
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: after `sbr_make_f_tablelim` (L35a3) -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

omit [CodeEnv] in
/-- `sbr_make_f_tablelim` only writes `f_tablelim` and `n_lim`. -/
theorem tl_eq {lb : Nat} {x y : Args} (h : Tablelim lb x y) :
    ∃ f n, y = { x with ftLim := f, nlim := n } := by
  cases h with
  | zero _ => exact ⟨_, _, rfl⟩
  | pos _ _ _ _ => exact ⟨_, _, rfl⟩

omit [CodeEnv] in
/-- `sbr_make_f_tablelim` does not read `start`. -/
theorem tl_start {lb : Nat} {x y : Args} (h : Tablelim lb x y) :
    Tablelim lb { x with start := 1#32 } { y with start := 1#32 } := by
  cases h with
  | zero h0 => exact Tablelim.zero h0
  | pos h1 h2 h3 h4 => exact Tablelim.pos h1 h2 h3 h4

omit [CodeEnv] in
/-- The default header with a changed `bs_limiter_bands` and no reset: a `Header true` step
through `sbr_make_f_tablelim`. -/
theorem hi_tl {A : UA} {t₀ : MachineData} {st : USt} {y : Args} (hI : Inv A st) (hS : S1 t₀ st)
    (hU : UeC A.1) (hr : (dhR A.1 st).x.reset = 0#32) (hlb : u8 A.1.uev 6 ≠ st.h.lb)
    (ht : Tablelim (u8 A.1.uev 6) (dhR A.1 st).x y) :
    HI ({ y with start := 1#32 }, (dhR A.1 st).h) := by
  have hm : MI (st.x, st.h) := hS.1.1
  have hr0 : st.x.reset = 0 := hS.1.2.1
  have hl := hI.2.1.1
  have he : dsp A.1 st = st.sp := by
    by_cases h : dsp A.1 st = st.sp
    · exact h
    · simp only [dhR, h, ↓reduceIte] at hr; exact absurd hr (by decide)
  have hs : u8 A.1.uev 1 = st.h.start := by
    rw [← hI.2.1.2.1]
    show (A.1.uev.getD 1 0).toNat = (st.sp.getD 0 0).toNat
    rw [← dsp_getD0 _ _ hl, he]
  rw [dhR_eq _ _ he hr0] at ht ⊢
  have hh := Header.mk (usac := true) (x := st.x) (h := st.h) (u8 A.1.uev 1) st.h.xover
    (u8 A.1.uev 6) (u8 A.1.uev 7) st.x.ready (BitVec.ofNat 32 (u8 A.1.uev 8 % 2))
    (BitVec.ofNat 32 (u8 A.1.uev 8 / 2 % 2)) false hU.2.1 (fun h => Bool.noConfusion h)
    (fun _ => rfl) hU.2.2.1 hU.2.2.2.1 (Or.inr rfl) (fun hne => absurd hs hne)
    (HdrLim.lim hlb hr0 (tl_start ht))
  exact (hdr_spec hm hr0 (Or.inr hh)).1

set_option maxRecDepth 20000 in
/-- `jmp`: on to `start = 1`. -/
theorem blk_L35a3 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35a3" := by
  cfg_block
  measure_hb "L35a3"
    intro n
    simp only [tbl_L35a3, var_L35a3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, y, hI, hS, hr, hlb, ht, hLy, hm⟩, h15⟩ :=
      hs₀.1
    obtain rfl := hs₀.2
    have hU : UeC A.1 := hF.1.2.2.2.2.1
    have hi := hi_tl hI hS hU hr hlb ht
    obtain ⟨f, n', rfl⟩ := tl_eq ht
    have hmc : PLift (s₀.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
      { dhR A.1 st with x := { (dhR A.1 st).x with ftLim := f, nlim := n' } }) := ⟨hm⟩
    have hbxc : PLift (s₀.regs.get64 .rbx = A.1.c) := ⟨hbx⟩
    have hIv := inv_dhR hI hU
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) _ = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ?_, ?_⟩
    · rw [tbl_L35b5]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_,
        { dhR A.1 st with x := { (dhR A.1 st).x with ftLim := f, nlim := n' } },
        ⟨hIv.1, ⟨hIv.2.1.1, hIv.2.1.2.1, hIv.2.1.2.2.1, hIv.2.1.2.2.2.1, hLy⟩, hIv.2.2⟩,
        ⟨hi, hS.2, hS.1.2.2, spw_dhR hI hU⟩, hmc.down⟩, ?_⟩
      all_goals first
        | exact hsp | exact hbp | exact h12 | exact h14 | exact hbxc.down
        | exact h13 | exact h15
    · first
        | exact Or.inr ⟨by simp only [var_L35b5], by decide⟩
        | exact Or.inl (by simp only [var_L35b5]; omega)

omit [CodeEnv] in
/-- A header writes no field of `UKeep` and leaves `start = 1`. -/
theorem hdr_keep {usac : Bool} {s s' : St} (hh : Header usac s s') :
    UKeep s.1 s'.1 ∧ s'.1.start = 1#32 := by
  cases hh with
  | mk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl =>
    cases hl with
    | keep _ => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
    | lim _ _ ht =>
      obtain ⟨f, n, rfl⟩ := tl_eq ht
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

omit [CodeEnv] in
theorem with_start_eq {x : Args} (h : x.start = 1#32) : { x with start := 1#32 } = x := by
  rw [← h]

omit [CodeEnv] in
/-- The header contract's conclusion from `S1`: `Inv`, and `HI` with `start = 1`. -/
theorem hdr_ok {A : UA} {t₀ : MachineData} {st st' : USt} (hI : Inv A st) (hS : S1 t₀ st)
    (hrel : Header true (st.x, st.h) (st'.x, st'.h) ∧ st'.u = 1#32 ∧ SpOk st'
      ∧ st'.i.toNat ≤ A.1.p8.toNat ∧ u8 st'.sp 3 < 4 ∧ u8 st'.sp 4 < 2) :
    Inv A st' ∧ (HI ({ st'.x with start := 1#32 }, st'.h) ∧ st'.x.idAac = idv t₀
      ∧ st'.u = 1#32 ∧ SpW st') := by
  obtain ⟨hh, hu, hsp, hi, h3, h4⟩ := hrel
  obtain ⟨hHI, hid⟩ := hdr_spec hS.1.1 hS.1.2.1 (Or.inr hh)
  obtain ⟨hk, hs⟩ := hdr_keep hh
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hk
  obtain ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ := hI.1
  refine ⟨⟨⟨k1.trans j1, k2.trans j2, k3.trans j3, k4.trans j4, k5.trans j5, k6.trans j6,
    k7.trans j7, k8.trans j8⟩, hsp, hi⟩, ?_, hid.trans hS.2, hu,
    fun _ => ⟨by omega, by omega⟩⟩
  have e : { st'.x with start := 1#32 } = st'.x := with_start_eq hs
  rw [e]; exact hHI

/-- `read_sbr_header(sbr, gb, 1)`. -/
theorem blk_L35a5 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData)
    (hc : HeaderSpec k A.1.Ext A.1.Oth) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L35a5" := by
  cfg_block
  measure_hb "L35a5"
    intro n
    simp only [tbl_L35a5, var_L35a5, tbl_L35b5, var_L35b5]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hS, hm⟩, h15⟩, rfl⟩ := hs₀
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
      "read_sbr_header" hc]
    all_goals try call_simp
    have hs1 := ‹_ = s₀›
    subst hs1
    refine ⟨fun ra' => ⟨⟨⟨?_, trivial, trivial⟩, h13, h14, ?_, hS.1.1, hS.1.2.1, hI.2.1, hI.2.2,
      hF.1.2.2.2.1,
      hF.1.2.2.2.2.2.2.1⟩,
      fun s' hpost => ?_⟩, fun _ => Or.inr (Or.inr (Or.inl trivial)), hld⟩
    · rw [e50]; exact hpush _
    · first | rfl | decide | simp
    · obtain ⟨st', hrel, hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      rw [e50] at hm'
      obtain ⟨hI', hP⟩ := hdr_ok hI hS hrel
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st', hI', hP, hm'⟩, ?_⟩, Nat.le_refl _⟩
      · exact hsp'.trans e72
      · exact hbp'.trans hbp
      · exact h12'.trans h12
      · exact hbx'.trans hbx
      · exact h14'.trans h14
      · exact h13'.trans h13
      · rw [h15']; exact h15

end Kraken.Examples.Sbr.Usac
