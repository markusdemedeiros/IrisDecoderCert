import Kraken.X64.Examples.Sbr.Parse.ResetPat5

/-!
# `sbr_reset`: the end of the patch loop (`L320e`): drop a last patch narrower than 3
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

/-- The loop's normal end gives `sbr_hf_calc_npatches`'s success values. -/
theorem rsC_tail {a : RArgs} {c : PCx} {f : Nat → Nat} {ki : Nat} {r : PL} {N : Nat}
    (hF : PFix a c f) (hk : KInit f c.nm (ptop a c f) (goalSb a.x.sampleRate.toInt) ki)
    (hr : PR a c f (pinit a c f ki) r true)
    (hN1 : 1 < r.np ∧ u8 r.pn (r.np - 1) < 3 → N = r.np - 1)
    (hN2 : ¬ (1 < r.np ∧ u8 r.pn (r.np - 1) < 3) → N = r.np) :
    TailOk a { pxs a c f r with npatch := N } ∧ TlimIn a { pxs a c f r with npatch := N } := by
  obtain ⟨e0, h0x, hx32, et, hxn, h64', hnm, hxo, hmono⟩ := rsB_fix hF
  simp only [pk0, pkx, ptop] at e0 h0x hx32 et hxn
  have hF' := hF
  obtain ⟨hM, h64, h32, hq1, hq5, hTl, -⟩ := hF'
  have hP := Patches.run (sr := a.x.sampleRate.toInt) (k0 := (x0D a c.k0).k0)
    (kx1 := f (xoOf a)) (m1 := f c.nm - f (xoOf a)) (x := px0 a c f) ki hk hr
  have hy : ({ pxs a c f r with npatch := N } : Args) = { px0 a c f with
      npatch := if true = true ∧ 1 < r.np ∧ u8 r.pn (r.np - 1) < 3 then r.np - 1 else r.np,
      pnum := r.pn, pstart := r.pst } := by
    by_cases h : 1 < r.np ∧ u8 r.pn (r.np - 1) < 3
    · rw [hN1 h, ite_eq_left_iff.mpr (fun h' => absurd ⟨rfl, h⟩ h')]
    · rw [hN2 h, ite_eq_right_iff.mpr (fun h' => absurd h'.2 h)]
  rw [hy]
  refine ⟨⟨c.k0, c.nm, f, c.q, hM, h64, h32, hq1, hq5, hP⟩, ?_⟩
  have hm1 := hmono (xoOf a) c.nm (by omega) (Nat.le_refl _)
  obtain ⟨hn6, hl6, -, hb, -⟩ := patches_spec (show c.k0.toNat ≤ 32 by omega)
    (show c.k0.toNat ≤ f (xoOf a) by omega) (show 1 ≤ f c.nm - f (xoOf a) by omega)
    (fun i hi => by have := hmono i c.nm hi (Nat.le_refl _); omega) hP
  obtain ⟨h1, -, hps⟩ := hb rfl
  obtain ⟨t1, -, -, t4, t5, -, t7, -, t9, t10⟩ := hTl
  exact ⟨t1, hn6, fun _ => Nat.le_trans h1 (Nat.le_add_left _ _), t4, t5, hl6, t7, hps, t9, t10⟩

/-- A byte of a list read with `loadInt … 1`. -/
theorem rsC_b1 (l : List UInt8) (o : Nat) (h : o < l.length) :
    (BitVec.ofInt 8 (Int.ofBytes (slice l o 1))).toNat = u8 l o := by
  have e : slice l o 1 = [l[o]] := by
    apply List.ext_getElem (by simp only [slice, List.length_take, List.length_drop,
      List.length_cons, List.length_nil]; omega)
    intro j h1 h2
    simp only [List.length_cons, List.length_nil] at h2
    simp only [slice, List.getElem_take, List.getElem_drop]
    rcases j with _ | j
    · rfl
    · omega
  rw [e, Int.ofBytes_cons]
  unfold u8
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  simp only [Option.getD_some, show Int.ofBytes [] = 0 from rfl, BitVec.toNat_ofInt]
  have := UInt8.toNat_lt l[o]
  omega

theorem rsC_dec {x : Nat} (h1 : 1 ≤ x) (h : x < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 x) - 1#32)
      = BitVec.ofNat 64 (x - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem rsC_dec32 {x : Nat} (h1 : 1 ≤ x) (h : x < 2 ^ 32) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 x) - 1#32).toNat = x - 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- Drop a last patch narrower than 3. -/
theorem blk_L320e (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L320e" ⟨"sbr_reset.L320e", B.L320e, some "sbr_reset.L3228"⟩ := by
  info_off
  measure_hb "L320e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨ki, r, hk, hrun, hI, hx, hcx, h12⟩, hm⟩ := T.L320e.mp hs
    clear hs
    have hT := fun N => rsC_tail (N := N) hFx hk hrun
    have PX := PLift.up hx
    have hnp6 : r.np ≤ 6 := hI.2.2.2.2.2.1
    have hpl : r.pn.length = 6 := hI.2.2.2.2.2.2.2.1
    have hstp : st.x.pnum = r.pn := by rw [hx]
    have hLB : 2 ≤ r.np → loadInt s₀.dmem (t₀.regs.get64 .rsi + BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofNat 64 r.np) - 1#32) + 312116#64) 1
          = some (Int.ofBytes (slice r.pn (r.np - 1) 1)) := fun h2 => by
      have ha : t₀.regs.get64 .rsi + BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofNat 64 r.np) - 1#32) + 312116#64
            = arg1 t₀ + 0x4c334#64 + BitVec.ofNat 64 (r.np - 1) := by
        rw [rsC_dec (by omega) (by omega)]; simp only [arg1]; bv_omega
      have := region_load (o := r.np - 1) (n := 1) (focus (Mm_pnum ..) hm) ha
        (by rw [hstp]; omega) (by rw [hstp, hpl]; decide)
      rw [hstp] at this; exact this
    have ld := c4_isSome (focus (Mm_npatch ..) hm)
    have S1 : PLift (∀ w : Int, Int.toBytes 4 w = Int.toBytes 4 ((r.np - 1 : Nat) : Int) →
        s₀.dmem.storeInt (arg1 t₀ + 0x4c330#64) 4 w
          =⋆ Mm k e a ra t₀ { st with x := { st.x with npatch := r.np - 1 } } fr) :=
      ⟨fun w hw => Mm_upd_npatch .. ▸ c4_store (focus (Mm_npatch ..) hm) w _ hw⟩
    have P12 : PLift (s₀.regs.get64 .r12 = arg1 t₀) := ⟨h12⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    clear hFx hk hrun hI hx h40 h30 h38 h48 h50 h80 hrbp
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L320e]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, cc_c_sub, not_dec_true, not_dec_false,
        decide_eq_true_eq, decide_eq_false_iff_not, hcx, P12.down, BitVec.toNat_setWidth,
        BitVec.toNat_ofNat] at *
    · -- `jb L3228`: fewer than two patches
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L3228.mpr ⟨hC, ⟨?_, ?_⟩, ?_, st, fr, ?_, hsp, hfm, hF, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down,
        P12.down]
      · rw [PX.down]; exact hT r.np (fun h => absurd h.1 (by omega)) (fun _ => rfl)
      · edge_step
    all_goals have h2 : 2 ≤ r.np := by omega
    · rw [hLB h2]; rfl
    all_goals obtain rfl := Option.some.inj ((hLB h2).symm.trans ‹loadInt _ _ 1 = some _›)
    all_goals simp only [cc_a_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
      rsC_b1 r.pn (r.np - 1) (by omega), decide_eq_true_eq, decide_eq_false_iff_not,
      Nat.reduceMod, Nat.not_lt] at *
    · -- `ja L3228`: the last patch is wide enough
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L3228.mpr ⟨hC, ⟨?_, ?_⟩, ?_, st, fr, ?_, hsp, hfm, hF, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down,
        P12.down]
      · rw [PX.down]
        exact hT r.np (fun h => absurd h.2 (by simp only [u8] at *; omega)) (fun _ => rfl)
      · edge_step
    · exact ld
    · -- drop the last patch: `num_patches--`
      refine ⟨T.L3228.mpr ⟨hC, ⟨?_, ?_⟩, ?_, { st with x := { st.x with npatch := r.np - 1 } },
        fr, ?_, hsp, hfm, hF, S1.down _ (by rw [rsB4_tb, rsC_dec32 (by omega) (by omega)])⟩,
        by var_step⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down,
        P12.down]
      · show TailOk a { st.x with npatch := r.np - 1 }
          ∧ TlimIn a { st.x with npatch := r.np - 1 }
        rw [PX.down]
        exact hT (r.np - 1) (fun _ => rfl)
          (fun h => absurd ⟨by omega, by simp only [u8] at *; omega⟩ h)

end Kraken.Examples.Sbr.Reset
