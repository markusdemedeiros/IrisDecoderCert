import Kraken.X64.Examples.Sbr.Parse.ResetPat3

/-!
# `sbr_reset`: the patch loop, the store of `patch_num_subbands[np]` (`L318c`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

/-- `sub`/`test`/`cmovle` with `0`: `FFMAX(F - U, 0)` on small values. -/
theorem rsC_cmov {F U : Nat} (hF : F < 2 ^ 31) (hU : U < 2 ^ 31) (af : Bool) :
    (if CondCode.le.interp (StatusFlags.from_result
        ((BitVec.setWidth 32 (BitVec.ofNat 64 F) - BitVec.setWidth 32 (BitVec.ofNat 64 U)) &&&
          (BitVec.setWidth 32 (BitVec.ofNat 64 F) - BitVec.setWidth 32 (BitVec.ofNat 64 U)))
        { cf := false, af := af, of := false }) = true
      then BitVec.setWidth 32 (0#64)
      else BitVec.setWidth 32 (BitVec.ofNat 64 F) - BitVec.setWidth 32 (BitVec.ofNat 64 U))
      = BitVec.ofNat 32 (F - U) := by
  rw [a2_cc_le_test]
  have ht : (BitVec.setWidth 32 (BitVec.ofNat 64 F)
      - BitVec.setWidth 32 (BitVec.ofNat 64 U)).toInt = (F : Int) - U := by
    rw [BitVec.toInt_eq_toNat_bmod]
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    simp only [Int.bmod_def]; split <;> omega
  rw [ht]
  by_cases h : (F : Int) - U ≤ 0
  · rw [ite_eq_left_iff.mpr (fun h' => absurd (decide_eq_true h) h')]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [ite_eq_right_iff.mpr (fun h' => absurd (of_decide_eq_true h') h)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

/-- The byte `mov %r14b, …` stores. -/
theorem rsC_byte {D : Nat} (hD : D < 256) :
    Int.toBytes 1 ((BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 D))).toInt)
      = [UInt8.ofNat D] := by
  rw [rsB4_tb1]; unfold u8i
  rw [BitVec.toInt_eq_toNat_bmod, show (256 : Int) = ((2 ^ 8 : Nat) : Int) from rfl, Int.bmod_emod]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  congr 2
  omega

theorem rsC_sw {x : Nat} (h : x < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem rsC_add {x y : Nat} (h : x + y < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 y) + BitVec.ofNat 32 x)
      = BitVec.ofNat 64 (x + y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- `num_patches ≥ 6` fails; store `patch_num_subbands[np]`. -/
theorem blk_L318c (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L318c" ⟨"sbr_reset.L318c", B.L318c, some "sbr_reset.L31b5"⟩ := by
  info_off
  measure_hb "L318c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, j, hH, hnr, hj, hx, hdi, hax, h11, h13, h9, h10, hcx, hsi, h8⟩, hm⟩ := T.L318c.mp hs
    clear hs
    obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    have hpl : p.pn.length = 6 := hH.2.1.2.2.2.2.2.2.2.1
    have hnp6 : p.np ≤ 6 := hH.2.1.2.2.2.2.2.1
    have hu64 : p.usb ≤ 64 := by have := hH.2.1.2.2.2.2.1; omega
    have hstp : st.x.pnum = p.pn := by rw [hx]
    have hfj : fOf st j ≤ 64 := by
      have h1 := rsB_hf hFx j (by have := hj.1; have := hH.2.1.1; omega); omega
    have hod : oddOf (pk0 c) (fOf st j) ≤ 1 := by unfold oddOf; omega
    have ha : ∀ X : BitVec 64, X = arg1 t₀ →
        X + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 p.np)) + 312116#64
          = arg1 t₀ + 0x4c334#64 + BitVec.ofNat 64 p.np := by
      intro X hX; subst hX; rw [rsB_sw (by omega)]; bv_omega
    have LD1 := fun (h5 : p.np < 6) => region_load (o := p.np) (n := 1)
      (focus (Mm_pnum ..) hm) (ha _ rfl) (by rw [hstp]; omega) (by rw [hstp, hpl]; decide)
    have S2 : PLift (p.np < 6 → ∀ w : Int, s₀.dmem.storeInt (arg1 t₀ + BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofNat 64 p.np)) + 312116#64) 1 w =⋆ Mm k e a ra t₀
          { st with x := { st.x with pnum := wr st.x.pnum p.np (Int.toBytes 1 w) } } fr) :=
      ⟨fun h5 w => Mm_upd_pnum .. ▸ region_store (o := p.np) (n := 1) (focus (Mm_pnum ..) hm)
        (ha _ rfl) (by rw [hstp]; omega) (by rw [hstp, hpl]; decide) w⟩
    have hL1 : p.np < 6 → (loadInt s₀.dmem (arg1 t₀ + BitVec.setWidth 64
        (BitVec.setWidth 32 (BitVec.ofNat 64 p.np)) + 312116#64) 1).isSome = true := fun h5 => by
      rw [LD1 h5]; rfl
    have e30 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x30 := by bv_omega
    have L30 : loadInt s₀.dmem (t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64) 8
        = some (Int.ofBytes (slice fr (rb 0x30) 8)) := by
      rw [e30]; exact fr_load hm hF (by omega) (by omega)
    have PH : PLift (PHd a c (fOf st) p ∧ PNr p) := ⟨hH, hnr⟩
    have PJ : PLift (Inner (fOf st) (pk0 c) p.msb p.k j) := ⟨hj⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have PX := PLift.up hx
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
        ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h40, h30, h38, h48, h50, h80⟩
    have PR : PLift (s₀.regs.get64 .rdi = BitVec.ofNat 64 p.k
        ∧ s₀.regs.get64 .rax = BitVec.ofNat 64 p.k
        ∧ s₀.regs.get64 .r9 = BitVec.ofNat 64 p.msb ∧ s₀.regs.get64 .r10 = BitVec.ofNat 64 p.usb
        ∧ s₀.regs.get64 .rcx = BitVec.ofNat 64 p.np ∧ s₀.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c)
        ∧ s₀.regs.get64 .r8 = 0#64) := ⟨hdi, hax, h9, h10, hcx, hsi, h8⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have NB : PLift (fOf st j ≤ 64 ∧ p.np ≤ 6 ∧ pk0 c ≤ 32 ∧ p.usb ≤ 64
        ∧ oddOf (pk0 c) (fOf st j) ≤ 1 ∧ p.k ≤ 48) :=
      ⟨hfj, hnp6, by omega, hu64, hod, by have := hH.2.1.1; omega⟩
    have h30' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1344 8)) = t₀.regs.get64 .rsi := h30
    have P11 : PLift (s₀.regs.get64 .r11 = BitVec.ofNat 64 (fOf st j)
        ∧ s₀.regs.get64 .r13 = BitVec.ofNat 64 (oddOf (pk0 c) (fOf st j))) := ⟨h11, h13⟩
    have PL := PLift.up hpl
    clear hFx h40 h30 h38 h48 h50 h80 hH hnr hj hx hdi hax h9 h10 h8 hfj h11 h13
      e0 h0x hx32 et hxn h64 hnm LD1 hcx hsi hod hpl hnp6 hu64 hstp
    generalize hFv : fOf st j = F at P11 NB
    have PFv : PLift (fOf st j = F) := ⟨hFv⟩
    clear hFv
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L318c]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, cc_nc_sub, not_dec_true, not_dec_false,
        decide_eq_true_eq, decide_eq_false_iff_not, Prbp.down, (PR.down).1, (PR.down).2.1,
        (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1, (PR.down).2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2, (P11.down).1, (P11.down).2, L30,
        BitVec.toNat_setWidth, BitVec.toNat_ofNat] at *
    all_goals obtain ⟨n1, n2, n3, n4, n5, n6⟩ := NB.down
    all_goals try simp only [rsC_cmov (show F < 2 ^ 31 by omega) (show p.usb < 2 ^ 31 by omega)]
    · -- `jae L31f5`: `num_patches > 5`
      rename_i hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L31f5.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down.1, ?_, ?_, hsp, hfm, hF,
        PS.down.1, PS.down.2.1, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down]
      · rw [PX.down]
        exact rsB_reset_fail (r := { p with lk := p.k, lmsb := p.msb, sb := fOf st j }) hC.2.1
          PF.down PH.down.1.1 (PRun.many p j PH.down.2 PJ.down (by omega))
      · rw [PX.down]; rfl
      · edge_step
    all_goals obtain rfl := Option.some.inj ‹some (Int.ofBytes (slice fr 1344 8)) = some _›
    all_goals have h5 : p.np < 6 := by omega
    · rw [h30']; exact hL1 h5
    · obtain ⟨W, hW⟩ : ∃ W : Int,
          W = (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 (F - p.usb)))).toInt :=
        ⟨_, rfl⟩
      refine ⟨T.L31b5.mpr ⟨hC, ⟨?_, ?_⟩,
        { st with x := { st.x with pnum := wr st.x.pnum p.np (Int.toBytes 1 W) } }, fr, c,
        PF.down, hsp, hfm, hF, PS.down.1, PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1,
        PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨p, j, PH.down.1, PH.down.2, PJ.down, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_⟩, ?mem⟩, ?_⟩
      case mem =>
        subst hW
        rw [h30']
        exact S2.down h5 _
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down,
        (PR.down).1, (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1,
        (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2, (P11.down).1, PFv.down, pk0, arg1, h30']
      · rw [PX.down]; dsimp only
        rw [hW, rsC_byte (by omega), rsB4_wr PL.down (by omega), ← PFv.down]
        rfl
      · exact rsC_sw (by omega)
      · exact rsC_add (by omega)
      · exact rsB_sw (by omega)
      · exact rsB_sw (by omega)
      · rw [V.L31b5, V.L318c]
        simp only [VD.L31b5, VD.L318c, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        rw [slot32_of_load (v := Int.ofBytes (slice fr (rb 128) 4)) ?q1,
          slot32_of_load (v := Int.ofBytes (slice fr (rb 128) 4)) ?q2]
        case q1 | q2 =>
          first
          | (rw [Prbp.down]; exact fr_load hm hF (by omega) (by omega))
          | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rw [Prbp.down]
             exact fr_load (S2.down h5 _) hF (by omega) (by omega))
        exact Nat.le_refl _

end Kraken.Examples.Sbr.Reset
