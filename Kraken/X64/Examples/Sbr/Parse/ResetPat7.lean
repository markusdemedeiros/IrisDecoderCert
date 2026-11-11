import Kraken.X64.Examples.Sbr.Parse.ResetPat6

/-!
# `sbr_reset`: the end of a pass of the patch loop (`L3108`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

theorem rsC_sw32 (x : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 x) = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem rsC_toInt32 {x : Nat} (h : x < 2 ^ 16) : (BitVec.ofNat 32 x).toInt = (x : Int) := by
  rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat]; simp only [Int.bmod_def]; split <;> omega

/-- `sub`, `cmp $3`, `cmovl` on two small values: `f[k] - f[j] < 3` (signed). -/
theorem rsC_cc_l {x y : Nat} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) (c f : Bool) :
    CondCode.l.interp (StatusFlags.from_result
      (BitVec.ofNat 32 x - BitVec.ofNat 32 y - 3#32)
      { cf := c, af := f,
        of := (BitVec.ofNat 32 x - BitVec.ofNat 32 y - 3#32).signed
          != (BitVec.ofNat 32 x - BitVec.ofNat 32 y).signed - (3#32).signed })
      = decide ((x : Int) - y < 3) := by
  simp only [CondCode.interp_l, StatusFlags.sf_from_result, StatusFlags.of_from_result,
    BitVec.signed]
  have h3 : (3#32) = BitVec.ofNat 32 3 := rfl
  rw [h3]
  have hs : (BitVec.ofNat 32 x - BitVec.ofNat 32 y).toInt = (x : Int) - y := by
    rw [BitVec.toInt_eq_toNat_bmod, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    simp only [Int.bmod_def]; split <;> omega
  have hs3 : (BitVec.ofNat 32 x - BitVec.ofNat 32 y - BitVec.ofNat 32 3).toInt
      = (x : Int) - y - 3 := by
    rw [BitVec.toInt_eq_toNat_bmod]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Int.bmod_def]; split <;> omega
  have hm : (BitVec.ofNat 32 x - BitVec.ofNat 32 y - BitVec.ofNat 32 3).msb
      = decide ((x : Int) - y < 3) := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    by_cases h : (x : Int) - y < 3 <;> simp only [h, decide_true, decide_false,
      decide_eq_true_eq, decide_eq_false_iff_not] <;> omega
  rw [hs, hs3, hm, rsC_toInt32 (by omega)]
  have e3 : ((3 : Nat) : Int) = 3 := rfl
  by_cases h : (x : Int) - y < 3 <;> simp [h, e3]

/-- `cmp %r11w, -0x50(%rbp)`; `je`: equality of two small values. -/
theorem rsC_cc_z16 {x y : Nat} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16)
    (r : StatusFlags.from_result.Remaining) :
    CondCode.z.interp (StatusFlags.from_result
      (BitVec.ofInt 16 (x : Int) - BitVec.setWidth 16 (BitVec.ofNat 64 y)) r) = decide (x = y) := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result]
  by_cases h : x = y
  · subst h
    have : BitVec.ofInt 16 (x : Int) = BitVec.setWidth 16 (BitVec.ofNat 64 x) := by
      rw [BitVec.ofInt_natCast]; apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    simp [this]
  · have hne : ¬ BitVec.ofNat 16 x - BitVec.ofNat 16 y = 0#16 := by
      intro h'
      have := congrArg BitVec.toNat h'
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    simp [hne, h]

/-- The variant step `L3108 → L312e` (the digits of `VD.L312e` / `VD.L3108`). -/
theorem rsC_var {np k k1 m m1 u u1 J x nm : Nat} (hm : m ≤ u) (hu : u ≤ 64) (hx : x ≤ u)
    (hJ : J ≤ 64) (hk : k ≤ nm) (hnm : nm ≤ 48)
    (h4 : (0 < J - u ∧ m1 = J ∧ u1 = J) ∨ (¬ 0 < J - u ∧ m1 = x ∧ u1 = u))
    (h5 : k1 = nm ∨ k1 = k) :
    lex [11, 6 - np % 2 ^ 64, 8 * (48 - k1 % 2 ^ 64)
        + (((if ¬ k % 2 ^ 64 % 2 ^ 32 = k1 % 2 ^ 64 % 2 ^ 32 then 2 else 0)
        + if ¬ m1 % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 = m % 2 ^ 32 % 2 ^ 64 % 2 ^ 32 then 2 else 0)
        + if m1 % 2 ^ 32 % 2 ^ 64 = u1 % 2 ^ 64 then 1 else 0), 49]
      ≤ lex [11, 6 - np % 2 ^ 64, 8 * (48 - k % 2 ^ 64)
        + if m1 % 2 ^ 64 = u1 % 2 ^ 64 ∧ u1 % 2 ^ 64 = J % 2 ^ 64 ∧ ¬ m % 2 ^ 64 = u1 % 2 ^ 64
          then 3
          else ((2 + if m % 2 ^ 64 = u1 % 2 ^ 64 then 1 else 0)
            + if ¬ m % 2 ^ 64 = u1 % 2 ^ 64 ∧ ¬ m % 2 ^ 64 = x % 2 ^ 32 then 2 else 0) - 1,
        49] := by
  have b1 : m1 ≤ 64 := by omega
  have b2 : u1 ≤ 64 := by omega
  have b3 : k1 ≤ 48 := by omega
  simp only [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show k1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show k1 < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show m < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show m1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show m1 < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show u1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show J < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega)]
  refine rsB_lex_le rfl (by (repeat' split) <;> omega) (by omega) ?_
  rcases h4 with ⟨h, rfl, rfl⟩ | ⟨h, rfl, rfl⟩ <;> rcases h5 with rfl | rfl <;>
    (repeat' split) <;> omega

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- The rest of the pass. -/
theorem blk_L3108 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3108" ⟨"sbr_reset.L3108", B.L3108, some "sbr_reset.L312e"⟩ := by
  info_off
  measure_hb "L3108"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, j, hH, hnr, hj, hnp, hx, hdi, hax, h11, h9, h14, h10, hcx, hsi, h8, h12⟩, hm⟩ :=
      T.L3108.mp hs
    clear hs
    obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    have hkn : p.k ≤ c.nm := hH.2.1.1
    have hfk : fOf st p.k ≤ 64 := by have := rsB_hf hFx p.k hkn; omega
    have hfj : fOf st j ≤ 64 := by have := rsB_hf hFx j (by have := hj.1; omega); omega
    have e38 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x38 := by bv_omega
    have e48 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x48 := by bv_omega
    have e50 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x50 := by bv_omega
    have L38 : loadInt s₀.dmem (t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64) 8
        = some (Int.ofBytes (slice fr (rb 0x38) 8)) := by
      rw [e38]; exact fr_load hm hF (by omega) (by omega)
    have L48 : loadInt s₀.dmem (t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64) 8
        = some (Int.ofBytes (slice fr (rb 0x48) 8)) := by
      rw [e48]; exact fr_load hm hF (by omega) (by omega)
    have L50 : loadInt s₀.dmem (t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64) 2
        = some ((ptop a c (fOf st) : Nat) : Int) := by
      rw [e50, fr_load hm hF (by omega) (by omega)]
      rw [rsB_slice2_of4 (by simp only [rb]; omega) h50 (by omega)]
    have LK : loadInt s₀.dmem (t₀.regs.get64 .rsi + 311792#64 + BitVec.ofNat 64 p.k * 2#64) 2
        = some ((fOf st p.k : Nat) : Int) :=
      rsB_fm_load hm hfm (by omega) (by simp only [arg1]; bv_omega)
    have h38' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1336 8)) = BitVec.ofNat 64 c.nm := h38
    have h48' : BitVec.ofInt 64 (Int.ofBytes (slice fr 1320 8))
        = t₀.regs.get64 .rsi + 311792#64 := h48
    have hk032 : pk0 c ≤ 32 := by omega
    have hkkx : pk0 c ≤ pkx a (fOf st) := by omega
    have PEnd : PLift (fOf st j = ptop a c (fOf st) →
        (∃ ki, KInit (fOf st) c.nm (ptop a c (fOf st)) (goalSb a.x.sampleRate.toInt) ki
          ∧ PR a c (fOf st) (pinit a c (fOf st) ki)
            (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j) true)
        ∧ PInv (pk0 c) (pkx a (fOf st)) c.nm (ptop a c (fOf st))
            (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j)) :=
      ⟨fun ht => let ⟨ki, hk, hr⟩ := hH.1
        ⟨⟨ki, hk, hr _ _ (PRun.stop p j hnr hj hnp ht)⟩,
          pbody_inv hk032 hkkx (rsB_hf hFx) hH.2.1 hj hnp⟩⟩
    have PStep : PLift (fOf st j ≠ ptop a c (fOf st) →
        PHd a c (fOf st) (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j)) :=
      ⟨fun ht => rsB_hd_step hFx hH hnr hj hnp ht⟩
    have hKk : BitVec.setWidth 64 (if (fOf st p.k : Int) - fOf st j < 3 then BitVec.ofNat 32 c.nm
        else BitVec.ofNat 32 p.k)
        = BitVec.ofNat 64 (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).k := by
      simp only [pbody]
      by_cases h : (fOf st p.k : Int) - fOf st j < 3 <;> simp only [h, ↓reduceIte] <;>
        exact rsB3_w64 (by omega)
    have hmsb : (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).msb ≤ 64 := by
      simp only [pbody]; split <;> omega
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
        ∧ s₀.regs.get64 .r9 = BitVec.ofNat 64 p.msb
        ∧ s₀.regs.get64 .r14
          = BitVec.ofNat 64 (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).msb
        ∧ s₀.regs.get64 .r10
          = BitVec.ofNat 64 (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).usb
        ∧ s₀.regs.get64 .rcx = BitVec.ofNat 64 (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).np
        ∧ s₀.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c) ∧ s₀.regs.get64 .r8 = 0#64
        ∧ s₀.regs.get64 .r12 = arg1 t₀) := ⟨hdi, hax, h9, h14, h10, hcx, hsi, h8, h12⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have P11 : PLift (s₀.regs.get64 .r11 = BitVec.ofNat 64 (fOf st j)) := ⟨h11⟩
    have NB : PLift (fOf st j ≤ 64 ∧ fOf st p.k ≤ 64 ∧ p.k ≤ c.nm ∧ c.nm ≤ 48
        ∧ ptop a c (fOf st) ≤ 64) :=
      ⟨hfj, hfk, hkn, hnm, by omega⟩
    have PMs := PLift.up hmsb
    have PV : PLift (p.msb ≤ p.usb ∧ p.usb ≤ ptop a c (fOf st) ∧ pkx a (fOf st) ≤ p.usb
        ∧ ((0 < fOf st j - p.usb
            ∧ (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).msb = fOf st j
            ∧ (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).usb = fOf st j)
          ∨ (¬ 0 < fOf st j - p.usb
            ∧ (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).msb = pkx a (fOf st)
            ∧ (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).usb = p.usb))
        ∧ ((pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).k = c.nm
          ∨ (pbody (fOf st) (pk0 c) (pkx a (fOf st)) c.nm p j).k = p.k)) := by
      refine ⟨hH.2.1.2.2.1, hH.2.1.2.2.2.2.1, hH.2.1.2.2.2.1, ?_, ?_⟩
      · simp only [pbody]
        by_cases h : 0 < fOf st j - p.usb <;> simp only [h, ↓reduceIte] <;> simp
      · simp only [pbody]; split <;> simp
    clear hFx h40 h30 h38 h48 h50 h80 hH hnr hj hx hdi hax h9 h14 h10 hcx hsi h8 h12 h11
      e0 h0x hx32 et hxn h64 hnm hkn hfk hfj e38 e48 e50 hrbp hk032 hkkx hmsb
    generalize hFJ : fOf st j = FJ at P11 NB hKk PV
    generalize hFK : fOf st p.k = FK at LK NB hKk
    generalize hFT : ptop a c (fOf st) = FT at L50 NB PV
    have PFJ : PLift (fOf st j = FJ) := ⟨hFJ⟩
    have PFK : PLift (fOf st p.k = FK) := ⟨hFK⟩
    have PFT : PLift (ptop a c (fOf st) = FT) := ⟨hFT⟩
    clear hFJ hFK hFT
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L3108]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, Int64.toBitVec_neg_ofNat_norm,
        Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod,
        Nat.reducePow, Nat.reduceSub, Option.isSome_some, sw32_64, Prbp.down, (PR.down).1,
        L38, L48, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals simp only [h38', h48', LK, L50, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals obtain ⟨n1, n2, n3, n4, n5⟩ := NB.down
    all_goals try simp only [(P11.down), rsC_sw32, rsB3_w16 (show FK < 2 ^ 16 by omega),
      rsC_cc_l (show FK < 2 ^ 16 by omega) (show FJ < 2 ^ 16 by omega),
      rsC_cc_z16 (show FT < 2 ^ 16 by omega) (show FJ < 2 ^ 16 by omega),
      decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rfl
    · rfl
    · -- `je L320e`: the last pass (`sb == kx[1] + m[1]`)
      rename_i ht
      obtain ⟨⟨ki, hk, hr⟩, hI⟩ := PEnd.down (by rw [PFJ.down, PFT.down]; exact ht.symm)
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L320e.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, PS.down.1,
        PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1, PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨ki, _, hk, hr, hI, PX.down, ?_, ?_⟩, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down,
        (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.2]
      edge_step
    · -- on to the next pass
      rename_i ht
      have hH' := PStep.down (by rw [PFJ.down, PFT.down]; exact fun h => ht h.symm)
      refine ⟨T.L312e.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, PS.down.1,
        PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1, PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨_, hH', PX.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, Prbp.down,
        (PR.down).1, (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1,
        (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2.2.2, hKk, sw32_64, rsC_sw32]
      all_goals try exact rsB3_w64 (by have := PMs.down; omega)
      all_goals try (simp only [pbody]; rw [BitVec.ofInt_natCast]; done)
      simp only [V.L312e, V.L3108, VD.L312e, VD.L3108, Reg64s.get64_set64, reduceCtorEq,
        ↓reduceIte, (PR.down).1, (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1,
        (PR.down).2.2.2.2.1, (PR.down).2.2.2.2.2.1, P11.down]
      rw [slot32_of_load (v := Int.ofBytes (slice fr (rb 128) 4)) ?q]
      case q => rw [Prbp.down]; exact fr_load hm hF (by omega) (by omega)
      have h80' := PS.down.2.2.2.2.2
      simp only [rb, Nat.reduceSub] at h80' ⊢
      rw [h80']
      simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat, ne_eq]
      obtain ⟨v1, v2, v3, v4, v5⟩ := PV.down
      exact rsC_var v1 (by omega) v3 n1 n3 n4 v4 v5

end Kraken.Examples.Sbr.Reset
