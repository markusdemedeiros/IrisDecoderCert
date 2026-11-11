import Kraken.X64.Examples.Sbr.Parse.ResetPatLib

/-!
# `sbr_reset`: the patch loop `sbr_hf_calc_npatches`, the loop head and the inner loop (gB)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- The loop head: `k == last_k && msb == last_msb` fails (`L31d5`) or goes on. -/
theorem blk_L312e (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L312e" ⟨"sbr_reset.L312e", B.L312e, some "sbr_reset.L3141"⟩ := by
  info_off
  measure_hb "L312e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, hH, hx, h9, h10, hcx, hsi, h8, hdi, hax, h15, h12⟩, hm⟩ := T.L312e.mp hs
    clear hs
    obtain ⟨-, -, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    obtain ⟨hR, ⟨i1, i2, i3, i4, i5, i6⟩, hIm, hK, hl1, hl2, hm1, hm2⟩ := hH
    have hk48 : p.k < 2 ^ 31 := by omega
    have hms : p.msb < 2 ^ 31 := by omega
    have hkx : (pkx a (fOf st)) < 2 ^ 31 := by omega
    have hsl := rsB_slot32 hm hF hrbp (d := 0x80) (by omega) (by omega)
    rw [h80] at hsl
    have PH : PLift (PHd a c (fOf st) p) := ⟨⟨hR, ⟨i1, i2, i3, i4, i5, i6⟩, hIm, hK, hl1, hl2, hm1, hm2⟩⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have PX : PLift (st.x = pxs a c (fOf st) p) := ⟨hx⟩
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
        ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h40, h30, h38, h48, h50, h80⟩
    have PR' : PLift (PReach a c (fOf st) p) := ⟨hR⟩
    have hb : p.usb ≤ 64 ∧ p.np ≤ 6 ∧ pkx a (fOf st) ≤ 32 :=
      ⟨by have h5 := i5; simp only [ptop, pkx] at h5 hxn; omega, i6.1, by omega⟩
    have PK := PLift.up (rsB_slot32' hm hF hrbp (d := 0x80) (by omega) (by omega))
    have P9 : PLift (s₀.regs.get64 .r9 = BitVec.ofNat 64 p.msb) := ⟨h9⟩
    have PD : PLift (s₀.regs.get64 .rdi = BitVec.ofNat 64 p.k) := ⟨hdi⟩
    have PA : PLift (BitVec.setWidth 32 (s₀.regs.get64 .rax) = BitVec.ofInt 32 p.lk) := ⟨hax⟩
    have P15 : PLift (BitVec.setWidth 32 (s₀.regs.get64 .r15) = BitVec.ofInt 32 p.lmsb) := ⟨h15⟩
    have hIm' : (p.msb : Int) ≠ p.lmsb ∨ p.msb = pkx a (fOf st) := by
      by_cases h : (p.msb : Int) = p.lmsb
      · exact Or.inr (hIm h)
      · exact Or.inl h
    have hK' : p.msb = p.usb ∨ p.msb = pkx a (fOf st) ∨ p.lk = -1 := by
      by_cases h1 : p.msb = p.usb
      · exact Or.inl h1
      by_cases h2 : p.msb = pkx a (fOf st)
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (hK h1 h2))
    obtain ⟨hu64, hnp6, hkx32⟩ := hb
    have NB : PLift (p.k ≤ 48 ∧ p.msb ≤ 64 ∧ p.usb ≤ 64 ∧ p.np ≤ 6 ∧ pkx a (fOf st) ≤ 32
        ∧ p.msb ≤ p.usb ∧ -1 ≤ p.lk ∧ p.lk ≤ 48 ∧ -1 ≤ p.lmsb ∧ p.lmsb ≤ 64
        ∧ ((p.msb : Int) ≠ p.lmsb ∨ p.msb = pkx a (fOf st))
        ∧ (p.msb = p.usb ∨ p.msb = pkx a (fOf st) ∨ p.lk = -1)) :=
      ⟨by omega, by omega, hu64, hnp6, hkx32, i3, hl1, hl2, hm1, hm2, hIm', hK'⟩
    clear hFx hx h40 h30 h38 h48 h50 h80 hR hIm hK hIm' hK' i1 i2 i3 i4 i5 i6 et hxn h64 hnm hx32
      hk48 hms hkx hu64 hnp6 hkx32 hsl
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L312e]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, cc_nz_sub, cc_z_sub, not_dec_true, not_dec_false,
        decide_eq_true_eq, decide_eq_false_iff_not, hdi, hax, h9, h15] at *
    all_goals obtain ⟨hk48, hms64, hu64, hnp6, hkx32, hmu, hl1, hl2, hm1, hm2, hIm', hK'⟩ := NB.down
    all_goals try simp only [rsB_bv32_eq hl1 (by omega) (show p.k < 2 ^ 31 by omega),
      rsB_bv32_eq hm1 (by omega) (show p.msb < 2 ^ 31 by omega)] at *
    all_goals clear hk48 hms64 hu64 hnp6 hkx32 hmu hl1 hl2 hm1 hm2 hIm' hK'
    all_goals obtain ⟨hk48, hms64, hu64, hnp6, hkx32, hmu, hl1, hl2, hm1, hm2, hIm', hK'⟩ := NB.down
    all_goals obtain ⟨h40, h30, h38, h48, h50, h80⟩ := PS.down
    · -- `k != last_k`: `jne L3141`
      rename_i hne
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L3141.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, h40, h30, h38,
        h48, h50, h80, ⟨p, PH.down, fun h => hne h.1, PX.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h10, hcx,
        hsi, h8, h12, P9.down, PD.down]
      · exact rsB_sw (by omega)
      · refine (Nat.lt_or_eq_of_le ?_).imp id (fun h => ⟨h, by first | decide | (simp only [lex_var]; decide)⟩)
        rw [V.L3141, V.L312e]
        simp only [VD.L3141, VD.L312e]
        rw [PK.down _ ?_ ?_, show BitVec.ofInt 32 (Int.ofBytes (slice fr (1392 - 128) 4))
          = BitVec.ofNat 32 (pkx a (fOf st)) from h80]
        · simp only [VD.L3141, VD.L312e, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, h10,
            P9.down, PD.down, PA.down, P15.down, rsB_toNat (show p.np < 2 ^ 32 by omega),
            rsB_toNat (show p.k < 2 ^ 32 by omega), rsB_toNat (show p.msb < 2 ^ 32 by omega),
            rsB_toNat (show p.usb < 2 ^ 32 by omega), rsB_toNat32 (show pkx a (fOf st) < 2 ^ 32 by simp only [pkx, fOf, u16, u8, xoOf]; omega),
            ne_eq, rsB_bv32_eq' hl1 (by omega) (show p.k < 2 ^ 31 by omega),
            rsB_bv32_eq hm1 (by omega) (show p.msb < 2 ^ 31 by omega)]
          simp only [pkx, fOf, u16, u8, xoOf]
          refine rsB_lex_le rfl (by (repeat' split) <;> omega) (by omega) ?_
          (repeat' split) <;> first | omega | (exfalso; rcases hIm' with h | h <;> simp_all)
        · rfl
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · -- the repeat: `je L31d5`
      rename_i hkeq hmeq
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L31d5.mpr ⟨hC, ⟨?_, ?_⟩, ?_, st, fr, c, PF.down.1, ?_, ?_, hsp, hfm, hF,
        h40, h30, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h12]
      · rw [PX.down]; exact rsB_reset_fail hC.2.1 PF.down PR'.down (PRun.rep p ⟨hkeq, hmeq⟩)
      · rw [PX.down]; rfl
      · edge_step
    · -- `msb != last_msb`: on to `L3141`
      rename_i hkeq hmne
      refine ⟨T.L3141.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, h40, h30, h38,
        h48, h50, h80, ⟨p, PH.down, fun h => hmne h.2, PX.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, hrbp, h10, hcx,
        hsi, h8, h12, P9.down, PD.down]
      · exact rsB_sw (by omega)
      · rw [V.L3141, V.L312e]
        simp only [VD.L3141, VD.L312e]
        rw [PK.down _ ?_ ?_, show BitVec.ofInt 32 (Int.ofBytes (slice fr (1392 - 128) 4))
          = BitVec.ofNat 32 (pkx a (fOf st)) from h80]
        · simp only [VD.L3141, VD.L312e, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, h10,
            P9.down, PD.down, PA.down, P15.down, rsB_toNat (show p.np < 2 ^ 32 by omega),
            rsB_toNat (show p.k < 2 ^ 32 by omega), rsB_toNat (show p.msb < 2 ^ 32 by omega),
            rsB_toNat (show p.usb < 2 ^ 32 by omega), rsB_toNat32 (show pkx a (fOf st) < 2 ^ 32 by simp only [pkx, fOf, u16, u8, xoOf]; omega),
            ne_eq, rsB_bv32_eq' hl1 (by omega) (show p.k < 2 ^ 31 by omega),
            rsB_bv32_eq hm1 (by omega) (show p.msb < 2 ^ 31 by omega)]
          simp only [pkx, fOf, u16, u8, xoOf]
          refine rsB_lex_le rfl (by (repeat' split) <;> omega) (by omega) ?_
          (repeat' split) <;> first | omega | (exfalso; rcases hIm' with h | h <;> simp_all)
        · rfl
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]

set_option maxRecDepth 100000 in
/-- `k ≤ 48` (else the trap), `r14d = msb + k[0]`, `r15 = &f_master[k]`, `r12 = 0`. -/
theorem blk_L3141 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3141" ⟨"sbr_reset.L3141", B.L3141, some "sbr_reset.L3160"⟩ := by
  info_off
  measure_hb "L3141"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, hH, hnr, hx, hax, hdi, h9, h10, hcx, hsi, h8, h12⟩, hm⟩ := T.L3141.mp hs
    clear hs
    obtain ⟨-, -, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    obtain ⟨hR, ⟨i1, i2, i3, i4, i5, i6⟩, hIm, hK, hl1, hl2, hm1, hm2⟩ := hH
    have hk48 : p.k ≤ 48 := by omega
    have hbd : p.msb ≤ 64 ∧ p.usb ≤ 64 ∧ p.np ≤ 6 :=
      ⟨by have h5 := i5; simp only [ptop, pkx] at h5 hxn; omega,
       by have h5 := i5; simp only [ptop, pkx] at h5 hxn; omega, i6.1⟩
    have ha8 : t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 0x578#64 + BitVec.ofNat 64 (rb 0x48) := by
      have : (-72 : Int64).toBitVec = 0xffffffffffffffb8#64 := by decide
      simp only [rb, this]; bv_omega
    have ld48 := fr_load8 hm hF (d := 0x48) (by omega) (by omega) ha8
    have P48 : PLift (frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64) := ⟨h48⟩
    have PH : PLift (PHd a c (fOf st) p ∧ PNr p) :=
      ⟨⟨hR, ⟨i1, i2, i3, i4, i5, i6⟩, hIm, hK, hl1, hl2, hm1, hm2⟩, hnr⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have PX : PLift (st.x = pxs a c (fOf st) p) := ⟨hx⟩
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
        ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h40, h30, h38, h48, h50, h80⟩
    have PK := PLift.up (rsB_slot32' hm hF hrbp (d := 0x80) (by omega) (by omega))
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have hrd : BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 p.k)) = BitVec.ofNat 64 p.k := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hx0 : ∀ x : BitVec 64, BitVec.setWidth 64 (BitVec.setWidth 32 x ^^^ BitVec.setWidth 32 x)
        = 0#64 := by intro x; simp
    have PRD := PLift.up hrd
    have PD : PLift (s₀.regs.get64 .rdi = BitVec.ofNat 64 p.k) := ⟨hdi⟩
    have PX0 := PLift.up hx0
    clear hrd hx0
    clear hFx hx h40 h30 h38 h48 h50 h80 hR i1 i2 i3 i4 i5 i6 hIm hK hl1 hl2 hm1 hm2 hnr
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L3141]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, cc_a_sub, decide_eq_true_eq, decide_eq_false_iff_not,
        hdi, hrbp, ld48] at *
    · -- `ja` to the trap: `k > 48` is impossible
      exfalso; rename_i hja
      simp only [hax, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hja; omega
    · -- the load of `[rbp-0x48]` is defined
      rw [ld48]; rfl
    · rename_i hld
      rw [ld48, Option.some.injEq] at hld; subst hld
      obtain ⟨h40, h30, h38, h48, h50, h80⟩ := PS.down
      refine ⟨T.L3160.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, h40, h30, h38,
        h48, h50, h80, ⟨p, p.k, PH.down.1, PH.down.2, PX.down, Nat.le_refl _,
          fun i' h1 h2 => absurd h2 (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, h9, h10, hcx,
        hsi, h8, h12, AddrIndex.offset64_scale1, AddrIndex.offset64_scale2, PRD.down, PX0.down, hax,
        Prbp.down, pk0, arg1]
      · apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
      · have h48' := h48
        simp only [show (1392 : Nat) - 72 = 1320 from rfl] at h48'
        rw [h48']
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega
      · exact (BitVec.sub_self _).symm
      · rw [V.L3160, V.L3141]
        simp only [VD.L3160, VD.L3141]
        rw [PK.down _ ?_ ?_, PK.down _ ?_ ?_, show BitVec.ofInt 32 (Int.ofBytes (slice fr (1392 - 128) 4))
          = BitVec.ofNat 32 (pkx a (fOf st)) from h80]
        ·
          simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx, h10, h9, PD.down, PRD.down, PX0.down,
            BitVec.add_zero, rsB_toNat (show p.np < 2 ^ 32 by omega),
            rsB_toNat (show p.k < 2 ^ 32 by omega), rsB_toNat (show p.msb < 2 ^ 32 by omega),
            rsB_toNat (show p.usb < 2 ^ 32 by omega),
            rsB_toNat32 (show pkx a (fOf st) < 2 ^ 32 by simp only [pkx, fOf, u16, u8, xoOf]; omega),
            ne_eq]
          simp only [pkx, fOf, u16, u8, xoOf]
          refine rsB_lex_le rfl (by (repeat' split) <;> omega) (by omega) (Or.inr ⟨rfl, ?_⟩)
          simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
        all_goals first | rfl | simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]

end Kraken.Examples.Sbr.Reset
