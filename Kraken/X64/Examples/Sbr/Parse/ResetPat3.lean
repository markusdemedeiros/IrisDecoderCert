import Kraken.X64.Examples.Sbr.Parse.ResetPatLib

/-!
# `sbr_reset`: the inner loop `L3160` and `num_patches++` (`L30f8`) of `sbr_hf_calc_npatches` (gB)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

theorem rsB3_w16 {F : Nat} (h : F < 2 ^ 16) :
    BitVec.setWidth 32 (BitVec.ofInt 16 (F : Int)) = BitVec.ofNat 32 F := by
  rw [BitVec.ofInt_natCast]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem rsB3_w64 {F : Nat} (h : F < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.ofNat 32 F) = BitVec.ofNat 64 F := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem rsB3_odd {k0 F : Nat} (hk : k0 < 2 ^ 31) (_hF : F < 2 ^ 31) :
    BitVec.setWidth 32 (BitVec.ofNat 64 k0 + BitVec.ofNat 64 F) &&& BitVec.setWidth 32 1#64
      = BitVec.ofNat 32 ((F + k0) % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.reduceMod, Nat.reducePow, Nat.and_one_is_mod]
  omega

theorem rsB3_na {x y : Nat} (hx : x ≤ 1) (hy : y < 2 ^ 31) (hxy : x + 1 ≤ y) :
    (BitVec.ofNat 32 y + ~~~(BitVec.ofNat 32 x)).toNat = y - x - 1 := by
  rw [BitVec.add_comm]; exact rsB_not_add hx hy hxy

theorem rsB3_idx {i k : Nat} (_hi : i ≤ 48) (_hk : k ≤ 48) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 k + (BitVec.ofNat 64 i - BitVec.ofNat 64 k - 1#64))).toNat
      = (i + 4294967295) % 4294967296 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem rsB3_idx0 {i k : Nat} (hi : i ≤ 48) (_hk : k ≤ 48) :
    (BitVec.setWidth 32 (BitVec.ofNat 64 k + (BitVec.ofNat 64 i - BitVec.ofNat 64 k))).toNat = i := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem rsB3_dec {i k : Nat} (h1 : 1 ≤ i) (hi : i ≤ 48) (_hk : k ≤ 48) :
    BitVec.ofNat 64 i - BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (i - 1) - BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

theorem rsB4_tb (v : BitVec 32) : Int.toBytes 4 v.toInt = Int.toBytes 4 (v.toNat : Int) := by
  rw [← Int.toBytes_emod 4 v.toInt, ← Int.toBytes_emod 4 (v.toNat : Int)]
  congr 1
  simp only [Int.take]
  rw [BitVec.toInt_eq_toNat_bmod]
  have := Int.bmod_emod (x := (v.toNat : Int)) (m := 2 ^ 32)
  simpa using this

theorem rsB4_wr {l : List UInt8} (h : l.length = 6) {o : Nat} (ho : o < 6) (b : UInt8) :
    wr l o [b] = mk 6 (fun i => if i = o then b else old l i) := by
  apply List.ext_getElem
  · rw [wr_length (by simp; omega)]; simp [h]
  · intro i h1 h2
    simp only [mk, List.getElem_map, List.getElem_range, old]
    have hl : (l.take o).length = o := by simp; omega
    simp only [wr, List.append_assoc, List.length_singleton] at h1 ⊢
    rcases Nat.lt_trichotomy i o with hi | hi | hi
    · rw [List.getElem_append_left (by omega)]
      simp [List.getElem_take, show i ≠ o by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < l.length by omega)]
    · subst hi
      rw [List.getElem_append_right (by omega)]
      simp [hl]
    · rw [List.getElem_append_right (by omega)]
      simp only [hl, show i ≠ o by omega, ↓reduceIte]
      obtain ⟨d, rfl⟩ : ∃ d, i = o + 1 + d := ⟨i - o - 1, by omega⟩
      have hlen : o + 1 + d < l.length := by rw [h]; simp only [mk_length] at h2; omega
      simp only [show o + 1 + d - o = d + 1 by omega, List.singleton_append, List.getElem_cons_succ,
        List.getElem_drop, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
        Option.getD_some]

theorem rsB4_tb1 (v : Int) : Int.toBytes 1 v = [u8i v] := by
  simp only [Int.toBytes, u8i, List.cons.injEq, and_true]
  simp only [Int.take]
  first | rfl | simp [Nat.toUInt8]

theorem rsB4_byte {k0 D o : Nat} (hk : k0 ≤ 32) (hD : D ≤ 64) (ho : o ≤ 1) :
    Int.toBytes 1 ((BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 k0)
      - BitVec.setWidth 32 (BitVec.ofNat 64 (D + o))))).toInt) = [u8i ((k0 : Int) - o - D)] := by
  rw [rsB4_tb1]; unfold u8i
  rw [BitVec.toInt_eq_toNat_bmod, show (256 : Int) = ((2 ^ 8 : Nat) : Int) from rfl, Int.bmod_emod]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  congr 2
  omega

theorem rsB4_ne0 {D : Nat} (hD : D ≤ 64) :
    (BitVec.setWidth 8 (BitVec.ofNat 64 D) &&& BitVec.setWidth 8 (BitVec.ofNat 64 D) = 0#8) ↔ D = 0 := by
  rw [BitVec.and_self]
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this; omega
  · intro h; subst h; rfl

theorem rsB4_nz {w : Nat} (x : BitVec w) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result x f) = !decide (x = 0) := by
  rw [CondCode.interp_nz]
  simp [StatusFlags.zf_from_result]
  by_cases h : x = 0#w <;> simp [h]

variable [CodeEnv]

set_option maxRecDepth 100000 in
/-- The inner loop. -/
theorem blk_L3160 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L3160" ⟨"sbr_reset.L3160", B.L3160, some "sbr_reset.L3187"⟩ := by
  info_off
  measure_hb "L3160"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, i, hH, hnr, hx, hik, hall, hdi, hax, h14, h15, h12, h9, h10, hcx, hsi, h8⟩, hm⟩ := T.L3160.mp hs
    clear hs
    obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    obtain ⟨hR, ⟨i1, i2, i3, i4, i5, i6⟩, hIm, hK, hl1, hl2, hm1, hm2⟩ := hH
    have hk1 : 1 ≤ c.k0.toNat := by
      have := rsB_k0_pos hFx.1 hC.2.1; omega
    have hFi : fOf st i ≤ 64 := by have h1 := rsB_hf hFx i (by omega); omega
    have hz : i = 0 → fOf st i = c.k0.toNat := by intro h; subst h; simp only [pk0] at e0; omega
    have NB : PLift (1 ≤ c.k0.toNat ∧ c.k0.toNat ≤ p.msb ∧ p.msb ≤ 64 ∧ fOf st i ≤ 64 ∧ i ≤ p.k
        ∧ p.k ≤ 48 ∧ (i = 0 → fOf st i = c.k0.toNat) ∧ c.k0.toNat ≤ 32 ∧ p.usb ≤ 64 ∧ p.np ≤ 6
        ∧ pkx a (fOf st) ≤ 32) :=
      ⟨hk1, by simp only [pk0] at i2; omega, by omega, hFi, hik, by omega, hz,
        by simp only [pk0] at e0; omega, by omega, i6.1, hx32⟩
    have hld := rsB_fm_load hm hfm (i := i) (by omega)
      (addr := s₀.regs.get64 .r15 + (BitVec.ofNat 64 i - BitVec.ofNat 64 p.k) * 2#64)
      (by rw [h15]; bv_omega)
    have PLD := PLift.up hld
    have PH : PLift (PHd a c (fOf st) p ∧ PNr p) :=
      ⟨⟨hR, ⟨i1, i2, i3, i4, i5, i6⟩, hIm, hK, hl1, hl2, hm1, hm2⟩, hnr⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have PX : PLift (st.x = pxs a c (fOf st) p) := ⟨hx⟩
    have PALL := PLift.up hall
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
        ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h40, h30, h38, h48, h50, h80⟩
    have PR : PLift (s₀.regs.get64 .rdi = BitVec.ofNat 64 p.k ∧ s₀.regs.get64 .rax = BitVec.ofNat 64 p.k
        ∧ (s₀.regs.get64 .r14).setWidth 32 = BitVec.ofNat 32 (p.msb + pk0 c)
        ∧ s₀.regs.get64 .r15 = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * p.k)
        ∧ s₀.regs.get64 .r12 = BitVec.ofNat 64 i - BitVec.ofNat 64 p.k
        ∧ s₀.regs.get64 .r9 = BitVec.ofNat 64 p.msb ∧ s₀.regs.get64 .r10 = BitVec.ofNat 64 p.usb
        ∧ s₀.regs.get64 .rcx = BitVec.ofNat 64 p.np ∧ s₀.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c)
        ∧ s₀.regs.get64 .r8 = 0#64) := ⟨hdi, hax, h14, h15, h12, h9, h10, hcx, hsi, h8⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have PK := PLift.up (rsB_slot32' hm hF hrbp (d := 0x80) (by omega) (by omega))
    have P80 : PLift (frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h80⟩
    clear hFx h40 h30 h38 h48 h50 h80 hR i1 i2 i3 i4 i5 i6 hIm hK hl1 hl2 hm1 hm2 hnr hx hall
      hax h15 h9 h10 h8 hrbp hld hk1 hFi hz e0 h0x hx32 et hxn h64 hnm hik hdi h12 hsi h14
    generalize hFv : fOf st i = F at PLD NB
    have PFv : PLift (fOf st i = F) := ⟨hFv⟩
    clear hFv
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L3160]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1, AddrIndex.offset64_scale2,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, cc_nc_sub, cc_c_sub, not_dec_true, not_dec_false,
        decide_eq_true_eq, decide_eq_false_iff_not, (PR.down).2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.2.1,
        (PR.down).1, (PR.down).2.2.2.2.2.2.2.1, (PR.down).2.2.1] at *
    · rw [PLD.down]; rfl
    all_goals obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11⟩ := NB.down
    all_goals have hv := ‹loadInt _ _ 2 = some _›
    all_goals rw [PLD.down, Option.some.injEq] at hv
    all_goals subst hv
    all_goals simp only [rsB3_w16 (show F < 2 ^ 16 by omega),
      rsB3_w64 (show F < 2 ^ 32 by omega), rsB3_odd (show c.k0.toNat < 2 ^ 31 by omega)
        (show F < 2 ^ 31 by omega)] at *
    all_goals try rw [rsB3_na (by omega) (by omega) (by omega)] at *
    all_goals simp only [rsB3_idx (show i ≤ 48 by omega) n6, BitVec.toNat_ofNat,
      BitVec.toNat_setWidth, Nat.reduceMod, Nat.reducePow] at *
    · -- `jae L318c`: the inner loop stops at `j = i`
      rename_i hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L318c.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, PS.down.1,
        PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1, PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨p, i, PH.down.1, PH.down.2,
          (by unfold Inner; refine ⟨n5, ?_, PALL.down⟩; simp only [fOf, u16, PFv.down, oddOf, pk0]; omega),
          PX.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hm⟩, ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, (PR.down).1,
        (PR.down).2.1, (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.2.2, Prbp.down, pk0, arg1]
      · simp only [fOf, u16, PFv.down]
      · rw [rsB3_w64 (by omega)]; simp only [oddOf, fOf, u16, PFv.down]
      · refine (Nat.lt_or_eq_of_le ?_).imp id (fun h => ⟨h, by decide⟩)
        rw [V.L318c, V.L3160]
        simp only [VD.L318c, VD.L3160]
        rw [PK.down _ ?_ ?_, PK.down _ ?_ ?_, P80.down]
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, (PR.down).1, (PR.down).2.2.2.2.1,
            (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
            BitVec.toNat_ofNat, ne_eq]
          refine rsB_lex_le rfl (by (repeat' split) <;> omega) (by omega) (Or.inr ⟨rfl, Nat.zero_le _⟩)
        all_goals first | rfl | simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · -- `jb L3160`: on to `i - 1`
      rename_i hc hj
      have hi1 : 1 ≤ i := by omega
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L3160.mpr ⟨hC, ⟨?_, ?_⟩, st, fr, c, PF.down, hsp, hfm, hF, PS.down.1,
        PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1, PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨p, i - 1, PH.down.1, PH.down.2, PX.down, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        hm⟩, Or.inl ?_⟩
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, (PR.down).1,
        (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.2.2, Prbp.down, pk0, arg1]
      · intro i' h1 h2
        by_cases h : i' = i
        · subst h; simp only [fOf, u16, PFv.down, oddOf, pk0]; omega
        · exact PALL.down i' (by omega) h2
      · exact rsB3_dec hi1 (by omega) n6
      · simp only [V.L3160, VD.L3160]
        rw [PK.down _ ?_ ?_, PK.down _ ?_ ?_, P80.down]
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, (PR.down).1, (PR.down).2.2.2.2.1,
            (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
            rsB3_idx (show i ≤ 48 by omega) n6, rsB3_idx0 (show i ≤ 48 by omega) n6,
            BitVec.toNat_ofNat, ne_eq]
          refine rsB_lex_lt (by omega) (by (repeat' split) <;> omega) (by omega)
            (Or.inr ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩)
          omega
        all_goals first | rfl | simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    · -- `L3187`: unreachable (`i = 0` stops the inner loop as `msb ≥ k[0] ≥ 1`)
      rename_i hc hj
      exfalso
      have hi0 : i = 0 := by omega
      have := n7 hi0
      subst this
      omega


set_option maxRecDepth 100000 in
/-- `num_patches++`. -/
theorem blk_L30f8 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L30f8" ⟨"sbr_reset.L30f8", B.L30f8, some "sbr_reset.L3108"⟩ := by
  info_off
  measure_hb "L30f8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, j, hH, hnr, hj, hnp, hpos, hx, hdi, hax, h11, h12, h9, h10, hcx, hsi, h8⟩, hm⟩ := T.L30f8.mp hs
    clear hs
    obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    have hfj : fOf st j ≤ 64 := by
      have h1 := rsB_hf hFx j (by have := hj.1; have := hH.2.1.1; omega); omega
    have ld := c4_isSome (focus (Mm_npatch ..) hm)
    have PH : PLift (PHd a c (fOf st) p ∧ PNr p) := ⟨hH, hnr⟩
    have PJ : PLift (Inner (fOf st) (pk0 c) p.msb p.k j) := ⟨hj⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have PX := PLift.up hx
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
        ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h40, h30, h38, h48, h50, h80⟩
    have PR : PLift (s₀.regs.get64 .rdi = BitVec.ofNat 64 p.k ∧ s₀.regs.get64 .rax = BitVec.ofNat 64 p.k
        ∧ s₀.regs.get64 .r11 = BitVec.ofNat 64 (fOf st j) ∧ s₀.regs.get64 .r12 = arg1 t₀
        ∧ s₀.regs.get64 .r9 = BitVec.ofNat 64 p.msb ∧ s₀.regs.get64 .r10 = BitVec.ofNat 64 p.usb
        ∧ s₀.regs.get64 .rcx = BitVec.ofNat 64 p.np ∧ s₀.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c)
        ∧ s₀.regs.get64 .r8 = 0#64) := ⟨hdi, hax, h11, h12, h9, h10, hcx, hsi, h8⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    have NB : PLift (fOf st j ≤ 64 ∧ p.np ≤ 5 ∧ p.k ≤ 48 ∧ 0 < fOf st j - p.usb) :=
      ⟨hfj, hnp, by have := hH.2.1.1; omega, hpos⟩
    have S1 : PLift (∀ w : Int, Int.toBytes 4 w = Int.toBytes 4 ((p.np + 1 : Nat) : Int) →
        s₀.dmem.storeInt (arg1 t₀ + 0x4c330#64) 4 w
          =⋆ Mm k e a ra t₀ { st with x := { st.x with npatch := p.np + 1 } } fr) :=
      ⟨fun w hw => Mm_upd_npatch .. ▸ c4_store (focus (Mm_npatch ..) hm) w _ hw⟩
    clear hFx h40 h30 h38 h48 h50 h80 hH hnr hj hx hdi hax h11 h9 h10 h8 hrbp hfj hnp hpos
      e0 h0x hx32 et hxn h64 hnm
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L30f8]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, hcx, h12, hsi] at *
    · exact ld
    obtain ⟨n1, n2, n3, n4⟩ := NB.down
    have hc1 : (BitVec.setWidth 32 (BitVec.ofNat 64 p.np) + 1#32).toNat = p.np + 1 := by
      simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    refine ⟨T.L3108.mpr ⟨hC, ⟨?_, ?_⟩, { st with x := { st.x with npatch := p.np + 1 } }, fr, c,
      PF.down, hsp, hfm, hF, PS.down.1, PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1,
      PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
      ⟨p, j, PH.down.1, PH.down.2, PJ.down, n2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      S1.down _ (by rw [rsB4_tb, hc1])⟩, ?_⟩
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, (PR.down).1,
      (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1,
      (PR.down).2.2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.2, Prbp.down, pk0, arg1]
    · show ({ st.x with npatch := p.np + 1 } : Args) = _
      rw [PX.down]
      simp only [pxs, pbody, n4, ↓reduceIte]
    all_goals try simp only [pbody, n4, ↓reduceIte]
    all_goals try exact rsB_sw (by omega)
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, hc1]; simp only [BitVec.toNat_ofNat]
    · simp only [V.L3108, V.L30f8, VD.L3108, VD.L30f8, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        (PR.down).2.2.2.2.2.2.1, BitVec.toNat_setWidth, hc1, BitVec.toNat_ofNat]
      refine rsB_lex_le (by omega) (by omega) (by omega) (Or.inl ?_)
      (repeat' split) <;> omega

set_option maxRecDepth 100000 in
/-- Store `patch_start_subband[np]`. -/
theorem blk_L31b5 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L31b5" ⟨"sbr_reset.L31b5", B.L31b5, some "sbr_reset.L31d5"⟩ := by
  info_off
  measure_hb "L31b5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨hC, ⟨hrsp, hrbp⟩, st, fr, c, hFx, hsp, hfm, hF, h40, h30, h38, h48, h50, h80,
      ⟨p, j, hH, hnr, hj, hnp, hx, hdi, hax, h11, h14, h15, h12, hbx, hdx, h9, h10, hcx, hsi, h8⟩, hm⟩ := T.L31b5.mp hs
    clear hs
    obtain ⟨e0, h0x, hx32, et, hxn, h64, hnm, -, -⟩ := rsB_fix hFx
    have hpl : p.pst.length = 6 := hH.2.1.2.2.2.2.2.2.2.2.1
    have hstp : st.x.pstart = p.pst := by rw [hx]
    have hfj : fOf st j ≤ 64 := by
      have h1 := rsB_hf hFx j (by have := hj.1; have := hH.2.1.1; omega); omega
    have ha : t₀.regs.get64 .rsi + BitVec.ofNat 64 p.np + 312122#64
        = arg1 t₀ + 0x4c33a#64 + BitVec.ofNat 64 p.np := by simp only [arg1]; bv_omega
    have LD1 := region_load (o := p.np) (n := 1) (focus (Mm_pstart ..) hm) ha
      (by rw [hstp]; omega) (by rw [hstp, hpl]; decide)
    have hL1 : (loadInt s₀.dmem (t₀.regs.get64 .rsi + BitVec.ofNat 64 p.np + 312122#64) 1).isSome
        = true := by rw [LD1]; rfl
    have S2 : PLift (∀ w : Int, s₀.dmem.storeInt (t₀.regs.get64 .rsi + BitVec.ofNat 64 p.np + 312122#64) 1 w
        =⋆ Mm k e a ra t₀ { st with x := { st.x with pstart := wr st.x.pstart p.np (Int.toBytes 1 w) } } fr) :=
      ⟨fun w => Mm_upd_pstart .. ▸ region_store (o := p.np) (n := 1) (focus (Mm_pstart ..) hm) ha
        (by rw [hstp]; omega) (by rw [hstp, hpl]; decide) w⟩
    have e80 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64
        = t₀.regs.get64 .rsp - 8#64 - BitVec.ofNat 64 0x80 := by bv_omega
    have LD2 : PLift (∀ w : Int, loadInt (s₀.dmem.storeInt (t₀.regs.get64 .rsi + BitVec.ofNat 64 p.np
        + 312122#64) 1 w) (t₀.regs.get64 .rsp - 8#64 + 18446744073709551488#64) 4
          = some (Int.ofBytes (slice fr (rb 0x80) 4))) :=
      ⟨fun w => by rw [e80]; exact fr_load (S2.down w) hF (by omega) (by omega)⟩
    have NB : PLift (fOf st j ≤ 64 ∧ p.np ≤ 5 ∧ pk0 c ≤ 32 ∧ fOf st j - p.usb ≤ 64
        ∧ oddOf (pk0 c) (fOf st j) ≤ 1 ∧ pkx a (fOf st) ≤ 32 ∧ p.k ≤ 48) :=
      ⟨hfj, hnp, by omega, by omega, by unfold oddOf; omega, hx32, by have := hH.2.1.1; omega⟩
    have PH : PLift (PHd a c (fOf st) p ∧ PNr p) := ⟨hH, hnr⟩
    have PJ : PLift (Inner (fOf st) (pk0 c) p.msb p.k j) := ⟨hj⟩
    have PF : PLift (PFix a c (fOf st)) := ⟨hFx⟩
    have PX := PLift.up hx
    have PS : PLift (frSlot64 fr 0x40 = arg0 t₀ ∧ frSlot64 fr 0x30 = arg1 t₀
        ∧ frSlot64 fr 0x38 = BitVec.ofNat 64 c.nm ∧ frSlot64 fr 0x48 = arg1 t₀ + 0x4c1f0#64
        ∧ frSlot32 fr 0x50 = BitVec.ofNat 32 (ptop a c (fOf st))
        ∧ frSlot32 fr 0x80 = BitVec.ofNat 32 (pkx a (fOf st))) := ⟨h40, h30, h38, h48, h50, h80⟩
    have PR : PLift (s₀.regs.get64 .rdi = BitVec.ofNat 64 p.k ∧ s₀.regs.get64 .rax = BitVec.ofNat 64 p.k
        ∧ s₀.regs.get64 .r11 = BitVec.ofNat 64 (fOf st j)
        ∧ s₀.regs.get64 .r9 = BitVec.ofNat 64 p.msb ∧ s₀.regs.get64 .r10 = BitVec.ofNat 64 p.usb
        ∧ s₀.regs.get64 .rcx = BitVec.ofNat 64 p.np ∧ s₀.regs.get64 .rsi = BitVec.ofNat 64 (pk0 c)
        ∧ s₀.regs.get64 .r8 = 0#64 ∧ s₀.regs.get64 .rdx = arg1 t₀) :=
      ⟨hdi, hax, h11, h9, h10, hcx, hsi, h8, hdx⟩
    have Prbp : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hrbp⟩
    clear hFx h40 h30 h38 h48 h50 h80 hH hnr hj hx hdi hax h11 h9 h10 h8 hfj hnp
      e0 h0x hx32 et hxn h64 hnm LD1 hcx hsi
    generalize hP : Mm k e a ra t₀ st fr = P at hm
    simp only [B.L31b5]
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, AddrIndex.offset64_none,
        AddrIndex.offset64_scale1,
        Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm,
        BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.reduceMod, Nat.reducePow, Nat.reduceSub,
        Option.isSome_some, sw32_64, hdx, hbx, h12, h14, h15, hrbp, rsB4_nz, BitVec.and_self,
        not_dec_true, not_dec_false, decide_eq_true_eq, decide_eq_false_iff_not, (LD2.down _)] at *
    · exact hL1
    all_goals obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := NB.down
    · -- `jne L30f8`: a nonempty patch
      rename_i hne
      have hpos : 0 < fOf st j - p.usb := by
        refine Nat.pos_of_ne_zero fun h => hne ?_
        simp only [fOf, u16] at h; rw [h]; rfl
      left; apply Table.ofLabels_at
      obtain ⟨W, hW⟩ : ∃ W : Int, W = (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofNat 64 c.k0.toNat) - BitVec.setWidth 32 (BitVec.ofNat 64
            ((st.fm.getD (2 * j) 0).toNat + 256 * (st.fm.getD (2 * j + 1) 0).toNat - p.usb +
              oddOf c.k0.toNat ((st.fm.getD (2 * j) 0).toNat
                + 256 * (st.fm.getD (2 * j + 1) 0).toNat)))))).toInt := ⟨_, rfl⟩
      refine ⟨by decide, T.L30f8.mpr ⟨hC, ⟨?_, ?_⟩,
        { st with x := { st.x with pstart := wr st.x.pstart p.np (Int.toBytes 1 W) } }, fr, c,
        PF.down, hsp, hfm, hF, PS.down.1, PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1,
        PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨p, j, PH.down.1, PH.down.2, PJ.down, n2, hpos, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?mem⟩, Or.inl ?_⟩
      case mem =>
        subst hW
        exact S2.down _
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, (PR.down).1,
        (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1,
        (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2.2.2, Prbp.down, pk0, arg1]
      · rw [PX.down]; dsimp only
        rw [hW, rsB4_byte (by omega) (by omega) (by omega), rsB4_wr hpl (by omega)]
        rfl
      · simp only [V.L30f8, V.L31b5, VD.L30f8, VD.L31b5, Reg64s.get64_set64, reduceCtorEq,
          ↓reduceIte, (PR.down).2.2.2.2.2.1, BitVec.toNat_ofNat]
        exact rsB_lex_lt (by omega) (by (repeat' split) <;> omega) (by omega) (Or.inl (by omega))
    · -- `jmp L3108`: an empty patch, `msb = kx[1]`
      rename_i hz hld
      simp only [Option.some.injEq] at hld; subst hld
      have hD0 : ¬ 0 < fOf st j - p.usb := by
        intro h; apply absurd hz
        have := congrArg BitVec.toNat hz
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, fOf, u16, u8] at this h ⊢; omega
      have h80' := PS.down.2.2.2.2.2
      simp only [Nat.reduceSub] at h80'
      obtain ⟨W, hW⟩ : ∃ W : Int, W = (BitVec.setWidth 8 (BitVec.setWidth 64
          (BitVec.setWidth 32 (BitVec.ofNat 64 c.k0.toNat) - BitVec.setWidth 32 (BitVec.ofNat 64
            ((st.fm.getD (2 * j) 0).toNat + 256 * (st.fm.getD (2 * j + 1) 0).toNat - p.usb +
              oddOf c.k0.toNat ((st.fm.getD (2 * j) 0).toNat
                + 256 * (st.fm.getD (2 * j + 1) 0).toNat)))))).toInt := ⟨_, rfl⟩
      left; apply Table.ofLabels_at
      refine ⟨by decide, T.L3108.mpr ⟨hC, ⟨?_, ?_⟩,
        { st with x := { st.x with pstart := wr st.x.pstart p.np (Int.toBytes 1 W) } }, fr, c,
        PF.down, hsp, hfm, hF, PS.down.1, PS.down.2.1, PS.down.2.2.1, PS.down.2.2.2.1,
        PS.down.2.2.2.2.1, PS.down.2.2.2.2.2,
        ⟨p, j, PH.down.1, PH.down.2, PJ.down, n2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
        ?mem⟩, Or.inl ?_⟩
      case mem =>
        subst hW
        exact S2.down _
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, hrsp, (PR.down).1,
        (PR.down).2.1, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1,
        (PR.down).2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.1, (PR.down).2.2.2.2.2.2.2.1,
        (PR.down).2.2.2.2.2.2.2.2, Prbp.down, pk0, arg1, h80']
      · rw [PX.down]; dsimp only
        rw [hW, rsB4_byte (by omega) (by omega) (by omega), rsB4_wr hpl (by omega)]
        simp only [pbody, fOf, u16] at hD0 ⊢
        simp only [hD0, ↓reduceIte]
      all_goals try (simp only [pbody, fOf, u16] at hD0 ⊢; simp only [hD0, ↓reduceIte])
      all_goals try exact rsB3_w64 (by omega)
      · simp only [V.L3108, V.L31b5, VD.L3108, VD.L31b5, Reg64s.get64_set64, reduceCtorEq,
          ↓reduceIte, (PR.down).2.2.1, (PR.down).2.2.2.1, (PR.down).2.2.2.2.1,
          (PR.down).2.2.2.2.2.1, BitVec.toNat_ofNat]
        rw [slot32_of_load (v := Int.ofBytes (slice fr (rb 128) 4)) ?q1,
          slot32_of_load (v := Int.ofBytes (slice fr (rb 128) 4)) ?q2]
        case q1 | q2 =>
          first
          | (rw [Prbp.down]; exact fr_load hm hF (by omega) (by omega))
          | (simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; rw [Prbp.down]
             exact fr_load (S2.down _) hF (by omega) (by omega))
        simp only [rb, Nat.reduceSub]
        rw [h80']
        simp only [BitVec.toNat_eq, BitVec.toNat_setWidth, BitVec.toNat_ofNat, ne_eq]
        refine rsB_lex_lt ?_ ?_ ?_ (Or.inr ⟨rfl, Or.inl ?_⟩)
        all_goals (repeat' split) <;> omega


end Kraken.Examples.Sbr.Reset
