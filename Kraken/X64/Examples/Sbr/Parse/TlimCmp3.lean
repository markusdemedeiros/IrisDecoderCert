import Kraken.X64.Examples.Sbr.Parse.TlimCmp2

/-!
# `sbr_make_f_tablelim`: the compaction loop, steps (`L4363`, `L4370`, `L42d0`)

`L4363` stores `repl`, `L4370` closes a `drop`/`repl` step (`in + 1`, `n_lim - 1`), `L42d0`
an `adv` step (`out + 1`, `in + 1`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

theorem av_set (fl : List UInt8) (o u : Nat) (v : Int) (hv : v % 65536 = (u : Int))
    (hl : fl.length = 60) (ho : o < 30) : AV (setW2 fl o v) = upd (AV fl) o u := by
  funext q
  simp only [AV, upd]
  rw [u16_setW2 _ _ _ (by omega)]
  split
  · rw [hv]; simp
  · rfl

theorem v16 (u : Nat) (hu : u < 65536) :
    (BitVec.setWidth 16 (BitVec.ofNat 64 u)).toInt % 65536 = (u : Int) := by
  rw [sw16_64 u hu]; omega

variable [CodeEnv]

theorem mu_ld {t₀ s : MachineData} {L o : Nat}
    (hld : s.dmem.loadInt (s.regs.get64 .rbx + 311788#64) 4 = some (Int.ofBytes (Int.toBytes 4 (L : Int))))
    (h14 : s.regs.get64 .r14 = pA t₀) (hcx : s.regs.get64 .rcx = pA t₀ + v64 (2 * o))
    (hL : L < 2 ^ 31) (hw : (pA t₀).toNat + 2 * o < 2 ^ 64) : mu s = L - o := by
  simp only [mu, rN, ld4]
  rw [hld, Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by omega), hcx, h14, addr_toNat _ _ hw]
  show L - _ = _
  omega

theorem blk_L4363 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4363" := by
  cfg_block
  measure_hb "L4363"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hsi⟩, hm⟩, hn⟩ := hs₀
    rw [var_L4363] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -, -, -, -, -, -, -, -, hw0⟩ := hC'
    have hfl : fl.length = 60 := hL.1
    have hpA := pA_toNat hC
    have hL1' : L + 1 ≤ x.a.n0 + x.a.npatch := hL1
    have hL31 : L < 2 ^ 31 := by omega
    have ho30 : o < 30 := by omega
    have hw : (pA t₀).toNat + 2 * o < 2 ^ 64 := by omega
    have hmu := mu_val hm hbx h14 hcx hL31 hw
    have hFl := focus (T_fl k x ra t₀ (Saved t₀) _) hm
    have hst : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨setW2 fl o v, L, stk, pb⟩ := fun v =>
      focus (T_fl k x ra t₀ (Saved t₀) ⟨setW2 fl o v, L, stk, pb⟩).symm
        (st16 hFl o hcx (by simp only; omega) (by simp only; omega) v)
    have hld : ∀ v, (s₀.dmem.storeInt (s₀.regs.get64 .rcx) 2 v).loadInt
        (s₀.regs.get64 .rbx + 311788#64) 4 = some (Int.ofBytes (Int.toBytes 4 (L : Int))) := by
      intro v
      rw [hbx]
      exact loadInt_sep _ _ 4 _ _ (focus (T_nl k x ra t₀ (Saved t₀) ⟨setW2 fl o v, L, stk, pb⟩) (hst v))
        (Int.toBytes_length 4 _) (by omega)
    have hl16 := ld16 hFl o hcx (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hst
    have hlH : Hide _ := hld
    clear hm hFl hst hld
    vcgen
    all_goals try call_simp
    all_goals first | (rename_i hs _ _; subst hs) | (rename_i hs; subst hs)
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat] at *
    · rw [hl16]; rfl
    · unfold Hide at hlH; rw [hlH]; rfl
    rename_i hx
    unfold Hide at hlH hsH
    rw [hlH, Option.some.injEq] at hx
    subst hx
    simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast, zx_small _ hL31]
    rw [hsi]
    rw [tab_L4370]
    refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa,
      setW2 fl o (BitVec.setWidth 16 (v64 (AV fl (o + 1 + (NN x - 1 - L))))).toInt, stk, pb, _, o, L,
      ⟨by rw [setW2_length _ _ _ (by omega)]; exact hfl, hL.2.1, hL.2.2⟩, hP,
      ⟨hS, hL1, hoL, rfl, ?_, ?_, fun r R h => hCm r R (Compact.repl hol (by
        rw [av_set fl o _ _ (v16 _ (u16_lt fl _)) hfl ho30] at h; exact h))⟩, hol, ?_, hsH _⟩, ?var⟩
    case var =>
      rw [hmu, var_L4370, mu_ld (t₀ := t₀) (o := o) (L := L)
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hlH _)
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact h14)
        (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hcx) hL31 hw]
      omega
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
      h14, hcx, hax]

omit [CodeEnv] in
theorem nl_dec32 (L : Nat) (h1 : 1 ≤ L) (h : L < 2 ^ 31) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofNat 32 L - 1#32))
      = BitVec.ofNat 32 (L - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem nl_dec64 (L : Nat) (h1 : 1 ≤ L) (h : L < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.ofNat 32 L - 1#32) = BitVec.ofNat 64 (L - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem sw32 (n : Nat) : BitVec.setWidth 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem rax2 (p : BitVec 64) (n : Nat) (h : n < 2 ^ 31) :
    BitVec.setWidth 64 2#64 + (p + BitVec.ofNat 64 (2 * n)) = p + BitVec.ofNat 64 (2 * (n + 1)) := by
  bv_omega

theorem blk_L4370 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L4370" := by
  cfg_block
  measure_hb "L4370"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, hol, hdx, hm⟩, hn⟩ := hs₀
    rw [var_L4370] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -, -, -, -, -, -, -, -, hw0⟩ := hC'
    have hfl : fl.length = 60 := hL.1
    have hpA := pA_toNat hC
    have hL1' : L + 1 ≤ x.a.n0 + x.a.npatch := hL1
    have hL31 : L < 2 ^ 31 := by omega
    have hw : (pA t₀).toNat + 2 * o < 2 ^ 64 := by omega
    have hmu := mu_val hm hbx h14 hcx hL31 hw
    have hb' : s₀.regs.get64 .rbx + 311788#64 = sA t₀ + 0x4c1ec#64 := by rw [hbx]
    have hs4 : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbx + 311788#64) 4 v =⋆
        Int.toBytes 4 v =@ (sA t₀ + 0x4c1ec#64) ⋆ Tnl k x ra t₀ (Saved t₀) fl stk pb := by
      intro v
      rw [hb']
      exact storeInt_sep _ 4 _ _ _ ⟨focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, L, stk, pb⟩) hm,
        Int.toBytes_length 4 _⟩ v
    have hsH : Hide _ := hs4
    have hl4 : (s₀.dmem.loadInt (s₀.regs.get64 .rbx + 311788#64) 4).isSome = true := by
      rw [hb', loadInt_sep _ _ 4 _ _ (focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, L, stk, pb⟩) hm)
        (Int.toBytes_length 4 _) (by omega)]; rfl
    have hL0 : 1 ≤ L := by omega
    have hi31 : o + 1 + (NN x - 1 - L) < 2 ^ 31 := by simp only [NN]; omega
    have hmem : ∀ m : Mem 64, (m =⋆ Int.toBytes 4 (BitVec.ofNat 32 (L - 1)).toInt =@ (sA t₀ + 0x4c1ec#64)
        ⋆ Tnl k x ra t₀ (Saved t₀) fl stk pb) → (m =⋆ T k x ra t₀ (Saved t₀) ⟨fl, L - 1, stk, pb⟩) := by
      intro m h5
      rw [toInt32_small _ (by omega)] at h5
      exact focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, L - 1, stk, pb⟩).symm h5
    clear hm hs4
    vcgen
    all_goals try call_simp
    all_goals first | (rename_i hs hc; subst hs) | (rename_i hs; subst hs)
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hdx, nl_dec32 L hL0 hL31,
      nl_dec64 L hL0 hL31, sw32] at *
    · exact hl4
    · rw [cc_c_sub _ _ _ (by rfl)] at hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L42eb]
        unfold Hide at hsH
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, o + 1 + (NN x - 1 - L) + 1,
          o, L - 1, ⟨hL.1, hL.2.1, hL.2.2⟩, hP, ⟨hS, by simp only [NN]; omega, by omega, by simp only [NN]; omega,
          ?_, ?_, hCm⟩, ?_, ?mem⟩
        case mem => exact hmem _ (hsH (BitVec.ofNat 32 (L - 1)).toInt)
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, rax2 _ _ hi31]
      · rw [var_L42eb, hmu]
        unfold Hide at hsH
        have hm' := hmem _ (hsH (BitVec.ofNat 32 (L - 1)).toInt)
        rw [hb'] at hm'
        have hlv := loadInt_sep _ _ 4 _ _ (focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, L - 1, stk, pb⟩) hm')
          (Int.toBytes_length 4 _) (by omega)
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hb', hlv, hcx, h14,
          Option.getD_some]
        rw [Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by omega), addr_toNat _ _ hw]
        show 64 * ((L - 1) - _) + 63 < _
        omega
    · exfalso
      rw [cc_c_sub _ _ _ (by rfl)] at hc
      simp at hc
      omega

omit [CodeEnv] in
theorem rcx2 (p : BitVec 64) (n : Nat) (h : n < 2 ^ 31) :
    p + BitVec.ofNat 64 (2 * n) + 2#64 = p + BitVec.ofNat 64 (2 * (n + 1)) := by
  bv_omega

theorem blk_L42d0 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L42d0" := by
  cfg_block
  measure_hb "L42d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hsi⟩, hm⟩, hn⟩ := hs₀
    rw [var_L42d0] at hn
    subst hn
    subst hi
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -, -, -, -, -, -, -, -, hw0⟩ := hC'
    have hfl : fl.length = 60 := hL.1
    have hpA := pA_toNat hC
    have hL1' : L + 1 ≤ x.a.n0 + x.a.npatch := hL1
    have hL31 : L < 2 ^ 31 := by omega
    have ho30 : o + 1 < 30 := by omega
    have hw : (pA t₀).toNat + 2 * o < 2 ^ 64 := by omega
    have hw1 : (pA t₀).toNat + 2 * (o + 1) < 2 ^ 64 := by omega
    have hi31 : o + 1 + (NN x - 1 - L) < 2 ^ 31 := by simp only [NN]; omega
    have hmu := mu_val hm hbx h14 hcx hL31 hw
    have hcx2 : s₀.regs.get64 .rcx + 2#64 = pA t₀ + v64 (2 * (o + 1)) := by
      rw [hcx]; exact rcx2 _ _ (by omega)
    have hFl := focus (T_fl k x ra t₀ (Saved t₀) _) hm
    have hst : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rcx + 2#64) 2 v =⋆
        T k x ra t₀ (Saved t₀) ⟨setW2 fl (o + 1) v, L, stk, pb⟩ := fun v =>
      focus (T_fl k x ra t₀ (Saved t₀) ⟨setW2 fl (o + 1) v, L, stk, pb⟩).symm
        (st16 hFl (o + 1) hcx2 (by simp only; omega) (by simp only; omega) v)
    have hld : ∀ v, (s₀.dmem.storeInt (s₀.regs.get64 .rcx + 2#64) 2 v).loadInt
        (s₀.regs.get64 .rbx + 311788#64) 4 = some (Int.ofBytes (Int.toBytes 4 (L : Int))) := by
      intro v
      rw [hbx]
      exact loadInt_sep _ _ 4 _ _ (focus (T_nl k x ra t₀ (Saved t₀) ⟨setW2 fl (o + 1) v, L, stk, pb⟩) (hst v))
        (Int.toBytes_length 4 _) (by omega)
    have hl16 := ld16 hFl (o + 1) hcx2 (by simp only; omega) (by simp only; omega)
    have hsH : Hide _ := hst
    have hlH : Hide _ := hld
    clear hm hFl hst hld
    vcgen
    all_goals try call_simp
    all_goals first | (rename_i hs _ _ _; subst hs) | (rename_i hs _ _; subst hs) | (rename_i hs; subst hs)
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat] at *
    · rw [hl16]; rfl
    · unfold Hide at hlH; rw [hlH]; rfl
    all_goals rename_i v hc hx
    all_goals unfold Hide at hlH hsH
    all_goals rw [hlH, Option.some.injEq] at hx
    all_goals subst hx
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast,
      zx_small _ hL31, sw32] at hc ⊢
    · exfalso
      rw [cc_nc_sub _ _ _ (by rfl)] at hc
      simp at hc
      omega
    · rw [hsi, tab_L42eb]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa,
        setW2 fl (o + 1) (BitVec.setWidth 16 (v64 (AV fl (o + 1 + (NN x - 1 - L))))).toInt, stk, pb,
        o + 1 + (NN x - 1 - L) + 1, o + 1, L,
        ⟨by rw [setW2_length _ _ _ (by omega)]; exact hfl, hL.2.1, hL.2.2⟩, hP,
        ⟨hS, hL1, by omega, by simp only [NN]; omega, ?_, ?_, fun r R h => hCm r R (Compact.adv hol (by
          rw [av_set fl (o + 1) _ _ (v16 _ (u16_lt fl _)) hfl ho30] at h; exact h))⟩, ?_, hsH _⟩, ?var⟩
      case var =>
        rw [hmu, var_L42eb, mu_ld (t₀ := t₀) (o := o + 1) (L := L)
          (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact hlH _)
          (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact h14)
          (by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hcx]
              exact rax2 _ _ (by omega)) hL31 hw1]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, rax2 _ _ hi31, rax2 _ o (by omega)]

end Kraken.Examples.Sbr.Tlim
