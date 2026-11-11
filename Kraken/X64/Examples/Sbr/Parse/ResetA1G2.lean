import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetA1G

/-!
# `sbr_reset`: `bs_freq_scale = 0`, the `f_master` fill loops (shard A1)

`vmovdqu %xmm0` stores of the `dk` broadcast (`bc16`) into `f_master`: eight words `dk` per store
(`a1_filled_bc`). `L1e30`: the first half of the 32-wide body.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Reset

variable [CodeEnv]

omit [CodeEnv] in
theorem a1_bc16_words (d : Nat) (hd : d = 1 ∨ d = 2) :
    ∀ t, t < 8 → ((bc16 d).toInt / 65536 ^ t) % 65536 = (d : Int) := by
  rcases hd with rfl | rfl <;> decide

omit [CodeEnv] in
theorem a1_filled_bc {l : List UInt8} (hl : l.length = 98) {d i : Nat} (hd : d = 1 ∨ d = 2)
    (hF : Filled l d i) (hi : i + 8 ≤ 49) :
    Filled (wr l (2 * i) (Int.toBytes 16 (bc16 d).toInt)) d (i + 8) := by
  intro x h1 h2
  have hb : (Int.toBytes 16 (bc16 d).toInt).length = 16 := Int.toBytes_length ..
  rcases Nat.lt_or_ge x i with hx | hx
  · rw [a1_u16_wr_ne (by rw [hb]; omega) (by rw [hb]; omega)]; exact hF x h1 hx
  · have := a1_u16_wr_words 8 (l := l) (j := i) (bc16 d).toInt (by omega) (x - i) (by omega)
    rw [show i + (x - i) = x by omega, a1_bc16_words d hd _ (by omega)] at this
    exact_mod_cast this

omit [CodeEnv] in
theorem a1_fm_addr_c (b : BitVec 64) {j c d : Nat} (hj : j ≤ 48) (hd : d = 311792 + 2 * c) (hc : c ≤ 40) :
    b + BitVec.ofNat 64 j * 2#64 + BitVec.ofNat 64 d = b + 0x4c1f0#64 + BitVec.ofNat 64 (2 * (j + c)) := by
  subst hd
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

section Mem16

variable {k : Nat} {e : REnv} {a : RArgs} {ra : Int64} {t₀ : MachineData} {st : St}
  {fr : List UInt8} {m : Mem 64}

theorem a1_fm16_store (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {i : Nat} (hi : i + 8 ≤ 49)
    {addr : BitVec 64} (ha : addr = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * i)) (v : Int) :
    m.storeInt addr 16 v =⋆ Mm k e a ra t₀ { st with fm := wr st.fm (2 * i) (Int.toBytes 16 v) } fr :=
  Mm_upd_fm .. ▸ region_store (focus (Mm_fm ..) hm) (o := 2 * i) ha (by omega) (by omega) v

theorem a1_fm16_isSome (hm : m =⋆ Mm k e a ra t₀ st fr) (hl : st.fm.length = 98) {i : Nat} (hi : i + 8 ≤ 49)
    {addr : BitVec 64} (ha : addr = arg1 t₀ + 0x4c1f0#64 + BitVec.ofNat 64 (2 * i)) :
    (m.loadInt addr 16).isSome = true := by
  rw [region_load (focus (Mm_fm ..) hm) (o := 2 * i) (n := 16) ha (by omega) (by omega)]
  rfl

end Mem16

theorem blk_L1e30 (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1e30" ⟨"sbr_reset.L1e30", B.L1e30, some "sbr_reset.L1e44"⟩ := by
  info_off
  measure_hb "L1e30"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, st, fr, hx, hsp, hfm, hF,
      ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, h32, hr8, hX, hdi, j, hr9, hj32, hjl, hfil⟩,
      hm⟩, h12, h15⟩ := T.L1e30.mp hs
    clear hs
    have h48 := f0_nm_48 hr hC.2.1 hq
    have hA4 : u8 a.sp 4 ≤ 1 := hC.2.2.2.1
    have hdk : u8 a.sp 4 + 1 = 1 ∨ u8 a.sp 4 + 1 = 2 := by (try simp only [u8] at hA4 ⊢); omega
    simp only [Xbc, BitVec.setWidth_eq] at hX
    generalize hNdef : nmOf (k2 - k0N a row) (u8 a.sp 4) = N at *
    have hj : j + 1 + 8 ≤ 49 ∧ j + 9 + 8 ≤ 49 := by omega
    have ha1 := a1_fm_addr_c (arg1 t₀) (j := j) (c := 1) (d := 311794) (by omega) rfl (by omega)
    have ha2 := a1_fm_addr_c (arg1 t₀) (j := j) (c := 9) (d := 311810) (by omega) rfl (by omega)
    have hm1 := a1_fm16_store hm hfm hj.1 ha1 (bc16 (u8 a.sp 4 + 1)).toInt
    have hfm1 : (wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)).length = 98 := by
      rw [wr_length (by rw [Int.toBytes_length, hfm]; omega), hfm]
    have hm2 := a1_fm16_store hm1 hfm1 hj.2 ha2 (bc16 (u8 a.sp 4 + 1)).toInt
    have hfil1 := a1_filled_bc hfm hdk hfil hj.1
    have hfm2 : (wr (wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (j + 9))
        (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)).length = 98 := by
      rw [wr_length (by rw [Int.toBytes_length, hfm1]; omega), hfm1]
    have hfil2 := a1_filled_bc hfm1 hdk hfil1 hj.2
    simp only [B.L1e30]
    vcgen
    all_goals try subst s₀
    all_goals try subst n
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64, h12, h15, hdx, hax, hcx,
      hsi, h13, hr9, hX, AddrIndex.offset64_scale2, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]
    · exact a1_fm16_isSome hm hfm hj.1 ha1
    · exact a1_fm16_isSome hm1 hfm1 hj.2 ha2
    · subst hNdef
      refine ⟨T.L1e44.mpr ⟨row, k2, hr, hk2, hle, hq, h3, ⟨hC, hBO, ⟨hrsp, hrbp⟩, ({ st with fm := wr (wr st.fm (2 * (j + 1)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt)) (2 * (j + 9)) (Int.toBytes 16 (bc16 (u8 a.sp 4 + 1)).toInt) } : St), fr, hx, hsp, hfm2, hF,
        ⟨hk2s, ⟨⟨h2, hxo, hnm, hdx⟩, hsi, h13, hax, hcx⟩, h32, hr8, ?_, hdi, j, hr9, hj32, hjl, hfil2⟩,
        hm2⟩, h12, h15⟩, by var_step⟩
      simp only [Xbc, BitVec.setWidth_eq]
      exact hX

end Kraken.Examples.Sbr.Reset
