import Kraken.X64.Examples.Sbr.Parse.GridShA4

/-!
# `read_sbr_grid`: the last `get_bits1` of the `bs_freq_res` fill, VARFIX `get_bits(ceil_log2)`
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem shA_fr_last {x : GArgs} {st : GSt} (hC : GridC x) (hP : FrPre x st) {r : Nat}
    (hok : FrOk st r) (hr : r + 1 = st.n.toNat) {i : BitVec 32} (hi : i.toNat ≤ x.p8.toNat)
    (v : BitVec 8) (hv : v.toNat ≤ 1) (e₀ : Nat) (he : e₀ = r + 1) :
    SInv x ((st.withI i).setFr e₀ v) ∧ 1 ≤ ((st.withI i).setFr e₀ v).n.toNat := by
  subst he
  obtain ⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, -, hf0⟩, h1, hten⟩ := hP
  have hb : r + 1 < 9 := by omega
  refine ⟨shA_frPre_sinv hC ⟨⟨by simp only [List.length_set]; exact hfl, htl, hql, hn, hnn, hte9,
    htq, hi, ?_⟩, h1, hten⟩ ?_, h1⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hf0
  · intro e he
    simp only [u8]; rw [getD_set_if _ _ _ _ (by omega)]
    split
    · simp only [UInt8.toNat_ofBitVec]; omega
    · exact hok e (by simp only at he; omega)

/-- `bs_freq_res[rax+1] = get_bits1(gb)` with `rax + 1 = n`: the last flag. -/
theorem blk_L4e73 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4e73" := by
  cfg_block
  measure_hb "L4e73"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, hr1, hok⟩, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hP.1.2.2.2.2.2.2.2.1
    have hoff := rd_off1 st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 1 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have pli : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.i.toInt))) := ⟨by rw [hdx]; exact gb_load_idx hg⟩
    have plp : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))) := ⟨by rw [hdx]; exact gb_load_p8 hg⟩
    have plb : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))) := ⟨by rw [hdx]; exact gb_load_buf hg⟩
    have hst := T_storeI hm
    have hp : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hfl : st.fr.length = 9 := hP.1.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hra : (s₀.regs.get64 .rax).toNat + 1 < 9 := by
      have := hP.1.2.2.2.1; omega
    have ea : arg3 t₀ + s₀.regs.get64 .rax + 13#64
        = arg3 t₀ + BitVec.ofNat 64 ((s₀.regs.get64 .rax).toNat + 1) + 0xc#64 := by
      bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    obtain ⟨iv, piv⟩ : ∃ iv, Hide (iv = st.i + BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r9) ^^^
          BitVec.setWidth 32 (s₀.regs.get64 .r9))).replaceLow
        (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (st.i - x.p8)
          { cf := (st.i - x.p8).unsigned != st.i.unsigned - x.p8.unsigned,
            af := ((st.i - x.p8).take 4).unsigned != (st.i.take 4).unsigned - (x.p8.take 4).unsigned,
            of := (st.i - x.p8).signed != st.i.signed - x.p8.signed })).toNat))) := ⟨_, rfl⟩
    have hiv : iv.toNat ≤ x.p8.toNat := by rw [show iv = _ from piv]; exact shA_gb1_idx _ _ _ _ _ hI hp
    have hTi := hst iv
    clear hm hRB hg
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · rw [hdx, hrbx, ea, T_loadFr (hst _) _ hra]; rfl
    · rw [hdx, hrbx, ea]
      simp only [shA_sw8_rl]
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rename_i w _ _ _ _ _
      have hT := T_storeFr hTi hfl _ hra (BitVec.setWidth 8 w >>> 7)
      refine ⟨⟨⟨hC, ?_, _, ?_, hT⟩, hdi⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      apply shA_fr_last hC hP hok hr1
      · exact hiv
      · exact Nat.le_of_lt_succ (shr7_lt _)
      · omega

/-- `get_bits(gb, ceil_log2[n])` (the VARFIX pointer bits; the count `eax` is havocked). -/
theorem blk_L45d8 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L45d8" := by
  cfg_block
  measure_hb "L45d8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, h4⟩, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hP.1.2.2.2.2.2.2.2.1
    have hoff := rd_off st.i x.p8 x.L hI hC.2.2.2.2.1
    have hbl := T_buf_load hm _ 4 hoff
    obtain ⟨F, hg⟩ := T_gb hm
    have pli : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 8#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.i.toInt))) := ⟨by rw [hdx]; exact gb_load_idx hg⟩
    have plp : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))) := ⟨by rw [hdx]; exact gb_load_p8 hg⟩
    have plb : PLift (s₀.dmem.loadInt (s₀.regs.get64 .rdx) 8
        = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))) := ⟨by rw [hdx]; exact gb_load_buf hg⟩
    have hst := T_storeI hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hm hRB hg
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_scale1, AddrIndex.offset64_none, Reg64s.get64_set64,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, reduceCtorEq,
      ↓reduceIte, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self,
      BitVec.ushiftRight_eq] at *
    all_goals have li := pli.down
    all_goals have lp := plp.down
    all_goals have lb := plb.down
    all_goals try simp only [li, lp, lb, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt, BitVec.setWidth_32_64_32] at *
    · exact hbl
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _, ⟨shA_frPre_withI hP (gb_clamp _ _ _ _), h4⟩, hst _⟩,
        Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

end Kraken.Examples.Sbr.Grid
