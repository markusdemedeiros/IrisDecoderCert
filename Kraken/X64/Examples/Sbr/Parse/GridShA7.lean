import Kraken.X64.Examples.Sbr.Parse.GridShA6

/-!
# `read_sbr_grid`: FIXVAR (class 1), the `bs_freq_res` fill from the top (`FrD`)
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem shA_frD_withI {x : GArgs} {st : GSt} {a b : BitVec 32} {Q : Nat → Prop}
    (h : FrD x st a b Q) {i : BitVec 32} (hi : i.toNat ≤ x.p8.toNat) : FrD x (st.withI i) a b Q :=
  ⟨shA_frPre_withI h.1 hi, h.2⟩

omit [CodeEnv] in
theorem shA_c_sub32 (a b : BitVec 32) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((a - b).unsigned != a.unsigned - b.unsigned)) :
    CondCode.c.interp (StatusFlags.from_result (a - b) f) = decide (a.toNat < b.toNat) := by
  rw [CondCode.interp_c, StatusFlags.cf_from_result, hf]
  grind [BitVec.unsigned_eq]

omit [CodeEnv] in
theorem shA_frD_set {x : GArgs} {st : GSt} (hP : FrPre x st) {j : Nat} (hj : j < st.n.toNat)
    (hT : FrTop st j) (v : BitVec 8) (hv : v.toNat ≤ 1) :
    FrPre x (st.setFr (st.n.toNat - j) v) ∧ FrTop (st.setFr (st.n.toNat - j) v) (j + 1) := by
  obtain ⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, hf0⟩, h1, hten⟩ := hP
  refine ⟨⟨⟨by simp only [List.length_set]; exact hfl, htl, hql, hn, hnn, hte9, htq, hi, ?_⟩,
    h1, hten⟩, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hf0
  · intro e he1 he2
    dsimp only at he1 he2
    simp only [u8]; rw [getD_set_if _ _ _ _ (by omega)]
    split
    · simp only [UInt8.toNat_ofBitVec]; omega
    · exact hT e (by omega) he2

/-- The `get_bits1` read of the FIXVAR fill (the byte kept in `r9`, the shift in `L4905`). -/
theorem blk_L48d0 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L48d0" := by
  cfg_block
  measure_hb "L48d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hD, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hD.1.1.2.2.2.2.2.2.2.1
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
    have hfl : st.fr.length = 9 := hD.1.1.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    obtain ⟨iv, piv⟩ : ∃ iv, Hide (iv = st.i + BitVec.setWidth 32
        ((BitVec.setWidth 64 (st.i >>> 3 ^^^ st.i >>> 3)).replaceLow
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
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rw [hdx]
      refine ⟨⟨hC, ?_, rfl, hdi, _, shA_frD_withI hD hiv, hTi⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `r10d = bs_num_env`, `r11d = n - j`, the check `n - j < 9` (holds). -/
theorem blk_L48f3 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L48f3" := by
  cfg_block
  measure_hb "L48f3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, j, hj, hsi, hax, hT, -⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hld := T_loadN hm
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have key : BitVec.setWidth 32 (s₀.regs.get64 .rax + BitVec.setWidth 64 st.n)
        = BitVec.ofNat 32 (st.n.toNat - j) := by bv_omega
    clear hm hRB
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt,
      BitVec.setWidth_32_64_32] at *
    · exfalso
      have hf := ‹CondCode.nc.interp _ = true›
      rw [key] at hf
      have hv : st.n.toNat - j ≤ 8 := by omega
      generalize st.n.toNat - j = v at hf hv
      rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨ v = 8)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> revert hf <;> decide
    · obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      refine ⟨⟨hC, ?_, hdx, hdi, st, ⟨hP, j, hj, hsi, hax, hT, key, rfl⟩, hmT⟩, Nat.le_refl _⟩
      simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      exact ⟨hsp, hbp, h13, hbx⟩

/-- `bs_freq_res[n - j] = get_bits1`, `j + 1`; the back edge to `L48d0` or the exit to `L4ea2`. -/
theorem blk_L4905 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4905" := by
  cfg_block
  measure_hb "L4905"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, ⟨hP, j, hj, hsi, hax, hT, h11, h10⟩, hm⟩, hn⟩ := hs₀
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have h8 : st.n.toNat ≤ 8 := hP.1.2.2.2.1
    have hfl : st.fr.length = 9 := hP.1.1
    have ea : arg3 t₀ + BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r11)) + 12#64
        = arg3 t₀ + BitVec.ofNat 64 (st.n.toNat - j) + 0xc#64 := by
      rw [h11]; bv_omega
    have hst := T_storeFr hm hfl (st.n.toNat - j) (by omega)
    have hld := T_loadFr hm (st.n.toNat - j) (by omega)
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    clear hRB hm
    vcgen [shl_cl32_havoc]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [AddrIndex.offset64_none, AddrIndex.offset64_scale1, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, hrbx, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, get64_ite, ite_self, BitVec.ushiftRight_eq] at *
    all_goals try rw [ea]
    · rw [hld]; rfl
    · have hc := ‹CondCode.c.interp _ = true›
      rw [BitVec.setWidth_32_64_32, shA_c_sub32 _ _ _ rfl, hsi, h10] at hc
      have hj1 : j + 1 < st.n.toNat := by simp only [decide_eq_true_eq] at hc; bv_omega
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rename_i w _ _ _ _ _
      obtain ⟨hP', hT'⟩ := shA_frD_set hP hj hT (BitVec.setWidth 8 w >>> 7)
        (Nat.le_of_lt_succ (shr7_lt _))
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, BitVec.setWidth_32_64_32, shA_sw8_rl]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h13, hbx⟩, hdx, hdi, _,
        ⟨hP', j + 1, hj1, by rw [hsi]; bv_omega, by rw [hax]; bv_omega, hT', trivial⟩, hst _⟩, Or.inl ?_⟩
      simp only [Nat.add_eq, hsi]; bv_omega
    · have hc := ‹CondCode.c.interp _ = false›
      rw [BitVec.setWidth_32_64_32, shA_c_sub32 _ _ _ rfl, hsi, h10] at hc
      have hj1 : j + 1 = st.n.toNat := by simp only [decide_eq_false_iff_not] at hc; bv_omega
      obtain ⟨hsp, hbp, h13, hbx⟩ := pRB.down
      rename_i w _ _ _ _ _
      obtain ⟨hP', hT'⟩ := shA_frD_set hP hj hT (BitVec.setWidth 8 w >>> 7)
        (Nat.le_of_lt_succ (shr7_lt _))
      have hF : FrOk (st.setFr (st.n.toNat - j) (BitVec.setWidth 8 w >>> 7))
          (st.setFr (st.n.toNat - j) (BitVec.setWidth 8 w >>> 7)).n.toNat := by
        intro e he
        dsimp only at he
        by_cases e0 : e = 0
        · subst e0; exact hP'.1.2.2.2.2.2.2.2.2
        · exact hT' e (by dsimp only; omega) he
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, shA_sw8_rl]
      refine ⟨by decide, ⟨⟨hC, ⟨hsp, hbp, h13, hbx⟩, _, ⟨shA_frPre_sinv hC hP' hF, hP.2.1⟩, hst _⟩, hdi⟩,
        Or.inl ?_⟩
      simp only [Nat.add_eq, hsi]; bv_omega

end Kraken.Examples.Sbr.Grid
