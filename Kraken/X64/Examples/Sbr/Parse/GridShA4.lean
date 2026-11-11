import Kraken.X64.Examples.Sbr.Parse.GridShA3

/-!
# `read_sbr_grid`: VARFIX (class 2), `bs_pointer` and the `bs_freq_res` fill (`get_bits1`)
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
theorem shA_gb1_idx (i p r : BitVec 32) (cf af : Bool) (hi : i.toNat ≤ p.toNat)
    (hp : p.toNat < 2 ^ 31) :
    (i + BitVec.setWidth 32 ((BitVec.setWidth 64 (r ^^^ r)).replaceLow
      (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (i - p)
        { cf := cf, af := af, of := (i - p).signed != i.signed - p.signed })).toNat))).toNat
      ≤ p.toNat :=
  gb1_idx i p r cf af hi hp

omit [CodeEnv] in
theorem shA_sw8_rl (a : BitVec 64) (b : BitVec 8) : BitVec.setWidth 8 (a.replaceLow b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_replaceLow8]
  have := b.isLt
  omega

omit [CodeEnv] in
theorem shA_frLoop_set {x : GArgs} {st : GSt} {rax r9 rsi : BitVec 64} {j : Nat}
    (h : FrLoop x st rax r9 rsi j) (hj : j ≤ 1) {i : BitVec 32} (hi : i.toNat ≤ x.p8.toNat)
    (v : BitVec 8) (hv : v.toNat ≤ 1) (e₀ : Nat) (he : e₀ = rax.toNat + j + 1) :
    FrLoop x ((st.withI i).setFr e₀ v) rax r9 rsi (j + 1) := by
  subst he
  obtain ⟨⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, -, hf0⟩, h1, hten⟩, h2, hrsi, hr9, hev, hlt, hok⟩ := h
  have hb : rax.toNat + j + 1 < 9 := by omega
  refine ⟨⟨⟨by simp only [List.length_set]; exact hfl, htl, hql, hn, hnn, hte9, htq, hi, ?_⟩,
    h1, hten⟩, h2, hrsi, hr9, hev, hlt, ?_⟩
  · simp only [u8]; rw [getD_set_ne _ _ _ _ (by omega)]; exact hf0
  · intro e he
    simp only [u8]; rw [getD_set_if _ _ _ _ (by omega)]
    split
    · simp only [UInt8.toNat_ofBitVec]; omega
    · exact hok e (by omega)

/-- `bs_freq_res[rax+1] = get_bits1(gb)`. -/
theorem blk_L4630 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4630" := by
  cfg_block
  measure_hb "L4630"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hL, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hL.1.1.2.2.2.2.2.2.2.1
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
    have hfl : st.fr.length = 9 := hL.1.1.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hra : (s₀.regs.get64 .rax).toNat + 1 < 9 := by
      have := hL.1.1.2.2.2.1; have := hL.2.2.2.1; have := hL.2.2.2.2.2.1; have := hL.2.2.2.2.1; omega
    have ea : arg3 t₀ + s₀.regs.get64 .rax + 13#64
        = arg3 t₀ + BitVec.ofNat 64 ((s₀.regs.get64 .rax).toNat + 1) + 0xc#64 := by
      bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    obtain ⟨iv, piv⟩ : ∃ iv, Hide (iv = st.i + BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12) ^^^
          BitVec.setWidth 32 (s₀.regs.get64 .r12))).replaceLow
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
      refine ⟨⟨hC, ?_, trivial, hdi, ?_⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      refine ⟨_, ?_, hT⟩
      apply shA_frLoop_set (j := 0) hL (by decide)
      · exact hiv
      · exact Nat.le_of_lt_succ (shr7_lt _)
      · omega

/-- `bs_freq_res[rax+2] = get_bits1(gb)`. -/
theorem blk_L4662 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4662" := by
  cfg_block
  measure_hb "L4662"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hRB, hdx, hdi, st, hL, hm⟩, hn⟩ := hs₀
    have hI : st.i.toNat ≤ x.p8.toNat := hL.1.1.2.2.2.2.2.2.2.1
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
    have hfl : st.fr.length = 9 := hL.1.1.1
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hRB.2.2.2
    have hra : (s₀.regs.get64 .rax).toNat + 2 < 9 := by
      have := hL.1.1.2.2.2.1; have := hL.2.2.2.1; have := hL.2.2.2.2.2.1; have := hL.2.2.2.2.1; omega
    have ea : arg3 t₀ + s₀.regs.get64 .rax + 14#64
        = arg3 t₀ + BitVec.ofNat 64 ((s₀.regs.get64 .rax).toNat + 2) + 0xc#64 := by
      bv_omega
    have hmT : Hide _ := hm
    have pRB : PLift (RB t₀ s₀) := ⟨hRB⟩
    obtain ⟨iv, piv⟩ : ∃ iv, Hide (iv = st.i + BitVec.setWidth 32
        ((BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .r12) ^^^
          BitVec.setWidth 32 (s₀.regs.get64 .r12))).replaceLow
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
      refine ⟨⟨hC, ?_, trivial, hdi, ?_⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, h13, hbx⟩
      refine ⟨_, ?_, hT⟩
      apply shA_frLoop_set (j := 1) hL (by decide)
      · exact hiv
      · exact Nat.le_of_lt_succ (shr7_lt _)
      · omega

end Kraken.Examples.Sbr.Grid
