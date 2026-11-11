import Kraken.X64.Examples.Sbr.Parse.DecExtHarm

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the extension data (`read_sbr_data`, l.1100-1110)

`Lb1a` reads `bs_extended_data` and stores the reader's index; `Lb40`/`Lb64` the size
(`bs_extension_size`, `bs_esc_count`), `Lb86` the bit count, the loop `Lb9d` the extension ids
(`ff_ps_read_data` at `Lbe6`), the rest skips bits (`skip_bits_long`) and logs.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- The reader's next index after the inlined `get_bits1` (`cmp; setl; add`), from the index `a`,
`size_in_bits_plus8` `p`, the cleared register `x`. -/
abbrev setlIdx (a p x : BitVec 32) : BitVec 32 :=
  a + BitVec.setWidth 32 ((BitVec.setWidth 64 (x ^^^ x)).replaceLow
    (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (a - p)
      { cf := (a - p).unsigned != a.unsigned - p.unsigned,
        af := ((a - p).take 4).unsigned != (a.take 4).unsigned - (p.take 4).unsigned,
        of := (a - p).signed != a.signed - p.signed })).toNat))

omit [CodeEnv] in
theorem setlIdx_le (a p x : BitVec 32) (ha : a.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (setlIdx a p x).toNat ≤ p.toNat :=
  setl_inc a p x _ _ ha hp

theorem blk_Lb1a (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lb1a" := by
  cfg_block
  measure_hb "Lb1a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hR⟩, hn⟩ := hs₀
    var_n hn
    obtain ⟨hax, hsi, hdi⟩ := hR
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    obtain ⟨g, hg⟩ : ∃ g, g = setlIdx ((s₀.regs.get64 .rax).setWidth 32)
        ((s₀.regs.get64 .rsi).setWidth 32) ((s₀.regs.get64 .rdx).setWidth 32) := ⟨_, rfl⟩
    have hgl : g.toNat ≤ X.r.p8.toNat := by
      rw [hg, ← hsi]; exact setlIdx_le _ _ _ (hsi ▸ hax) (hsi ▸ hC.2.2.2.1.2.1)
    have p_hg := PLift.up hg
    clear hg
    vcgen [shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    case' vc3 => left; apply Table.ofLabels_at; rw [table.match_1.eq_30]
    case' vc4 =>
      rw [table.match_1.eq_46]
      all_goals try (intro e; simp only [String.reduceEq] at e)
      unfold tableE; rw [tableE.match_1.eq_1]
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals have hg := p_hg.down; clear p_hg
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hax hC.2.2.2.1.2.2.1)
    case vc3 =>
      refine ⟨by decide, ⟨hC, ⟨trivial, trivial, trivial⟩, i0, g, d, ih, hE, ⟨hgl, hrb.2⟩, ?_⟩, ?_⟩
      · subst hg
        simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
        simp only [sw32_64] at hm
        sep_close hm
        all_goals simp only [sw32_64]
      · rw [var_L4e2]; exact Or.inl (by omega)
    case vc4 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, g, d, ih, ⟨hE, ?_⟩, ⟨hgl, hrb.2⟩, ?_⟩, hsi, trivial⟩,
        ?_⟩
      iterate 3
        · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hsp, hbp, h14]
      · rw [sw32_64, hg]
      · subst hg
        simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        simp only [sw32_64] at hm
        sep_close hm
        all_goals simp only [sw32_64]
      · rw [var_Lb40]; omega

/-- A goal `table … l s` with `l` a label of `tableE`: the main table's last case, then the
`tableE` case `e` (the side goals: `l` differs from the earlier patterns). -/
macro "to_tableE " e:ident : tactic => `(tactic| (
  rw [table.match_1.eq_46]
  all_goals try (intro h; simp only [String.reduceEq] at h)
  unfold tableE
  rw [$e:ident]
  all_goals try (intro h; simp only [String.reduceEq] at h)))

omit [CodeEnv] in
/-- `bs_extension_size + bs_esc_count` (`get_bits(8) + 15`). -/
theorem add15_le (v : BitVec 32) :
    (BitVec.setWidth 32 15#64 + v.ushiftRight 24).toNat ≤ 270 := by
  have h := shr_lt v 8 (by decide)
  rw [show BitVec.setWidth 32 15#64 = 15#32 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat]
  have h' : (v.ushiftRight 24).toNat < 256 := h
  omega

omit [CodeEnv] in
/-- `bs_extension_size * 8` (`shl $3`), not below 8 (`jl` not taken). -/
theorem shl3_ge (x : BitVec 32) (h : x.toNat ≤ 270)
    (hc : decide ((x <<< 3).toInt < (BitVec.setWidth 32 8#64).toInt) = false) :
    8 ≤ (x <<< 3).toNat ∧ (x <<< 3).toNat ≤ 2160 := by
  have e : (x <<< 3).toNat = x.toNat * 8 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  rw [show (BitVec.setWidth 32 8#64).toInt = 8 from rfl, BitVec.toInt_eq_toNat_cond, e] at hc
  simp only [decide_eq_false_iff_not] at hc
  split at hc <;> omega

omit [CodeEnv] in
/-- The clamp of `skip_bits_long` (`av_clip(n, -index, size_in_bits_plus8 - index)`, two `cmovl`)
plus `index` stays within `[0, size_in_bits_plus8]`. -/
theorem sclamp_le (g p r : BitVec 32) (hg : g.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (g + if r.toInt < (-g).toInt then -g else if r.toInt < (p - g).toInt then r else p - g).toNat
      ≤ p.toNat := by
  have hgi : (-g).toInt = -(g.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_neg]; split <;> omega
  have hpi : (p - g).toInt = ((p.toNat - g.toNat : Nat) : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_sub]; split <;> omega
  rw [hgi, hpi]
  split
  · rw [BitVec.toNat_add, BitVec.toNat_neg]; omega
  · split
    · rename_i h1 h2
      rw [BitVec.toInt_eq_toNat_cond] at h1 h2
      rw [BitVec.toNat_add]
      split at h1 <;> omega
    · rw [BitVec.toNat_add, BitVec.toNat_sub]; omega

set_option hygiene false in
/-- The goals of a jump in the extension blocks: the frame registers (`hsp`, `hbp`, `h14`), the
reader's registers (`hsi`, `hdi`), the memory (`hm`), the variant. -/
macro "ext_close" : tactic => `(tactic| first
  | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64, hsp, hbp, h14];
     done)
  | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64, hsi, hdi]; done)
  | ((try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64])
     first
       | exact Nat.le_of_lt (Nat.lt_of_lt_of_le (shr_lt _ 4 (by decide)) (by decide))
       | exact add15_le _)
  | exact not_false
  | ((try left)
     first
       | rw [var_Lb64] | rw [var_Lb86] | rw [var_Lb9d] | rw [var_Lc1c] | rw [var_Lc1f]
       | rw [var_L4e2] | rw [var_Lca0] | rw [var_Lcbb] | rw [var_Lcc0] | rw [var_Lcd3]
       | rw [var_Lc41] | rw [var_Lc4b] | rw [var_Lc67] | rw [var_Lc7d] | rw [var_Lc83]
       | rw [var_Lbd4] | rw [var_Lbe6] | rw [var_Lbf5]
     (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64,
       Reg64s.get_low32])
     omega)
  | (simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
     try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
     sep_close hm
     all_goals simp only [sw32_64]))

theorem blk_Lb40 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lb40" := by
  cfg_block
  measure_hb "Lb40"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hdx⟩, hrb, hm⟩, hsi, hdi⟩, hn⟩ := hs₀
    var_n hn
    have hgi : (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).toNat ≤ X.r.p8.toNat := by
      rw [hdx]; exact hrb.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_3)
    all_goals try (to_tableE tableE.match_1.eq_2)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off _ _ _ hgi hC.2.2.2.1.2.2.1)
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64] at hm ⊢
    all_goals generalize hv : (if CondCode.c.interp _ = true then _ else _ : BitVec 32) = v at hm ⊢
    all_goals have hb : v.toNat ≤ X.r.p8.toNat := by subst hv; rw [← hsi]; exact clamp_le _ _ _ _
    case vc3 =>
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, hE, ⟨hb, hrb.2⟩, ?_⟩, ?_⟩, ?_⟩
      all_goals ext_close
    case vc4 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, ⟨hE, ?_⟩, ⟨hb, hrb.2⟩, ?_⟩, ?_, ?_⟩, ?_⟩
      all_goals ext_close

theorem blk_Lb64 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lb64" := by
  cfg_block
  measure_hb "Lb64"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hdx⟩, hrb, hm⟩, hsi, hdi⟩, hn⟩ := hs₀
    var_n hn
    have hgi : (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).toNat ≤ X.r.p8.toNat := by
      rw [hdx]; exact hrb.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (to_tableE tableE.match_1.eq_3)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off _ _ _ hgi hC.2.2.2.1.2.2.1)
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64] at hm ⊢
    all_goals generalize hv : (if CondCode.c.interp _ = true then _ else _ : BitVec 32) = v at hm ⊢
    all_goals have hb : v.toNat ≤ X.r.p8.toNat := by subst hv; rw [← hsi]; exact clamp_le _ _ _ _
    all_goals try (refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, hE, ⟨hb, hrb.2⟩, ?_⟩, ?_⟩, ?_⟩)
    all_goals ext_close

theorem blk_Lb86 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lb86" := by
  cfg_block
  measure_hb "Lb86"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hax⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_8)
    all_goals try (to_tableE tableE.match_1.eq_4)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    case vc2 =>
      refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
      all_goals ext_close
    case vc4 =>
      rename_i hc _
      simp only [CondCode.interp_l_cmp_toInt32, Reg64s.get_low32, sw32_64] at hc
      have hb := shl3_ge _ hax hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64,
        Reg64s.get_low32, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, arg0, arg1]
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, hb.1, hb.2⟩, ?_⟩
      all_goals first | rfl | ext_close
    all_goals ext_close

theorem blk_Lc1c (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc1c" := by
  cfg_block
  measure_hb "Lc1c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    vcgen
    all_goals subst s₀
    all_goals try (to_tableE tableE.match_1.eq_9)
    refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, hm⟩, ?_⟩
    all_goals ext_close

theorem blk_Lc1f (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc1f" := by
  cfg_block
  measure_hb "Lc1f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_15)
    all_goals try (left; apply Table.ofLabels_at; rw [table.match_1.eq_30])
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    case vc6 =>
      simp only [sw32_64, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt] at hm ⊢
      generalize hv : (if CondCode.c.interp _ = true then _ else _ : BitVec 32) = v at hm ⊢
      have hb : v.toNat ≤ X.r.p8.toNat := by subst hv; exact clamp_le _ _ _ _
      refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, hE, ⟨hb, hrb.2⟩, ?_⟩, ?_⟩
      all_goals ext_close
    all_goals refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
    all_goals ext_close

theorem blk_Lcbb (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lcbb" := by
  cfg_block
  measure_hb "Lcbb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    vcgen
    all_goals subst s₀
    left; apply Table.ofLabels_at; rw [table.match_1.eq_30]
    refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, hm⟩, ?_⟩
    all_goals ext_close

theorem blk_Lc7d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc7d" := by
  cfg_block
  measure_hb "Lc7d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals try (to_tableE tableE.match_1.eq_14)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [sw32_64, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, rfl⟩, hrb, ?_⟩, trivial⟩, ?_⟩
    all_goals ext_close

theorem blk_Lc83 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc83" := by
  cfg_block
  measure_hb "Lc83"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hdx⟩, hrb, hm⟩, hsi⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; rw [table.match_1.eq_30])
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [sw32_64, CondCode.interp_l_cmp_toInt32, decide_eq_true_eq, hsi] at hm ⊢
    generalize BitVec.setWidth 32 (Reg64s.get64 _ Reg64.r12) = r at hm ⊢
    generalize hg : BitVec.setWidth 32 (Reg64s.get64 _ Reg64.rdx) = g at hm hrb ⊢
    generalize hv : (g + if r.toInt < (-g).toInt then -g
      else if r.toInt < (X.r.p8 - g).toInt then r else X.r.p8 - g) = v at hm ⊢
    have hb : v.toNat ≤ X.r.p8.toNat := by subst hv; exact sclamp_le _ _ _ hrb.1 hC.2.2.2.1.2.1
    refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, hE, ⟨hb, hrb.2⟩, ?_⟩, ?_⟩
    all_goals ext_close

theorem blk_Lcd3 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lcd3" := by
  cfg_block
  measure_hb "Lcd3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; rw [table.match_1.eq_30])
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [sw32_64, CondCode.interp_l_cmp_toInt32, decide_eq_true_eq,
      BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt] at hm ⊢
    generalize BitVec.setWidth 32 (Reg64s.get64 _ Reg64.r12) = r at hm ⊢
    generalize hv : (gi + if r.toInt < (-gi).toInt then -gi
      else if r.toInt < (X.r.p8 - gi).toInt then r else X.r.p8 - gi) = v at hm ⊢
    have hb : v.toNat ≤ X.r.p8.toNat := by subst hv; exact sclamp_le _ _ _ hrb.1 hC.2.2.2.1.2.1
    refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, hE, ⟨hb, hrb.2⟩, ?_⟩, ?_⟩
    all_goals ext_close

theorem blk_Lc41 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc41" := by
  cfg_block
  measure_hb "Lc41"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hdx⟩, hrb, hm⟩, hsi, hdi⟩, hn⟩ := hs₀
    var_n hn
    vcgen
    all_goals subst s₀
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_12)
    all_goals try (to_tableE tableE.match_1.eq_11)
    case vc3 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, hm⟩, ?_, ?_⟩, ?_⟩
      all_goals first | exact hdx | exact hsi | exact hdi | ext_close
    all_goals refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, hm⟩, ?_⟩
    all_goals ext_close

theorem blk_Lc4b (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc4b" := by
  cfg_block
  measure_hb "Lc4b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hE, hdx⟩, hrb, hm⟩, hsi, hdi⟩, hn⟩ := hs₀
    var_n hn
    have hgi : (BitVec.setWidth 32 (s₀.regs.get64 .rdx)).toNat ≤ X.r.p8.toNat := by
      rw [hdx]; exact hrb.1
    have p_hdx := PLift.up hdx
    clear hdx
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc, shr_cl32_havoc]
    all_goals subst s₀
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_14)
    all_goals try (to_tableE tableE.match_1.eq_12)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off _ _ _ hgi hC.2.2.2.1.2.2.1)
    all_goals have hdx := p_hdx.down; clear p_hdx
    case vc2 =>
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, ⟨hE, ?_⟩, hrb, ?_⟩, ?_⟩, ?_⟩
      all_goals first | exact hdx | exact hsi | ext_close
    case vc3 =>
      refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
      all_goals ext_close

theorem blk_Lca0 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hAv : AvLogSpec Ext kc) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lca0" := by
  cfg_block
  measure_hb "Lca0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    have hl1 : (s₀.dmem.loadInt (t₀.regs.get64 .rdi + 8#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, DecF, AvW, arg0] at hm'
      sep_mem hm'
    have hl2 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 80#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, LocW] at hm'
      sep_mem hm'
    have p_h0 : PLift _ := ⟨hm⟩
    obtain ⟨F, hF⟩ := T_ext kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      simp only [hbp, AddrIndex.offset64_none, add_ofNat0]
      rw [show t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec = t₀.regs.get64 .rsp - 80#64
        from by rw [show (-72 : Int64).toBitVec = -72#64 from rfl]; bv_omega]
      exact hl2
    case vc2 =>
      rename_i x hx
      have hv : x = Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rdi).toInt) := by
        have hmu := p_h0.down
        simp only [T, LocW, arg0] at hmu
        simp only [hbp, AddrIndex.offset64_none, add_ofNat0] at hx
        rw [show t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec = t₀.regs.get64 .rsp - 80#64
          from by rw [show (-72 : Int64).toBitVec = -72#64 from rfl]; bv_omega] at hx
        sep_vals hmu
        first | rfl | (simp only [Option.some.injEq] at hx; exact hx.symm)
      subst hv
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, AddrIndex.offset64_none,
        add_ofNat0]
      rw [show (8 : Int64).toBitVec = 8#64 from rfl]
      exact hl1
    case vc3 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e70]; exact hpush _
      · rw [e70] at hpost
        obtain ⟨hsp', hbp', ⟨-, -, -, h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableE tableE.match_1.eq_16
        refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
        · rw [hsp']; bv_omega
        all_goals try (first | rw [hbp']; exact hbp | rw [h14']; exact h14)
        · exact (congrFun hF s'.dmem).mpr hm'
        · rw [var_Lcbb]; omega

theorem blk_Lc67 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hReq : AvReqSpec Ext kc) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lc67" := by
  cfg_block
  measure_hb "Lc67"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    have hl1 : (s₀.dmem.loadInt (t₀.regs.get64 .rdi + 8#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, DecF, AvW, arg0] at hm'
      sep_mem hm'
    have hl2 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 80#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, LocW] at hm'
      sep_mem hm'
    have p_h0 : PLift _ := ⟨hm⟩
    obtain ⟨F, hF⟩ := T_ext kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "avpriv_request_sample" hReq]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      simp only [hbp, AddrIndex.offset64_none, add_ofNat0]
      rw [show t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec = t₀.regs.get64 .rsp - 80#64
        from by rw [show (-72 : Int64).toBitVec = -72#64 from rfl]; bv_omega]
      exact hl2
    case vc2 =>
      rename_i x hx
      have hv : x = Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rdi).toInt) := by
        have hmu := p_h0.down
        simp only [T, LocW, arg0] at hmu
        simp only [hbp, AddrIndex.offset64_none, add_ofNat0] at hx
        rw [show t₀.regs.get64 .rsp - 8#64 + (-72 : Int64).toBitVec = t₀.regs.get64 .rsp - 80#64
          from by rw [show (-72 : Int64).toBitVec = -72#64 from rfl]; bv_omega] at hx
        sep_vals hmu
        first | rfl | (simp only [Option.some.injEq] at hx; exact hx.symm)
      subst hv
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, AddrIndex.offset64_none,
        add_ofNat0]
      rw [show (8 : Int64).toBitVec = 8#64 from rfl]
      exact hl1
    case vc3 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e70]; exact hpush _
      · rw [e70] at hpost
        obtain ⟨hsp', hbp', ⟨-, -, -, h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableE tableE.match_1.eq_13
        refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
        · rw [hsp']; bv_omega
        all_goals try (first | rw [hbp']; exact hbp | rw [h14']; exact h14)
        · exact (congrFun hF s'.dmem).mpr hm'
        · rw [var_Lc7d]; omega

theorem blk_Lcc0 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hAv : AvLogSpec Ext kc) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lcc0" := by
  cfg_block
  measure_hb "Lcc0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    obtain ⟨F, hF⟩ := T_ext kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e70]; exact hpush _
      · rw [e70] at hpost
        obtain ⟨hsp', hbp', ⟨-, -, -, h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableE tableE.match_1.eq_18
        refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
        · rw [hsp']; bv_omega
        all_goals try (first | rw [hbp']; exact hbp | rw [h14']; exact h14)
        · exact (congrFun hF s'.dmem).mpr hm'
        · rw [var_Lcd3]; omega

end Kraken.Examples.Sbr.DecExt
