import Kraken.X64.Examples.Sbr.Parse.DecExtExt

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the extension-id loop (`read_sbr_extension`)

`Lb9d` reads `bs_extension_id`, `Lbd4` tests `ps` (else the log at `Lcc0`), `Lbe6` calls
`ff_ps_read_data` (`PsSpec`), `Lbf5` subtracts its result from the bit count and stores the profile
and `ps.start`, then loops back to `Lb9d` while more than 7 bits are left.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- `lea -0x2(%rax),%r12d` with `eax ≥ 8`. -/
theorem sub2_toNat (x : BitVec 64) (h : 8 ≤ (x.setWidth 32).toNat) :
    (BitVec.setWidth 32 (x + 18446744073709551614#64)).toNat = (x.setWidth 32).toNat - 2 := by
  bv_omega

theorem blk_Lb9d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lb9d" := by
  cfg_block
  measure_hb "Lb9d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hbx, h13, hlo, hhi⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [bswap32_havoc, shl_cl32_havoc]
    all_goals subst s₀
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_10)
    all_goals try (to_tableE tableE.match_1.eq_5)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one, sw32_64,
      BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    case vc3 =>
      sep_mem hm
      rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
      exact rd_off _ _ _ hrb.1 hC.2.2.2.1.2.2.1
    all_goals generalize hv : (if CondCode.c.interp _ = true then _ else _ : BitVec 32) = v at hm ⊢
    all_goals have hb : v.toNat ≤ X.r.p8.toNat := by subst hv; exact clamp_le _ _ _ _
    case vc6 =>
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, ⟨hE, ?_⟩, ⟨hb, hrb.2⟩, ?_⟩, ?_, ?_⟩, ?_⟩
      all_goals first
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]; done)
        | ext_close
    case vc7 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, v, d, ih, hE, ⟨hb, hrb.2⟩, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64,
        arg0, arg1, hbx, h13, hsp, hbp, h14]; done)
      all_goals try (rw [sub2_toNat _ hlo]; omega)
      case refine_9 =>
        rw [var_Lbd4]
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
        rw [sub2_toNat _ hlo]; omega
      ext_close

theorem blk_Lbd4 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lbd4" := by
  cfg_block
  measure_hb "Lbd4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hbx, h13, hlo, hhi⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, AcF, AvW, arg0, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_17)
    all_goals try (to_tableE tableE.match_1.eq_6)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h13, BitVec.add_assoc, BitVec.reduceAdd]
    case vc3 =>
      refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
      all_goals first
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hsp, hbp, h14]; done)
        | (simp only [T, DecF, AcF, AvW, arg0, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
        | ext_close
    case vc4 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals first
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hsp, hbp, h14, hbx,
            h13, arg0, arg1]; done)
        | (simp only [T, DecF, AcF, AvW, arg0, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
        | ((try rw [var_Lbe6]); (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true,
            ite_false]); omega)

/-- The caller's part of the memory at the call of `ff_ps_read_data`: all of `T` but
`ps->common`, the reader `gbc`, the buffer and `Ext`. -/
abbrev PsR (X : XA) (ra : Int64) (t₀ : MachineData) (FR : (Mem 64 → Prop) → Mem 64 → Prop)
    (i0 : BitVec 64) (d : DS) (ih : BitVec 32) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  (8 ?@ (r - 0x68#64) ⋆ (Apply.c8 (r - 0x60#64) i0 ⋆ (Apply.c8 (r - 0x58#64) (arg4 t₀)
    ⋆ (Apply.c8 (r - 0x50#64) (arg0 t₀) ⋆ 4 ?@ (r - 0x34#64)))))
  ⋆ ((SbrS d (sbrA t₀) ⋆ (DataF d.a.d0 (sbrA t₀ + 0x80#64) ⋆ (DataF d.a.d1 (sbrA t₀ + 0x15b40#64)
    ⋆ TabF d.a (sbrA t₀))))
  ⋆ (GhW (arg2 t₀) X ih ⋆ (AvW (arg0 t₀) d.a ⋆ (AcF (arg0 t₀) d.a X.sr
    ⋆ (Grid.JtW ⋆ FR (Rest X.R ra t₀))))))

omit [CodeEnv] in
theorem permPs (a1 a2 a3 a4 g a5 S D0 D1 P Tb Gh Av Ac Bf Jt E Sv : Mem 64 → Prop) :
    (a1 ⋆ (a2 ⋆ (a3 ⋆ (a4 ⋆ (g ⋆ a5)))))
      ⋆ (((S ⋆ (D0 ⋆ (D1 ⋆ (P ⋆ Tb)))) ⋆ (Gh ⋆ (Av ⋆ (Ac ⋆ (Bf ⋆ (Jt ⋆ E)))))) ⋆ Sv)
    = (P ⋆ (g ⋆ (Bf ⋆ E))) ⋆ ((a1 ⋆ (a2 ⋆ (a3 ⋆ (a4 ⋆ a5))))
      ⋆ ((S ⋆ (D0 ⋆ (D1 ⋆ Tb))) ⋆ (Gh ⋆ (Av ⋆ (Ac ⋆ (Jt ⋆ Sv)))))) := by
  ac_rfl

theorem T_ps (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (i0 : BitVec 64) (gi : BitVec 32) (d : DS)
    (ih : BitVec 32) :
    T kc Ext X ra t₀ FR (LocW X t₀ i0 gi) d ih =
      8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ ((d.a.psc =@ (sbrA t₀ + 0x2b600#64) ⋆ (GbR (t₀.regs.get64 .rsp - 0x48#64) X.r gi
          ⋆ (BufW X.r ⋆ Ext))) ⋆ PsR X ra t₀ FR i0 d ih)) := by
  let r := t₀.regs.get64 .rsp
  exact congrArg (fun H => 8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ H))
    (permPs (8 ?@ (r - 0x68#64)) (Apply.c8 (r - 0x60#64) i0) (Apply.c8 (r - 0x58#64) (arg4 t₀))
      (Apply.c8 (r - 0x50#64) (arg0 t₀)) (GbR (r - 0x48#64) X.r gi) (4 ?@ (r - 0x34#64))
      (SbrS d (sbrA t₀)) (DataF d.a.d0 (sbrA t₀ + 0x80#64)) (DataF d.a.d1 (sbrA t₀ + 0x15b40#64))
      (d.a.psc =@ (sbrA t₀ + 0x2b600#64)) (TabF d.a (sbrA t₀))
      (GhW (arg2 t₀) X ih) (AvW (arg0 t₀) d.a) (AcF (arg0 t₀) d.a X.sr)
      (BufW X.r) Grid.JtW Ext (FR (Rest X.R ra t₀)))

omit [CodeEnv] in
/-- `EInv` with `ps->common` replaced by the result of `ff_ps_read_data`. -/
theorem einv_psc {PI : List UInt8 → Prop} {X : XA} {d : DS} {c : List UInt8} (h : EInv PI X d)
    (hw : ∀ h, PsWF d.a.psc h → PsWF c h) (hl : c.length = 764) (hp : PI c) :
    EInv PI X { d with a := { d.a with psc := c } } := by
  unfold EInv MI AI DS.ok Lens at h ⊢
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩, hL, ⟨o1, o2, o3, l1, l2, l3, l4, l5, l6, -⟩, -, hx, hsi⟩ :=
    h
  exact ⟨⟨⟨a1, a2, a3, a4, hw _ a5, a6⟩, i1⟩, hL, ⟨o1, o2, o3, l1, l2, l3, l4, l5, l6, hl⟩, hp, hx,
    hsi⟩

omit [CodeEnv] in
theorem sub112_add8 (t : BitVec 64) : t - 112#64 + 8#64 = t - 104#64 := by bv_omega

theorem blk_Lbe6 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hPs : PsSpec PI kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lbe6" := by
  cfg_block
  measure_hb "Lbe6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hbx, h13, hlo, hhi⟩, hn⟩ := hs₀
    var_n hn
    rw [T_ps] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at
      (⟨PsR X ra t₀ (Saved t₀) i0 d ih, d.a.psc, t₀.regs.get64 .rsp - 0x48#64, X.r, gi⟩ : PA)
      "ff_ps_read_data" hPs]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    have hA : t₀.regs.get64 .rsi + 343840#64 = sbrA t₀ + 177664#64 := by
      simp only [sbrA, arg1]; bv_omega
    refine ⟨fun ra' => ⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2.1, hC.2.2.2.1.2.2.1, hC.2.2.2.1.2.2.2⟩, ?_,
      hE.2.2.1.2.2.2.2.2.2.2.2.2, hE.2.2.2.1, ?_⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e70, hbx, hA]; exact hpush _
    · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
    · simp only [sw32_64]; rw [BitVec.toInt_eq_toNat_cond]; split <;> omega
    · obtain ⟨c', i', hw, hl, hp, hi, h0, hle, hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
      rw [e70, hbx, hA] at hm'
      simp only [sw32_64] at hle
      refine MachineWP.nil_spec.le_wp s' ?_
      to_tableE tableE.match_1.eq_7
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', { d with a := { d.a with psc := c' } }, ih,
        einv_psc hE hw hl hp, ⟨hi, hrb.2⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hsp', e70]
        exact sub112_add8 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [T_ps]; exact hm'
      · rw [hbx', hbx]
      · rw [h13', h13]
      · rw [h12']; exact hlo
      · rw [h12']; exact hhi
      · exact h0
      · rw [h12']; exact hle
      · rw [var_Lbf5, h12']; omega

omit [CodeEnv] in
/-- `sub %eax,%r12d` with `0 ≤ eax ≤ r12d ≤ 2158` (signed). -/
theorem subr_toNat (a b : BitVec 32) (h1 : a.toNat ≤ 2158) (h0 : 0 ≤ b.toInt)
    (hle : b.toInt ≤ a.toInt) :
    b.toNat ≤ a.toNat ∧ (a - b).toNat = a.toNat - b.toNat
      ∧ (a - b).toInt = ((a.toNat - b.toNat : Nat) : Int) := by
  have ha : a.toInt = a.toNat := by
    have e := BitVec.toInt_eq_toNat_cond a; split at e <;> omega
  have hb : b.toInt = b.toNat := by
    have e := BitVec.toInt_eq_toNat_cond b; split at e <;> omega
  have hs : (a - b).toNat = a.toNat - b.toNat := by rw [BitVec.toNat_sub]; omega
  refine ⟨by omega, hs, ?_⟩
  rw [BitVec.toInt_eq_toNat_cond, hs]; split <;> omega

theorem blk_Lbf5 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lbf5" := by
  cfg_block
  measure_hb "Lbf5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hbx, h13, hlo, hhi, h0, hle⟩, hn⟩ :=
      hs₀
    var_n hn
    simp only [T, DecF, AcF, AvW, arg0, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, Int64.toBitVec_ofNat_norm,
      BitVec.reduceToNat, Nat.reduceMod, ite_true, ite_false] at *
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_4)
    all_goals try (left; apply Table.ofLabels_at; to_tableE tableE.match_1.eq_9)
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h13, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one, Nat.mul_one, sw32_64,
      BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt] at *
    dx_run hm [hbp, hsp, h14, h13, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [sw32_64, CondCode.interp_g_cmp_toInt32, decide_eq_true_eq,
      Bool.not_eq_true, decide_eq_false_iff_not] at *
    all_goals obtain ⟨hab, hs, hi⟩ := subr_toNat _ _ hhi h0 hle
    case vc4 =>
      rename_i hc
      simp only [BitVec.reduceSetWidth, BitVec.reduceToInt, hi] at hc
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
      all_goals first
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hsp, hbp, h14, hbx,
            h13, arg0, arg1]; done)
        | (simp only [T, DecF, AcF, AvW, arg0, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
        | ((try rw [var_Lb9d]); simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
            sw32_64, hs]; omega)
    case vc5 =>
      refine ⟨by decide, ⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_⟩
      all_goals first
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hsp, hbp, h14]; done)
        | (simp only [T, DecF, AcF, AvW, arg0, BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
        | (rw [var_Lc1f]; omega)

end Kraken.Examples.Sbr.DecExt
