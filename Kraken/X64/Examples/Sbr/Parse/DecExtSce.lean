import Kraken.X64.Examples.Sbr.Parse.DecExtDat

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the single channel element (`L349`)

The inlined `if (get_bits1(gb)) skip_bits(gb, 4)` (`bs_data_extra`, `bs_reserved`): the reader's
index moves by one, or by five clamped to `size_in_bits_plus8`; the bit itself is not kept.

Then `L384` (the `read_sbr_grid` call on `data[0]`) and `L39d` (the `read_sbr_dtdf` call; on a
nonzero grid result the jump to `L48b`).
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem idA_ne1 {t₀ : MachineData} (hz : idA t₀ &&& 0xfffffffd#32 = 0#32) : idA t₀ ≠ 1#32 := by
  intro h; rw [h] at hz; exact absurd hz (by decide)

omit [CodeEnv] in
/-- `lea (%r8,%r9,1)` after `setl %r9b`: `setl_inc` with a 64-bit add truncated. -/
theorem setl_inc64 (r : BitVec 64) (p x : BitVec 32) (cf af : Bool)
    (ha : (r.setWidth 32).toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (BitVec.setWidth 32 (r + (BitVec.setWidth 64 (x ^^^ x)).replaceLow
      (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (r.setWidth 32 - p)
        { cf := cf, af := af,
          of := (r.setWidth 32 - p).signed != (r.setWidth 32).signed - p.signed })).toNat))).toNat
      ≤ p.toNat := by
  have e : ∀ y : BitVec 64, BitVec.setWidth 32 (r + y) = r.setWidth 32 + BitVec.setWidth 32 y :=
    fun y => by bv_omega
  rw [e]; exact setl_inc _ _ _ _ _ ha hp

omit [CodeEnv] in
/-- `cmp; cmovb`: `min(y, p)`. -/
theorem clamp_le (p y : BitVec 32) (af o : Bool) :
    (if CondCode.c.interp (StatusFlags.from_result (p - y)
        { cf := (p - y).unsigned != p.unsigned - y.unsigned, af := af, of := o }) = true
      then p else y).toNat ≤ p.toNat := by
  rw [interp_c_sub32]
  split
  · exact Nat.le_refl _
  · rename_i h; simp only [decide_eq_true_eq] at h; omega

theorem blk_L349 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L349" := by
  cfg_block
  measure_hb "L349"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hS, hr8⟩, hrb, hm⟩, hsi, h12, hz⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, LocW, GbR, GbW] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have hgi : (BitVec.setWidth 32 (s₀.regs.get64 .r8)).toNat ≤ X.r.p8.toNat := by
      rw [hr8]; exact hrb.1
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, hsi, DecF]
    dx_br hm
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Width.bytes,
      BitVec.mul_one] at *
    case vc3 =>
      sep_mem hm
      rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
      exact rd_off1 _ _ _ hgi hC.2.2.2.1.2.2.1
    case vc5 =>
      generalize hv : (if CondCode.ns.interp _ = true then _ else _ : BitVec 32) = v at hm ⊢
      have hb : v.toNat ≤ X.r.p8.toNat := by
        subst hv
        split
        · exact setl_inc64 _ _ _ _ _ hgi hC.2.2.2.1.2.1
        · exact clamp_le _ _ _ _
      refine ⟨⟨⟨hC, ⟨trivial, trivial, trivial⟩, i0, v, d, ih, hS, ⟨hb, hrb.2⟩, ?_⟩, ?_, ?_,
        idA_ne1 hz⟩, ?_⟩
      all_goals first
        | exact Nat.le_of_eq (var_L384 _)
        | exact trivial
        | sep_close hm

/-- The caller's part of the memory at a call in `read_sbr_data` (`gbc` at `rbp - 0x40`): the
other locals `LocW`, `*gb_host`, the `ac` fields, the saved registers and the caller's rest. -/
def GRW (X : XA) (ra : Int64) (t₀ : MachineData) (d : DS) (i0 : BitVec 64) (ih : BitVec 32) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  (8 ?@ (r - 0x68#64) ⋆ (Apply.c8 (r - 0x60#64) i0 ⋆ (Apply.c8 (r - 0x58#64) (arg4 t₀)
    ⋆ (Apply.c8 (r - 0x50#64) (arg0 t₀) ⋆ 4 ?@ (r - 0x34#64)))))
  ⋆ (GhW (arg2 t₀) X ih ⋆ (AcF (arg0 t₀) d.a X.sr ⋆ Saved t₀ (Rest X.R ra t₀)))

/-- The callee's logical variable at a call in `read_sbr_data`. -/
abbrev cD (X : XA) (ra : Int64) (t₀ : MachineData) (d : DS) (i0 : BitVec 64) (gi ih : BitVec 32) :
    CA :=
  ⟨GRW X ra t₀ d i0 ih, d, sbrA t₀, arg0 t₀, t₀.regs.get64 .rsp - 0x48#64, X.r, gi⟩

theorem T_dat (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ : MachineData)
    (d : DS) (i0 : BitVec 64) (gi ih : BitVec 32) :
    T kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih =
      8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ (CF Ext (cD X ra t₀ d i0 gi ih) d gi ⋆ GRW X ra t₀ d i0 ih)) := by
  let r := t₀.regs.get64 .rsp
  exact congrArg (fun H => 8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ H))
    (perm14 (8 ?@ (r - 0x68#64)) (Apply.c8 (r - 0x60#64) i0) (Apply.c8 (r - 0x58#64) (arg4 t₀))
      (Apply.c8 (r - 0x50#64) (arg0 t₀)) (GbR (r - 0x48#64) X.r gi) (4 ?@ (r - 0x34#64))
      (SbrF d (sbrA t₀)) (GhW (arg2 t₀) X ih) (AvW (arg0 t₀) d.a) (AcF (arg0 t₀) d.a X.sr)
      (BufW X.r) Grid.JtW Ext (Saved t₀ (Rest X.R ra t₀)))

omit [CodeEnv] in
theorem setCh_false (d : DS) (v : DV) : d.setCh false v = { d with a := { d.a with d0 := v } } :=
  rfl

omit [CodeEnv] in
/-- After `read_sbr_grid` on `data[0]`: `TInv`, and `EInv` on success (`id_aac ≠ 1`: only
`data[0]` must be live). -/
theorem grid_inv {PI : List UInt8 → Prop} {X : XA} {t₀ : MachineData} {d : DS}
    {n nn : Nat} {fr te tq : List UInt8} {ret : BitVec 32} (hS : SInv PI X t₀ d)
    (hid : idA t₀ ≠ 1#32)
    (hok : (d.setCh false (dvGrid d.a.d0 n fr nn te tq)).ok)
    (hxk : XKeep d.a (d.setCh false (dvGrid d.a.d0 n fr nn te tq)).a)
    (hG : GridV (dvGrid d.a.d0 n fr nn te tq) ret) :
    TInv PI X (d.setCh false (dvGrid d.a.d0 n fr nn te tq))
      ∧ (ret = 0#32 → EInv PI X (d.setCh false (dvGrid d.a.d0 n fr nn te tq))) := by
  rw [setCh_false] at hok hxk ⊢
  obtain ⟨⟨⟨⟨a1, a2, -, a4, a5, a6⟩, i1⟩, -, hP, hK, hsi⟩, -, hidA⟩ := hS
  have hA : AI { d.a with d0 := dvGrid d.a.d0 n fr nn te tq } :=
    ⟨a1, a2, hG.1, a4, a5, ⟨hG.2.1, a6.2⟩⟩
  refine ⟨⟨hA, hok, hP, xkeep_trans hK hxk, hsi⟩, fun h0 => ⟨⟨hA, i1⟩, ⟨fun _ => hG.2.2.2 h0,
    fun h => absurd (hidA.symm.trans h.2) hid⟩, hok, hP, xkeep_trans hK hxk, hsi⟩⟩

theorem blk_L384 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hG : GridSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L384" := by
  cfg_block
  measure_hb "L384"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hS, hrb, hm⟩, hsi, h12, hid⟩, hn⟩ := hs₀
    var_n hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [call_procS_spec_at ((cD X ra t₀ d i0 gi ih), false) "read_sbr_grid" hG.toS]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hS.1.2.1⟩, ?_, ?_, ?_, ?_, hS.1.1.1.2.2.1,
      hS.1.1.1.2.2.2.2.2.1⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inl ha)), hld⟩
    · rw [e70]; exact hpush _
    · exact h12
    · exact hsi
    · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
    · rw [h14, show Int64.toBitVec 166304 = 166304#64 from rfl]; bv_omega
    · obtain ⟨d', i', ⟨n', fr, nn, te, tq, rfl, hGV⟩, hok, hxk, hi', hsp', hbp',
        ⟨-, h12', h13', h14', -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih,
        grid_inv (n := n') (fr := fr) (nn := nn) (te := te) (tq := tq) hS hid hok hxk hGV,
        ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_⟩, Nat.le_of_eq (var_L39d _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [DecF, GRW, setCh_false, AcF] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact hsi
      · rw [h13', h14, show Int64.toBitVec 166304 = 166304#64 from rfl]; bv_omega

omit [CodeEnv] in
theorem sub8_m64 (x : BitVec 64) : x - 8#64 + (-64 : Int64).toBitVec = x - 72#64 := by
  rw [show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega

theorem blk_L39d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hD : DtdfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L39d" := by
  cfg_block
  measure_hb "L39d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hT, hE⟩, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_n hn
    have p_h0 : PLift _ := ⟨hm⟩
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_dtdf" hD]
    all_goals try call_simp
    all_goals try subst_vars
    case vc3 =>
      rename_i v hx _
      have hv : v = Int.ofBytes (Int.toBytes 4 d.usac.toInt) := by
        have hmu := p_h0.down
        simp only [DecF, SbrF, SbrS, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hmu
        simp only [h14, Int64.toBitVec_ofNat_norm] at hx
        sep_vals hmu
        rfl
      subst hv
      rename_i _ hz _
      have hE' := hE (by
        simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self,
          Bool.not_eq_false', beq_iff_eq] at hz
        exact hz)
      have D0 := hT.1.2.2.1
      have D1 := hT.1.2.2.2.1
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hT.2.1⟩, ?_, ?_, Or.inl h13, ?_,
        D0.2.2.2.2.1, D0.2.2.2.2.2.2.1, D1.2.2.2.2.1, D1.2.2.2.2.2.2.1⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, BitVec.setWidth_32_64_32]
      · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
      · simp only [BitVec.xor_self, BitVec.setWidth_zero]
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE', ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_, ?_⟩,
          Nat.le_of_eq (var_L3bd _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [h13']; exact h13
        · rw [hbx', hbp]; exact sub8_m64 _
    case vc1 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc2 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, SbrS, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, Int64.toBitVec_ofNat_norm]
      sep_mem hmu

omit [CodeEnv] in
theorem invf0_eq (d : DS) (vals : Nat → Nat) :
    d.invf 0 vals = { d with a := { d.a with d0 := invfRead d.a.nq d.a.d0 vals } } := rfl

omit [CodeEnv] in
/-- `read_sbr_invf` on `data[0]` keeps `EInv`. -/
theorem einv_invf0 {PI : List UInt8 → Prop} {X : XA} {d : DS} {vals : Nat → Nat}
    (hE : EInv PI X d) (hok : (d.invf 0 vals).ok) (hxk : XKeep d.a (d.invf 0 vals).a) :
    EInv PI X (d.invf 0 vals) := by
  rw [invf0_eq] at hok hxk ⊢
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩, ⟨l0, l1⟩, -, hP, hK, hsi⟩ := hE
  exact ⟨⟨⟨a1, a2, dwf_invfRead a3, a4, a5, a6⟩, i1⟩, ⟨fun h => live_invfRead (l0 h), l1⟩, hok,
    hP, xkeep_trans hK hxk, hsi⟩

theorem blk_L3bd (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hI : InvfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L3bd" := by
  cfg_block
  measure_hb "L3bd"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_n hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hq := hE.1.1.1.2.2.2.2.2.2.2.2.2.1
    have hl0 := hE.1.1.2.2.1.2.1
    have hl1 := hE.1.1.2.2.2.1.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_invf" hI]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, ?_, Or.inl ?_, hq, hl0, hl1⟩,
      fun s' hpost => ?_⟩, hld⟩
    · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
    · exact h12
    · exact hbx
    · exact h13
    · obtain ⟨d', i', ⟨vals, hd'⟩, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ :=
        hpost
      simp only [h13, ↓reduceIte] at hd'
      subst hd'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, einv_invf0 hE hok hxk, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_,
        ?_⟩, Nat.le_of_eq (var_L3cb _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [DecF, GRW, invf0_eq, AcF] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · rw [hbx']; exact hbx

omit [CodeEnv] in
theorem sub8_m72 (x : BitVec 64) : x - 8#64 + 0 + (-72 : Int64).toBitVec = x - 80#64 := by
  rw [show (-72 : Int64).toBitVec = -72#64 from rfl]; bv_omega

theorem blk_L3cb (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hV : EnvSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L3cb" := by
  cfg_block
  measure_hb "L3cb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_n hn
    rw [T_dat] at hm
    have p_h0 : PLift _ := ⟨hm⟩
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    have hA : ∀ r, s₀.regs.get64 .rbp + AddrIndex.offset64 none r + (-72 : Int64).toBitVec
        = t₀.regs.get64 .rsp - 80#64 := by
      intro r; rw [AddrIndex.offset64_none, hbp]; exact sub8_m72 _
    have hLs : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 80#64) 8).isSome = true := by
      have h := hm
      simp only [CF, GRW, arg0] at h
      sep_mem h
    clear hm
    have hal : (sbrA t₀).toNat % 32 = 0 := by
      have h := hC.2.2.2.2.2.2.2.2.1
      simp only [isAligned, beq_iff_eq] at h
      exact h
    have D0 := hE.1.1.2.2.1
    have D1 := hE.1.1.2.2.2.1
    have hn0 := hE.1.1.1.2.2.2.2.2.2.2.1
    have hn1 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    vcgen [call_procS_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_envelope" hV]
    all_goals try call_simp
    case vc1 =>
      rename_i hs; subst hs
      rw [hA]; exact hLs
    case vc2 =>
      rename_i hs _ _ _; subst hs
      rw [hA]; exact hLs
    case vc3 =>
      rename_i hs v1 hx1 v2 _ hx2
      subst hs
      rw [hA] at hx1 hx2
      have hv1 : v1 = Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rdi).toInt) := by
        have hmu := p_h0.down
        simp only [CF, GRW, arg0] at hmu
        sep_vals hmu
        rfl
      have hv2 : v2 = Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rdi).toInt) := by
        have hmu := p_h0.down
        simp only [CF, GRW, arg0] at hmu
        sep_vals hmu
        rfl
      subst hv1 hv2
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, h12, hbx, Or.inl h13, D0, D1,
        hn0, hn1, hal⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inr ha)), hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_, ?_⟩,
          Nat.le_of_eq (var_L3e4 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [h13']; exact h13
        · rw [hbx']; simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

end Kraken.Examples.Sbr.DecExt
