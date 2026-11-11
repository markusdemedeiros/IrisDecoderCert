import Kraken.X64.Examples.Sbr.Parse.PsBlkT2Lib
import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib
import Kraken.X64.Examples.Sbr.Parse.LibCall
import Kraken.X64.Examples.Sbr.Parse.PsBlkHLib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem t2L_rng0 {c : List UInt8} (h : PsWFb c) : Rng0 c := ⟨h.2.1, h.2.2.2.2.1⟩

set_option maxRecDepth 20000 in
/-- `r8d = index - index₀`; more than `bits_left`: `av_log`, then the error path `0x1479`. -/
theorem blk_L1404 (k : Nat) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1404" := by
  cfg_block
  measure_hb "L1404"
    intro n
    simp only [tab_L1404, var_L1404, tab_L142f, var_L142f]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, h15, hW⟩, hI, hbx⟩, hn⟩ := hs₀
    have L14 := t2_fload ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩ (18446744073709551476#64) 0x8c 4 rfl
      (by omega) (by omega) (by omega)
    have L40 := t2_fload ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩ (18446744073709551552#64) 64 8 rfl
      (by omega) (by omega) (by omega)
    have e1 : s₀.regs.get64 .rbp + Int64.toBitVec (-64)
        = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x60 := by
      rw [hbp]; exact fr_addr _ 64 (by omega) (by omega)
    obtain ⟨F, hF⟩ := hn_Fr_ext k Ext x ra t₀ f c x.idx
    have hm2 := hm
    rw [hF] at hm2
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm2 (by simp)
    have hpush := fun v => Block.storeInt_val hm2 (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0xb0#64 := by
      rw [hsp]; show _ - 168#64 - 8#64 = _; rw [BitVec.sub_sub_ofNat]
    clear hm2
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    pnorm at e1
    case vc1 =>
      t1norm
      rw [L14]; rfl
    case vc2 =>
      rename_i v hv hle
      t1norm at hv hle
      rw [L14, Option.some.injEq] at hv
      subst hv
      rw [CondCode.interp_le_cmp_toInt32, decide_eq_true_eq] at hle
      t1_jump "ff_ps_read_data.L142f"
      have hC' := hC
      obtain ⟨-, -, hip, hp31, -, -, -⟩ := hC'
      refine ⟨c, f, ⟨⟨hC, ⟨by t1r; exact hsp, by t1r; exact hbp, hf, hP, hbl, h08, hid⟩, hm⟩,
        by t1r; exact h15, hW⟩, ?_, ?_⟩
      · t1r
        rw [t2_sw3264, hid]
        have := x.idx.isLt
        rw [BitVec.toNat_sub, BitVec.toNat_setWidth]; omega
      · t1r
        rw [t2_sw3264]
        rw [t2_sw3264] at hle
        rw [h15] at hle; exact hle
    case vc3 =>
      pnorm
      rw [L40]; rfl
    case vc4 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e48]; exact hpush _
      · rw [e48] at hpost
        obtain ⟨hsp', hbp', ⟨hbx', -, -, -, h15'⟩, hm'⟩ := hpost
        have hm'' : s'.dmem =⋆ Fr k Ext x ra t₀ f c x.idx := (congrFun hF s'.dmem).mpr hm'
        vcgen
        all_goals try call_simp
        all_goals try dsimp only at *
        all_goals try t1norm at *
        t1_jump "ff_ps_read_data.L1479"
        refine ⟨⟨c, f, ⟨hC, ⟨?_, by (try t1r); rw [hbp', hbp], hf, hP, hbl, h08, hid⟩, hm''⟩,
          ?_, fun hp => t2L_rng0 (hW hp)⟩, ?_⟩
        · (try t1r)
          rw [hsp', BitVec.sub_add_ofNat_cancel _ _ _ (by omega) (by omega)]
        · (try t1r); rw [hbx']; first | exact hbx | (t1r; exact hbx)
        · (try t1r); rw [h15']; first | exact h15 | (t1r; exact h15)

omit [CodeEnv] in
theorem t2L_tb0 : ∀ n : Nat, Int.toBytes n 0 = List.replicate n 0
  | 0 => rfl
  | n + 1 => by
    simp only [Int.toBytes, Int.zero_ediv, List.replicate_succ, t2L_tb0 n, List.cons.injEq, and_true]
    rfl

omit [CodeEnv] in
theorem t2L_i8z {c : List UInt8} (hl : c.length = 764) (j : Nat) (h1 : 76 ≤ j) (h2 : j < 756) :
    i8 (wr c 76 680 0) j = 0 := by
  simp only [i8]
  rw [t1_getD_wr c 76 680 j _ (by omega), if_pos ⟨h1, by omega⟩, t1_toBytes_zero_getD]
  rfl

omit [CodeEnv] in
theorem t2L_wf {c : List UInt8} (hl : c.length = 764) (hP : PsInv c) (hc0 : i32 c 0 = 0)
    (hR : Rng0 c) : PsWFb (wr c 76 680 0) := by
  obtain ⟨-, -, -, -, h40, h44, h8⟩ := hP
  obtain ⟨h756, -⟩ := hR
  refine ⟨by rw [wr_length _ _ _ _ (by omega), hl], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [i32_wr]; exact h756
  · simp (disch := omega) only [i32_wr]; exact h44
  · simp (disch := omega) only [i32_wr]; exact h40
  · simp (disch := omega) only [i32_wr]; exact h8
  · intro e he b hb
    rw [t2L_i8z hl _ (by omega) (by omega)]; decide
  · intro e he b hb
    rw [t2L_i8z hl _ (by omega) (by omega), t2L_i8z hl (586 + 34 * e + b) (by omega) (by omega)]
    decide
  · intro h0
    exfalso; apply h0
    simp (disch := omega) only [i32_wr]; exact hc0

omit [CodeEnv] in
theorem t2L_ib (a d r idx p8 : BitVec 32) (q : Prop) [Decidable q] (ha : a = idx)
    (hd : d = 0#32 - idx) (hr : r.toNat ≤ p8.toNat - idx.toNat) (hp : idx.toNat ≤ p8.toNat)
    (hp31 : p8.toNat < 2 ^ 31) : (a + if q then d else r).toNat ≤ p8.toNat := by
  subst ha hd
  split
  · bv_omega
  · rw [BitVec.toNat_add]; omega

omit [CodeEnv] in
theorem t2L_mono3 {A B C R R' : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ A ⋆ (B ⋆ (C ⋆ R)))
    (hR : ∀ m', R m' → R' m') : m =⋆ A ⋆ (B ⋆ (C ⋆ R')) := by
  obtain ⟨m1, m2, hu, hi, h1, m3, m4, hu2, hi2, h3, m5, m6, hu3, hi3, h5, h6⟩ := h
  exact ⟨m1, m2, hu, hi, h1, m3, m4, hu2, hi2, h3, m5, m6, hu3, hi3, h5, hR _ h6⟩

omit [CodeEnv] in
theorem t2L_ex3 {A B C : Mem 64 → Prop} {P : BitVec 32 → Prop} {G : BitVec 32 → Mem 64 → Prop}
    {m : Mem 64} (h : m =⋆ A ⋆ (B ⋆ (C ⋆ (fun m => ∃ i, P i ∧ G i m)))) :
    ∃ i, P i ∧ (m =⋆ A ⋆ (B ⋆ (C ⋆ G i))) := by
  obtain ⟨m1, m2, hu, hi, h1, m3, m4, hu2, hi2, h3, m5, m6, hu3, hi3, h5, i, hp, hg⟩ := h
  exact ⟨i, hp, m1, m2, hu, hi, h1, m3, m4, hu2, hi2, h3, m5, m6, hu3, hi3, h5, hg⟩

omit [CodeEnv] in
theorem t2L_val_app3 (a b c : List UInt8) (p : BitVec 64)
    (h : a.length + b.length + c.length ≤ 2 ^ 64) :
    (a ++ b ++ c) =@ p = a =@ p ⋆ (b =@ (p + BitVec.ofNat 64 a.length)
      ⋆ c =@ (p + BitVec.ofNat 64 a.length + BitVec.ofNat 64 b.length)) := by
  rw [Val.eq, Val.eq, Val.eq, Val.eq, List.append_assoc,
    At_append_sep a (b ++ c) _ (by simp only [List.length_append]; omega),
    At_append_sep b c _ (by omega)]

/-- The rest of the frame around the `memset` of `[0x4c, 0x2f4)` of `*ps`. -/
abbrev t2L_MsR (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f c : List UInt8) (i : BitVec 32) : Mem 64 → Prop :=
  (c.take 76 =@ arg2 t₀ ⋆ c.drop 756 =@ (arg2 t₀ + 76#64 + BitVec.ofNat 64 680))
  ⋆ (f =@ (rsp0 t₀ - 0xa8#64) ⋆ (Sv t₀ ⋆ ((GbW (arg1 t₀) x i ⋆ (Blocks [(x.buf, x.L)]
      ⋆ (PsTabs x.v ⋆ Ext))) ⋆ (RetCell ra (rsp0 t₀) ⋆ x.R))))

theorem t2L_idx {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (v : BitVec 32) : m.storeInt (arg1 t₀ + 8#64) 4 v.toInt =⋆ Fr k Ext x ra t₀ f c v := by
  have hF : ∀ j, Fr k Ext x ra t₀ f c j = cell4 (arg1 t₀ + 8#64) j ⋆
      (f =@ (rsp0 t₀ - 0xa8#64) ⋆ (Sv t₀ ⋆ (8 ?@ (rsp0 t₀ - 0xb0#64) ⋆ (Reserve k (rsp0 t₀ - 0xb0#64)
        ⋆ ((c =@ arg2 t₀ ⋆ ((Int.toBytes 8 x.buf.toInt =@ arg1 t₀ ⋆ (4 ?@ (arg1 t₀ + 0xc#64)
          ⋆ cell4 (arg1 t₀ + 0x10#64) x.p8)) ⋆ (Blocks [(x.buf, x.L)] ⋆ (PsTabs x.v ⋆ Ext))))
          ⋆ (RetCell ra (rsp0 t₀) ⋆ x.R)))))) := fun j => by
    simp only [Fr, PF, GbW]; ac_rfl
  rw [hF] at h ⊢
  exact cell4_store h v

theorem t2L_split {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32} (h : m =⋆ Fr k Ext x ra t₀ f c i)
    (hl : c.length = 764) :
    m =⋆ 8 ?@ (rsp0 t₀ - 0xb0#64) ⋆ (Reserve k (rsp0 t₀ - 0xb0#64)
      ⋆ (680 ?@ (arg2 t₀ + 76#64) ⋆ t2L_MsR k Ext x ra t₀ f c i)) := by
  have e : c = c.take 76 ++ (c.drop 76).take 680 ++ c.drop 756 := by
    rw [List.append_assoc, show c.drop 756 = (c.drop 76).drop 680 by rw [List.drop_drop],
      List.take_append_drop, List.take_append_drop]
  simp only [Fr, PF] at h
  rw [e, t2L_val_app3 _ _ _ _ (by simp only [List.length_take, List.length_drop, hl]; omega)] at h
  have e1 : (c.take 76).length = 76 := by simp only [List.length_take, hl]; omega
  have e2 : ((c.drop 76).take 680).length = 680 := by
    simp only [List.length_take, List.length_drop, hl]; omega
  rw [e1, e2] at h
  have h' := Mem.ac (H₂ := ((c.drop 76).take 680) =@ (arg2 t₀ + 76#64)
    ⋆ (8 ?@ (rsp0 t₀ - 0xb0#64) ⋆ (Reserve k (rsp0 t₀ - 0xb0#64)
      ⋆ t2L_MsR k Ext x ra t₀ f c i))) h (by simp only [t2L_MsR]; ac_rfl)
  have h'' := Block.sep_intro e2 (by omega) h'
  exact Mem.ac h'' (by ac_rfl)

theorem t2L_join {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64}
    {t₀ : MachineData} {f c : List UInt8} {i : BitVec 32}
    (h : m =⋆ 8 ?@ (rsp0 t₀ - 0xb0#64) ⋆ (Reserve k (rsp0 t₀ - 0xb0#64)
      ⋆ (List.replicate 680 0 =@ (arg2 t₀ + 76#64) ⋆ t2L_MsR k Ext x ra t₀ f c i)))
    (hl : c.length = 764) : m =⋆ Fr k Ext x ra t₀ f (wr c 76 680 0) i := by
  simp only [Fr, PF, wr, t2L_tb0]
  rw [t2L_val_app3 _ _ _ _ (by simp only [List.length_take, List.length_drop, List.length_replicate, hl]; omega)]
  have e1 : (c.take 76).length = 76 := by simp only [List.length_take, hl]; omega
  rw [e1, List.length_replicate]
  exact Mem.ac h (by simp only [t2L_MsR]; ac_rfl)

/-- `t2L_MsR` at some index within the buffer. -/
abbrev t2L_Rex (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData)
    (f c : List UInt8) : Mem 64 → Prop :=
  fun m => ∃ i : BitVec 32, i.toNat ≤ x.p8.toNat ∧ t2L_MsR k Ext x ra t₀ f c i m

set_option maxRecDepth 20000 in
/-- The error path: the clamp's second half, `memset` of the four arrays, to the epilogue. -/
theorem blk_L1499 (k : Nat) (Ext : Mem 64 → Prop) (hMs : MemsetValSpec k) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L1499" := by
  cfg_block
  measure_hb "L1499"
    intro n
    simp only [tab_L1499, var_L1499, tab_L14b7, var_L14b7]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hC, hbx, h15, hc0, hR, hax, hdx, hsi, hcx⟩, hn⟩ := hs₀
    have hl : c.length = 764 := hC.2.1.2.2.2.1.1
    have hPi : PsInv c := hC.2.1.2.2.2.1
    have hPs := hC.1
    obtain ⟨-, -, hip, hp31, -, -, hb0⟩ := hPs
    have hm := hC.2.2
    have hsp : s₀.regs.get64 .rsp = rsp0 t₀ - 0xa8#64 := hC.2.1.1
    have hbp : s₀.regs.get64 .rbp = rsp0 t₀ - 8#64 := hC.2.1.2.1
    have hf : f.length = 0x78 := hC.2.1.2.2.1
    have hpre := fun v => t2L_split (t2L_idx hm v) hl
    have hpush := fun v w => Block.storeInt_val (hpre v) (Split.here _ _) w
    have hld : ∀ v : BitVec 32, ((s₀.dmem.storeInt (arg1 t₀ + 8#64) 4 v.toInt).loadInt
        (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := fun v => by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome (hpre v) (by simp)
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = rsp0 t₀ - 0xb0#64 := by
      rw [hsp]; show _ - 168#64 - 8#64 = _; rw [BitVec.sub_sub_ofNat]
    have e8 : Int64.toBitVec 8 = 8#64 := rfl
    have e680 : (BitVec.setWidth 64 (BitVec.setWidth 32 (Int64.toBitVec 680))).toNat = 680 := rfl
    have edst : BitVec.setWidth 64 (Int64.toBitVec 76) + s₀.regs.get64 .rbx = arg2 t₀ + 76#64 := by
      rw [hbx, BitVec.add_comm]; rfl
    have ez : ∀ a : BitVec 32,
        ({ toBitVec := BitVec.setWidth 8 (BitVec.setWidth 64 (a ^^^ a)) } : UInt8) = 0 := fun a => by
      simp only [BitVec.xor_self]; rfl
    vcgen [MachineWP.call_proc_spec_at (⟨t2L_Rex k Ext x ra t₀ f c⟩ : MsA) "memset" hMs]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      rw [hsi, e8, Fr_gb_idx hm]; rfl
    case vc2 =>
      simp only [hsi, e8, e48, e680, edst, t2_sw3264] at *
      refine ⟨fun ra' => ⟨?_, fun s' hpost => ?_⟩, hld _⟩
      · exact t2L_mono3 (hpush _ _) (fun m' h => ⟨_, t2L_ib _ _ _ x.idx x.p8 _ hax hdx hcx hip hp31, h⟩)
      · obtain ⟨-, hsp', hbp', ⟨-, -, -, -, h15'⟩, hm'⟩ := hpost
        rw [ez] at hm'
        obtain ⟨i', hi', hm2⟩ := t2L_ex3 hm'
        have hF := t2L_join hm2 hl
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨⟨wr c 76 680 0, i', f, ⟨t1_PsInv_wr 76 680 0 hPi (by omega) (by omega),
          fun hw => t2L_wf hl hPi hc0 (hR hw), hi', ?_, ?_⟩, hf, ?_, ?_, hF⟩, by var_step⟩
        · rw [h15', h15]; exact hb0
        · rw [h15', h15]; exact Int.le_refl _
        · have ek : ∀ R : BitVec 64, R - 0xb0#64 + 8 = R - 0xa8#64 := fun R => by bv_omega
          rw [hsp', ek]
        · rw [hbp', hbp]

end Kraken.Examples.Sbr.Ps
