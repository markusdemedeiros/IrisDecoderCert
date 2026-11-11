import Kraken.InfoOff
import Kraken.Rules.HbOptApply
import Kraken.X64.Examples.Sbr.ApplyTable

/-! # `ff_aac_sbr_apply`: blocks of shard `EntrySyn` -/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open scoped Kraken.FrameLemmas.Int32Nat
set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Apply

variable [CodeEnv]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ## Syn helper lemmas (apply) -/

/-- Re-packing the footprint at values `y` (that `Keep` the pointers of `x`, with `SbrWF y`)
as `ApplyFPost`. -/
theorem fpost_of {e : Env} {x y : Args} {t : MachineData} {A K : Mem 64 → Prop} {m : Mem 64}
    (hK : x.Keep y) (hw : SbrWF y) (h : m =⋆ A ⋆ (ApplyF e y t ⋆ K)) :
    m =⋆ A ⋆ (ApplyFPost e x t ⋆ K) := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu', hi', hc, hd⟩ := h
  obtain ⟨-, hav, hf, he, hps, ha', hs, hr, hD⟩ := hK
  exact ⟨a, b, hu, hi, ha, c, d, hu', hi', ⟨y, he, hf, ha', hs, hr, hD, hw, hav, hps, hc⟩, hd⟩

/-- `DWF` with a new `synthesis_filterbank_samples_offset` within its bounds. -/
theorem dwf_setVOff {live : Prop} {d : DV} {v : BitVec 32} (hw : DWF live d)
    (h1 : v.toInt ≤ 1664) (h2 : v.toNat % 8 = 0) : DWF live { d with vOff := v } := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, -, -, b16⟩ := hw
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, h1, h2, b16⟩

/-- `SbrWF` after channel 0's synthesis (`*v_off` as `QmfFPost`'s `VOffW` returns it). -/
theorem sbrwf_setV0 {y : Args} {v : BitVec 32} (hw : SbrWF y) (h1 : v.toInt ≤ 1664)
    (h2 : v.toNat % 8 = 0) : SbrWF (y.setV0 v) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hw
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, dwf_setVOff a14 h1 h2, a15, a16⟩

/-- `SbrWF` after channel 1's synthesis. -/
theorem sbrwf_setV1 {y : Args} {v : BitVec 32} (hw : SbrWF y) (h1 : v.toInt ≤ 1664)
    (h2 : v.toNat % 8 = 0) : SbrWF (y.setV1 v) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hw
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, dwf_setVOff a15 h1 h2, a16⟩

theorem applyc_setV0 {y : Args} {t : MachineData} {v : BitVec 32} (h : ApplyC y t)
    (h1 : v.toInt ≤ 1664) (h2 : v.toNat % 8 = 0) : ApplyC (y.setV0 v) t :=
  ⟨sbrwf_setV0 h.1 h1 h2, h.2⟩

theorem applyc_setV1 {y : Args} {t : MachineData} {v : BitVec 32} (h : ApplyC y t)
    (h1 : v.toInt ≤ 1664) (h2 : v.toNat % 8 = 0) : ApplyC (y.setV1 v) t :=
  ⟨sbrwf_setV1 h.1 h1 h2, h.2⟩

/-- The `*v_off` cell `sbr_qmf_synthesis` returns (`VOffW`): some value within `DWF`'s bounds. -/
theorem voffw_cell {a : BitVec 64} {F : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ VOffW a ⋆ F) :
    ∃ v : BitVec 32, v.toInt ≤ 1664 ∧ v.toNat % 8 = 0 ∧ (m =⋆ cell4 a v ⋆ F) := by
  obtain ⟨m₁, m₂, hu, hi, ⟨v, h1, h2, hc⟩, hF⟩ := h
  exact ⟨v, h1, h2, m₁, m₂, hu, hi, hc, hF⟩


/-- The callees' area with four 8-byte cells (the stack arguments of `sbr_qmf_synthesis`) carved off its top. -/
theorem res_args (k : Nat) {r₀ : BitVec 64} (hW : 0x460 + k ≤ r₀.toNat) (K : Mem 64 → Prop) :
    Reserve (0x298 + k) (r₀ - 0x1c8#64) ⋆ K
      = 8 ?@ (r₀ - 0x1c8#64 - 8#64) ⋆ (8 ?@ (r₀ - 0x1c8#64 - 16#64) ⋆ (8 ?@ (r₀ - 0x1c8#64 - 24#64)
        ⋆ (8 ?@ (r₀ - 0x1c8#64 - 32#64) ⋆ (Reserve (0x278 + k) (r₀ - 0x1c8#64 - 32#64) ⋆ K)))) := by
  have hr : 0x298 + k ≤ (r₀ - 0x1c8#64).toNat := by bv_omega
  generalize r₀ - 0x1c8#64 = r at hr ⊢
  rw [show 0x298 + k = 8 + (8 + (8 + (8 + (0x278 + k)))) by omega,
    Reserve_split 8 _ r (by omega)]
  rw [Reserve_split 8 _ (r - BitVec.ofNat 64 8) (by bv_omega)]
  rw [Reserve_split 8 _ (r - BitVec.ofNat 64 8 - BitVec.ofNat 64 8) (by bv_omega)]
  rw [Reserve_split 8 _ (r - BitVec.ofNat 64 8 - BitVec.ofNat 64 8 - BitVec.ofNat 64 8) (by bv_omega)]
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, Std.ExtHashMap.sep_assoc]

/-- A raw 4-byte block holds some 32-bit value. -/
theorem blk4_cell {a : BitVec 64} {F : Mem 64 → Prop} {m : Mem 64} (h : m =⋆ 4 ?@ a ⋆ F) :
    ∃ v : BitVec 32, m =⋆ cell4 a v ⋆ F := by
  obtain ⟨-, bs, hl, h⟩ := Block.sep_elim h
  refine ⟨BitVec.ofInt 32 (Int.ofBytes bs), ?_⟩
  have e : Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes bs)).toInt = bs := by
    rw [BitVec.toInt_ofInt, ← Int.toBytes_emod, Int.take]
    have h2 : (Int.ofBytes bs).bmod (2 ^ 32) % (2 ^ (8 * 4) : Int) = Int.ofBytes bs % 2 ^ (8 * 4) :=
      Int.bmod_emod
    rw [h2, show Int.ofBytes bs % 2 ^ (8 * 4) = (Int.ofBytes bs).take (8 * 4) from rfl, Int.toBytes_emod,
      Int.toBytes_ofBytes 4 bs (by omega), List.take_of_length_le (by omega)]
  simp only [cell4, Val, e]
  exact h

/-- The callees' area at the `sbr_qmf_synthesis` calls (stack arguments already pushed):
the return-address slot, the callee's `qmfNeed k`, the rest. -/
theorem res_qmf (k : Nat) (r : BitVec 64) (hr : 0x278 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x278 + k) r ⋆ K
      = 8 ?@ (r - 8#64) ⋆ (Reserve (0x130 + k) (r - 8#64)
        ⋆ (0x140 ?@ (r - BitVec.ofNat 64 (0x278 + k)) ⋆ K)) := by
  rw [show 0x278 + k = 8 + (0x270 + k) by omega, Reserve_split 8 (0x270 + k) r (by omega),
    Reserve.excess (0x130 + k) (0x270 + k) (r - BitVec.ofNat 64 8) (by omega) (by bv_omega),
    BitVec.sub_sub_ofNat, show 0x270 + k - (0x130 + k) = 0x140 by omega]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The pushed `div` (0 or 1, 8 bytes): its low 4 bytes as `sbr_qmf_synthesis` reads them, the high 4. -/
theorem c8_div (a : BitVec 64) (d : Nat) (hd : d ≤ 1) :
    c8 a (BitVec.ofNat 64 d) = Int.toBytes 4 (d : Int) =@ a ⋆ Int.toBytes 4 0 =@ (a + 4#64) := by
  have e : Int.toBytes 8 (BitVec.ofNat 64 d).toInt = Int.toBytes 4 (d : Int) ++ Int.toBytes 4 0 := by
    rcases (by omega : d = 0 ∨ d = 1) with rfl | rfl <;> decide
  simp only [c8, e]
  exact Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length]; try rfl) (by simp only [Int.toBytes_length]; try decide)

theorem syn_al32 (a : BitVec 64) (c : Nat) (ha : isAligned 32 a = true) (hc : c % 32 = 0) :
    isAligned 32 (a + BitVec.ofNat 64 c) = true :=
  isAligned_add (by decide) ha (by simp only [BitVec.toNat_ofNat]; omega)

theorem syn_al16 {a : BitVec 64} (h : isAligned 32 a = true) : isAligned 16 a = true := by
  simp only [isAligned, beq_iff_eq] at *; omega

/-- `rsp` arithmetic at the call: `a - c + d = a - (c - d)`. -/
theorem syn_subadd (a : BitVec 64) (c d : Nat) (h : d ≤ c) (hc : c < 2 ^ 64) :
    a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c - d) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- The `sbr_qmf_synthesis` contract at `div = dsN x`. -/
theorem syn_qspec {k : Nat} {e : Env} {x : Args} (h0 : QmfSynthesisSpec 0 k e.Ctx e.TxTab e.fs.qfs)
    (h1 : QmfSynthesisSpec 1 k e.Ctx e.TxTab e.fs.qfs) :
    QmfSynthesisSpec (dsN x) k e.Ctx e.TxTab e.fs.qfs := by
  unfold dsN; split <;> assumption

theorem syn_dsN_le (x : Args) : dsN x ≤ 1 := by unfold dsN; split <;> omega

theorem syn_win0 {x : Args} (h : dsN x = 0) :
    (2560 ?@ lab "sbr_qmf_window_us" : Mem 64 → Prop) = (2560 >>> dsN x) ?@ qmfWin (dsN x) := by
  rw [h]; simp only [qmfWin, if_true, Nat.reduceShiftRight]

theorem syn_win1 {x : Args} (h : dsN x = 1) :
    (1280 ?@ lab "sbr_qmf_window_ds" : Mem 64 → Prop) = (2560 >>> dsN x) ?@ qmfWin (dsN x) := by
  rw [h]; simp only [qmfWin, Nat.one_ne_zero, if_false, Nat.reduceShiftRight]

/-! ### D6 (M4b, apply-dqcpl): the `ff_ps_apply` call (`L9a02`) -/

/-- D6: `PsWF` after `ff_ps_apply`: `psc` unchanged, the new `h'` within W6. -/
theorem ps_wf_post {c h h' : List UInt8} (hw : PsWF c h) (hl : h'.length = 68)
    (h6 : ∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63) :
    PsWF c h' := by
  obtain ⟨a1, -, a3, a4, a5, a6, a7, a8, -, a10⟩ := hw
  exact ⟨a1, hl, a3, a4, a5, a6, a7, a8, h6, a10⟩

/-- D6: `SbrWF` with the new phase histories. -/
theorem ps_sbrwf_post {y : Args} {h' : List UInt8} (hw : SbrWF y) (hl : h'.length = 68)
    (h6 : ∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63) :
    SbrWF { y with psh := h' } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hw
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, ps_wf_post a16 hl h6⟩

/-- D6: `Int.ofBytes` is the unsigned value. -/
theorem ps_int_ofBytes (bs : List UInt8) : Int.ofBytes bs = ((Nat.ofBytes bs : Nat) : Int) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show Int.ofBytes bs * 256 + ((b.toNat : Nat) : Int) = ((Nat.ofBytes bs * 256 + b.toNat : Nat) : Int)
    rw [ih]; omega

/-- D6: the gate `ps->common.start != 0` read as a 32-bit load. -/
theorem ps_gate {bs : List UInt8} (h : BitVec.ofInt 32 (Int.ofBytes bs) ≠ 0) :
    (BitVec.ofNat 32 (Nat.ofBytes bs)).toInt ≠ 0 := by
  rw [ps_int_ofBytes, BitVec.ofInt_natCast] at h
  intro h'; apply h; apply BitVec.eq_of_toInt_eq; rw [h']; simp

/-- D6: the gate from `cmpl $0x0, (ps)` / `je` not taken. -/
theorem ps_gate2 {bs : List UInt8} {v : Int} (hv : some (Int.ofBytes bs) = some v)
    {f : StatusFlags.from_result.Remaining}
    (h : CondCode.z.interp (StatusFlags.from_result (BitVec.ofInt 32 v - BitVec.setWidth 32 0#64) f) = false) :
    (BitVec.ofNat 32 (Nat.ofBytes bs)).toInt ≠ 0 := by
  simp only [CondCode.interp_z, StatusFlags.zf_from_result, beq_eq_false_iff_ne, ne_eq] at h
  cases hv
  refine ps_gate fun h' => h ?_
  rw [h']; decide

/-- D6: `ps_post_ex` inside the call frame (`ra` cell, reserve). -/
theorem ps_post_ex3 {PsTab : Mem 64 → Prop} {a : PsArgs} {t : MachineData} {A B F : Mem 64 → Prop}
    {m : Mem 64} (h : m =⋆ A ⋆ (B ⋆ (PsApplyFPost PsTab a t ⋆ F))) :
    ∃ h' : List UInt8, h'.length = 68
      ∧ (∀ b < 34, 0 ≤ i8 h' b ∧ i8 h' b ≤ 63 ∧ 0 ≤ i8 h' (34 + b) ∧ i8 h' (34 + b) ≤ 63)
      ∧ (m =⋆ A ⋆ (B ⋆ (PsApplyF PsTab { a with psh := h' } t ⋆ F))) := by
  obtain ⟨m1, m2, hu, hi, hA, m3, m4, hu2, hi2, hB, m5, m6, hu3, hi3, ⟨h', hl, hw, hp⟩, hF⟩ := h
  exact ⟨h', hl, hw, m1, m2, hu, hi, hA, m3, m4, hu2, hi2, hB, m5, m6, hu3, hi3, hp, hF⟩

/-! ### M4b layout (apply-mapb): the synthesis call windows -/

/-- The rest of `analysis_filterbank_samples` beside the `qmfVSize` window of the
synthesis call (`a` = `&synthesis_filterbank_samples`): the last 3200 bytes when the window
is the larger one (11264 bytes), else all 5248 bytes. -/
def qvRest (dd : Nat) (off : BitVec 32) (a : BitVec 64) : Mem 64 → Prop :=
  if dd = 0 ∧ 1152 < off.toInt then 3200 ?@ (a + 11264#64) else 5248 ?@ (a + 9216#64)

omit [CodeEnv] in
/-- `synthesis_filterbank_samples ++ analysis_filterbank_samples` as the synthesis call's
`v0` window (`qmfVSize`) and the rest: for the larger window this is `a3_overread_carve` (relative to
`a = d + 0x80`). -/
theorem qv_carve (a : BitVec 64) (dd : Nat) (off : BitVec 32) (K : Mem 64 → Prop) :
    9216 ?@ a ⋆ (5248 ?@ (a + 9216#64) ⋆ K) = qmfVSize dd off ?@ a ⋆ (qvRest dd off a ⋆ K) := by
  unfold qmfVSize qvRest
  split
  · have e1 := Block.split a 9216 2048 (by decide)
    have e2 := Block.split (a + 9216#64) 2048 3200 (by decide)
    simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd] at e1 e2
    rw [e1, e2]
    simp only [Std.ExtHashMap.sep_assoc]
  · rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_start (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply" ⟨"ff_aac_sbr_apply", B.start, some "ff_aac_sbr_apply.start_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨rfl, ⟨hm, hC⟩⟩ := T.start.mp hs
  simp only [CallPre, applyNeed] at hm
  rw [reserve_frame k hSt, frame_split] at hm
  dsimp only
  simp only [B.start]
  clear hs
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd,
      Width.bytes, BitVec.add_zero, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, Nat.reduceAdd, Nat.reducePow, Nat.reduceSub,
    Nat.reduceLeDiff] at *
  case vc9 =>
    rw [T.start_1]
    refine ⟨⟨hC, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, arg0, arg1, arg2, arg3, arg4]
    case refine_8 =>
      sep_mem hm
      dsimp only [Mm, FrA, c8, arg3, arg4]
      sep_close hm
    case refine_9 => var_step
  all_goals sep_mem hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_start_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.start_1" ⟨"ff_aac_sbr_apply.start_1", B.start_1, some "ff_aac_sbr_apply.start_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ⟨h0, h1, h2, h3, h4⟩, hm⟩ := T.start_1.mp hs
  clear hs
  -- open the groups the block reads
  simp only [Mm, ApplyF, ScW, AcW, FrA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h0 h1 h2 h3 h4
  -- the `setl -0xf0(%rbp)` byte: cut slot sf0 into its low byte and the rest
  have hsp : (8 ?@ (t₀.regs.get64 .rsp - 248#64)) = 1 ?@ (t₀.regs.get64 .rsp - 248#64)
      ⋆ 7 ?@ (t₀.regs.get64 .rsp - 247#64) := by
    rw [show (8 : Nat) = 1 + 7 from rfl, Mem.Block.split _ 1 7 (by decide)]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [hsp] at hm
  simp only [B.start_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h0, h1, arg0, arg1, z]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  case vc4 =>
    have ez : BitVec.setWidth 64 0#32 = 0#64 := by decide
    rw [T.start_2]
    refine ⟨⟨hC, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      BitVec.xor_self, ez, true_and,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, arg0, arg1, arg2, arg3, arg4, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]
    case refine_8 =>
      have hq0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.extRate
      have hq1 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.sampleRate
      simp only [BitVec.setWidth_setWidth_of_le, Nat.reduceLeDiff, BitVec.setWidth_eq, hq0, hq1] at hm ⊢
      simp (disch := rfl) only [setl_byte] at hm ⊢
      simp only [Mm, ApplyF, ScW, AcW, FrA1, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
        BitVec.reduceAdd, dsN]
      sep_close hm
    case refine_9 => var_step

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_start_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.start_2" ⟨"ff_aac_sbr_apply.start_2", B.start_2, some "ff_aac_sbr_apply.start_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, ⟨h0, h1, h2, h3, h4⟩, hm⟩ := T.start_2.mp hs
  clear hs
  -- open the groups the block reads
  simp only [Mm, ApplyF, ScW, AcW, FrA, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h0 h1 h2 h3 h4
  dsimp only
  have hq0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.start
  have hq1 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.ready
  have hq2 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.pushed
  have e0 : BitVec.setWidth 32 0#64 = 0#32 := by decide
  simp only [B.start_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hzf : (x.pushed == 0#32) = decide (x.pushed = 0#32) := rfl
  have e8 : BitVec.setWidth 8 1#64 = 1#8 := by decide
  have e8' : BitVec.setWidth 8 (BitVec.setWidth 64 0#32) = 0#8 := by decide
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h1, hrbp, hrsp, z,
    Int64.toBitVec_neg_ofNat_norm, Nat.reduceSub, Nat.reduceAdd]
  all_goals try simp_loads [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp_conds [CondCode.interp, StatusFlags.from_result, hq0, hq1, hq2, Int64.toBitVec_ofNat_norm,
    BitVec.setWidth_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
    BitVec.zero_eq, beq_eq_false_iff_ne, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6797") ?_; refine ⟨isSome_at L.L6797, ?_, ?_⟩; rw [T.L6797])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6817") ?_; refine ⟨isSome_at L.L6817, ?_, ?_⟩; rw [T.L6817])
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6f32") ?_; refine ⟨isSome_at L.L6f32, ?_, ?_⟩; rw [T.L6f32])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.start_3])
  all_goals try (refine ⟨hC, ?_⟩; and_intros)
  all_goals try (refine ⟨⟨hC, ?_⟩, ?_⟩; and_intros)
  all_goals try (refine ⟨x, Or.inl rfl, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; exact IdLive.of_start0 ‹_›)
  all_goals try (refine IdLive.of_eq ?_; have hq3 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.idAac; have hcmp := ‹BitVec.setWidth 32 _ - BitVec.setWidth 32 (BitVec.setWidth 64 _) = 0#32›; rw [h2, hq3, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq] at hcmp; have hcmp' := congrArg (· + x.idAac) hcmp; simp only [BitVec.sub_add_cancel, BitVec.zero_add] at hcmp'; exact hcmp'.symm)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, setWidth8_replaceLow,
    BitVec.xor_self, e8, e8']; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, StatusFlags.from_result,
    hq2, e0, Int64.toBitVec_ofNat_norm, BitVec.sub_zero, BitVec.ofNat_eq_ofNat]; rfl)
  all_goals try (simp only [ne_eq, BitVec.ofNat_eq_ofNat]; assumption)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq,
      BitVec.sub_sub_ofNat, Nat.reduceAdd, arg0, arg1, arg2, arg3, arg4, hrsp, hrbp, and_self, h0, h1, h2, h3, h4]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, AcW, FrA, FrD, FrRaw, sbrA, arg0, arg1, arg2, arg3, arg4,
    BitVec.add_assoc, BitVec.reduceAdd]; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_start_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.start_3" ⟨"ff_aac_sbr_apply.start_3", B.start_3, some "ff_aac_sbr_apply.L676e"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨⟨hC, hid⟩, ⟨hrsp, hrbp⟩, h9, hb, hst, hz, hm⟩ := T.start_3.mp hs
  clear hs
  simp only [B.start_3]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp_conds [CondCode.interp, hz, decide_eq_false_iff_not, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    Bool.not_eq_true', Bool.not_eq_false', decide_not, ne_eq]
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6825") ?_
                 refine ⟨isSome_at L.L6825, ?_, ?_⟩; rw [T.L6825])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L676e])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x, Or.inl rfl, Or.inr ⟨?_, rfl, hst⟩, by assumption, hid, hm⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, hb]; done)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L676e (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L676e" ⟨"ff_aac_sbr_apply.L676e", B.L676e, some "ff_aac_sbr_apply.L6797"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, x', hx', hbl, hp, hid, hm⟩ := T.L676e.mp hs
  clear hs
  have hK : x.Keep x'.push ∧ IdLive t₀ x'.push := ⟨by rcases hx' with rfl | rfl <;> first | exact Args.Keep.rfl'.push | exact Args.Keep.rfl'.turnoff.push, hid⟩
  have hid' := PLift.up hid; clear hid
  have hC' : ApplyC x'.push t₀ := by rcases hx' with rfl | rfl <;> first | exact hC.push | exact hC.turnoff.spSet.push
  have hK' := PLift.up hK; have hC'' := PLift.up hC'; clear hK hC'
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  simp only [B.L676e]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  -- the `test %bl,%bl` branch
  all_goals try (rcases hbl with hb | ⟨hb, rfl, hst⟩ <;>
    simp_conds [CondCode.interp, StatusFlags.from_result, Reg64s.get64_set64, ite_true, ite_false, hb,
      BitVec.and_self, reduceCtorEq, BitVec.zero_eq, beq_eq_false_iff_ne, ne_eq, BitVec.reduceEq,
      not_false_eq_true, not_true_eq_false, beq_self_eq_true, Bool.true_eq_false, Bool.not_eq_eq_eq_not,
      Bool.not_false, Bool.not_true, beq_iff_eq])
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L74e9"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74e9") ?_
                 refine ⟨isSome_at L.L74e9, ?_, ?_⟩; rw [T.L74e9])
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6838"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6838") ?_
                 refine ⟨isSome_at L.L6838, ?_, ?_⟩; rw [T.L6838])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x'.push, hK'.down, hC''.down, ?_⟩)
  all_goals try (refine ⟨⟨hC, hid'.down⟩, ⟨?_, ?_⟩, ?_, hst, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd,
    Int.toBytes4_reload, TabW_push, FnW_push, AcW_push, OutW_push, PsW, hp, ite_true] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6797 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6797" ⟨"ff_aac_sbr_apply.L6797", B.L6797, some "ff_aac_sbr_apply.L6797_1"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h0, h2, hm⟩ := T.L6797.mp hs
  clear hs
  simp only [Mm, ApplyF, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h0 h2
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  dsimp only
  simp only [B.L6797]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have zc : ∀ (a : BitVec 64) (c d : Nat), d ≤ c → a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c - d) := by
    intro a c d h; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h0, h2]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  case vc2 => decide
  case vc3 =>
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, h0, h2, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, h0, h2, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, h0, h2, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L6797_1]
      have h14' : s'.regs.get64 .r14 = 0#64 := by
        rw [hsv.2.2.2.1]
        all_goals first
        | (simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hrbp]; done)
        | exact hrbp.2
      refine ⟨hC, ⟨hrsp', hrbp', h14'⟩, ?_⟩
      simp only [Mm, ApplyF, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
        BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6797_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6797_1" ⟨"ff_aac_sbr_apply.L6797_1", B.L6797_1, some "ff_aac_sbr_apply.L6817"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, hm⟩ := T.L6797_1.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, DScW, FrA, sbrA, dA, Args.d, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd] at hm
  -- the 8-byte store covers `start` and `ready`: merge the two cells
  sep_pull hm [cell4 (t₀.regs.get64 .rsi + 0x28924#64) x.start,
    cell4 (t₀.regs.get64 .rsi + 0x28928#64) x.ready] as R hR
  rw [← Std.ExtHashMap.sep_assoc, ← Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  dsimp only
  simp only [B.L6797_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have e8 : BitVec.setWidth 8 1#64 = 1#8 := by decide
  have e8' : BitVec.setWidth 8 (BitVec.setWidth 64 0#32) = 0#8 := by decide
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  -- the load of the `che` slot: name its result, normalise its address, read the frame
  all_goals try (rename_i v hv; simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
    Width.bytes, hrbp, z, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv)
  all_goals try (simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at hv)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  case vc10 =>
    refine ⟨?_, ?_⟩
    rotate_left
    · var_step
    rw [T.L6817]
    refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, x.turnoff.spSet, Or.inr rfl, (IdLive.turnoff).spSet, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, arg1]; done)
    all_goals try (simp only [Reg64s.get64_set64, ite_true, setWidth8_replaceLow, e8]; done)
    have h8 : Int.toBytes 8 (BitVec.setWidth 64 0#64).toInt
        = Int.toBytes 4 (0#32).toInt ++ Int.toBytes 4 (0#32).toInt := by decide
    have e0 : (BitVec.setWidth 32 0#64).toInt = ((0 : Nat) : Int) := by decide
    have e32 : (BitVec.setWidth 32 32#64).toInt = ((32 : Nat) : Int) := by decide
    rw [h8, Val.append_eq _ _ _ (t₀.regs.get64 .rsi + 166184#64) (by simp only [Int.toBytes_length,
      BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
    have es32 : BitVec.setWidth 32 4294967295#64 = BitVec.allOnes 32 := by decide
    have es16 : BitVec.setWidth 16 65535#64 = BitVec.allOnes 16 := by decide
    simp only [e0, e32, es32, es16] at hm
    have hT : TabW x.turnoff.spSet t₀ = TabW x t₀ := rfl
    have hF : FnW e x.turnoff.spSet t₀ = FnW e x t₀ := rfl
    have hA : AcW x.turnoff.spSet t₀ = AcW x t₀ := rfl
    have hO : OutW x.turnoff.spSet t₀ = OutW x t₀ := rfl
    have hP : PsW x.turnoff.spSet t₀ = PsW x t₀ := rfl
    simp only [Mm, ApplyF, hT, hF, hA, hO, hP]
    simp only [ScW, DScW, FrD, sbrA, dA, Args.d, Args.turnoff, Args.spSet, arg1, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd]
    sep_close hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6817 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6817" ⟨"ff_aac_sbr_apply.L6817", B.L6817, some "ff_aac_sbr_apply.L6825"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hb, x', hx', hid, hm⟩ := T.L6817.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  have hp0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x'.pushed
  simp only [B.L6817]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp_conds [CondCode.interp, StatusFlags.from_result, hp0, Int64.toBitVec_ofNat_norm,
    BitVec.setWidth_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
    BitVec.zero_eq, beq_eq_false_iff_ne]
  all_goals try (left; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L676e") ?_
                 refine ⟨isSome_at L.L676e, ?_, ?_⟩; rw [T.L676e])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6825])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x', hx', Or.inl hb, by assumption, hid, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6825 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6825" ⟨"ff_aac_sbr_apply.L6825", B.L6825, some "ff_aac_sbr_apply.L6838"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, x', hx', hbl, hp, hid, hm⟩ := T.L6825.mp hs
  clear hs
  have hK : x.Keep x'.push ∧ IdLive t₀ x'.push := ⟨by rcases hx' with rfl | rfl <;> first | exact Args.Keep.rfl'.push | exact Args.Keep.rfl'.turnoff.push, hid⟩
  have hid' := PLift.up hid; clear hid
  have hC' : ApplyC x'.push t₀ := by rcases hx' with rfl | rfl <;> first | exact hC.push | exact hC.turnoff.spSet.push
  have hK' := PLift.up hK; have hC'' := PLift.up hC'; clear hK hC'
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  have hp' : ¬ x'.pushed = 0#32 := hp
  have e0 : BitVec.setWidth 32 0#64 = 0#32 := by decide
  simp only [B.L6825]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  -- the `test %bl,%bl` branch
  all_goals try (rcases hbl with hb | ⟨hb, rfl, hst⟩ <;>
    simp_conds [CondCode.interp, StatusFlags.from_result, Reg64s.get64_set64, ite_true, ite_false, hb,
      BitVec.and_self, reduceCtorEq, BitVec.zero_eq, beq_eq_false_iff_ne, ne_eq, BitVec.reduceEq,
      not_false_eq_true, not_true_eq_false, beq_self_eq_true, Bool.true_eq_false, Bool.not_eq_eq_eq_not,
      Bool.not_false, Bool.not_true, beq_iff_eq])
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L74e9"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L74e9") ?_
                 refine ⟨isSome_at L.L74e9, ?_, ?_⟩; rw [T.L74e9])
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6838])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x'.push, hK'.down, hC''.down, ?_⟩)
  all_goals try (refine ⟨⟨hC, hid'.down⟩, ⟨?_, ?_⟩, ?_, hst, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc, BitVec.reduceAdd,
    Int.toBytes4_reload, TabW_push, FnW_push, AcW_push, OutW_push, PsW, hp', ite_true, ite_false,
    Int64.toBitVec_ofNat_norm, e0, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6838 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6838" ⟨"ff_aac_sbr_apply.L6838", B.L6838, some "ff_aac_sbr_apply.L6838_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hst, hm⟩ := T.L6838.mp hs
  clear hs
  simp only [Mm, ApplyF, FrD, FrRaw] at hm
  have e1 : BitVec.setWidth 64 (BitVec.setWidth 32 1#64) = 1#64 := by decide
  simp only [B.L6838]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6838_1])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, hst, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, FrE, FrRaw, Args.push, e1] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6838_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6838_1" ⟨"ff_aac_sbr_apply.L6838_1", B.L6838_1, some "ff_aac_sbr_apply.L6838_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hst, hm⟩ := T.L6838_1.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, DScW, dA, Args.d, CstW, FrE, FrRaw, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd,
    TabW_push, FnW_push, AcW_push, OutW_push, PsW, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hm h9
  simp only [B.L6838_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have e1 : BitVec.setWidth 64 (BitVec.setWidth 32 1#64) = 1#64 := by decide
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  -- exits
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6fca"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6fca") ?_
                 refine ⟨isSome_at L.L6fca, ?_, ?_⟩; rw [T.L6fca]
                 refine ⟨hC, ⟨?_, ?_⟩, ?_, 1, Or.inl rfl, ?_⟩)
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6fbe"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6fbe") ?_
                 refine ⟨isSome_at L.L6fbe, ?_, ?_⟩; rw [T.L6fbe]
                 refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6abf"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6abf") ?_
                 refine ⟨isSome_at L.L6abf, ?_, ?_⟩; rw [T.L6abf]
                 refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_⟩)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L6838_2]; refine ⟨hC, ⟨?_, ?_⟩, ?_, hst, ?_, ?_, ?_, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    arg1, sbrA, e1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, DScW, CstW, FrD, FrE, FrS0, FrRaw, sbrA, arg0, arg1, arg3, arg4, TabW_push, FnW_push, AcW_push, OutW_push, PsW,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  all_goals (simp only [Mm, ApplyF, ScW, DScW, dA, Args.d, CstW, FrD, FrE, FrS0, FrRaw, sbrA, arg0, arg1, arg3, arg4, TabW_push, FnW_push, AcW_push, OutW_push, PsW,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd] at hm ⊢; sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6838_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6838_2" ⟨"ff_aac_sbr_apply.L6838_2", B.L6838_2, some "ff_aac_sbr_apply.L68b0"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hst, hbx, h12, h13, hm⟩ := T.L6838_2.mp hs
  clear hs
  simp only [Mm, ApplyF, CstW, FrD, FrRaw, TabW_push, FnW_push, AcW_push, OutW_push] at hm
  have hne : 1 ≤ x.d0.nenv := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd0, -⟩, -⟩ := id hC.1
    exact (hd0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hst).1
  simp only [B.L6838_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try sep_mem hm
  all_goals try (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, Nat.le_refl]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L68b0])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ⟨1, Nat.le_refl _, hne, ?_, ?_, ?_⟩, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    hbx, h12, h13, arg1, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul]; done)
  all_goals try (simp only [Mm, ApplyF, CstW, FrD, FrRaw, TabW_push, FnW_push, AcW_push, OutW_push] at hm ⊢; sep_close hm)
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6f32 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6f32" ⟨"ff_aac_sbr_apply.L6f32", B.L6f32, some "ff_aac_sbr_apply.L6f32_1"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAv, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, hb, hm⟩ := T.L6f32.mp hs
  clear hs
  simp only [Mm, ApplyF, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64), e.Ext]
    as Rc hRc
  dsimp only
  simp only [B.L6f32]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have zc : ∀ (a : BitVec 64) (c d : Nat), d ≤ c → a - BitVec.ofNat 64 c + BitVec.ofNat 64 d = a - BitVec.ofNat 64 (c - d) := by
    intro a c d h; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "av_log" hAv]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, hb]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
    Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Reg64s.get64_set64, reduceCtorEq, ite_true,
    ite_false, hrbp, hrsp, z]
  all_goals try simp_loads [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, arg0, BitVec.add_assoc, BitVec.reduceAdd] at *
  all_goals try sep_mem hm
  case vc3 =>
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, hb, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, hb, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrsp, hrbp, and_self, hb, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 → a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L6f32_1]
      have h14' : s'.regs.get64 .r14 = 0#64 := by
        rw [hsv.2.2.2.1]
        all_goals first
        | (simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, hrbp]; done)
        | exact hrbp.2
      refine ⟨hC, ⟨hrsp', hrbp', h14'⟩, ?_, ?_⟩
      · rw [hsv.1]; simpa only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false] using hb
      simp only [Mm, ApplyF, AcW, FnW, FrD, sbrA, arg0, arg1, arg2, arg3, arg4, BitVec.add_assoc,
        BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6f32_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6f32_1" ⟨"ff_aac_sbr_apply.L6f32_1", B.L6f32_1, some "ff_aac_sbr_apply.L6f32_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, hb, hm⟩ := T.L6f32_1.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, DScW, FrA, sbrA, dA, Args.d, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd] at hm
  -- the 8-byte store covers `start` and `ready`: merge the two cells
  sep_pull hm [cell4 (t₀.regs.get64 .rsi + 0x28924#64) x.start,
    cell4 (t₀.regs.get64 .rsi + 0x28928#64) x.ready] as R hR
  rw [← Std.ExtHashMap.sep_assoc, ← Val.append_eq _ _ _ _ (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  dsimp only
  simp only [B.L6f32_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  -- the load of the `che` slot: name its result, normalise its address, read the frame
  all_goals try (rename_i v hv; simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
    Width.bytes, hrbp, z, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv)
  all_goals try (simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at hv)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, arg1, BitVec.add_assoc, BitVec.reduceAdd]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  refine ⟨?_, ?_⟩
  rotate_left
  · var_step
  rw [T.L6f32_2]
  refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, arg1]; done)
  all_goals try (simpa only [Reg64s.get64_set64, reduceCtorEq, ite_false] using hb)
  have h8 : Int.toBytes 8 (BitVec.setWidth 64 0#64).toInt
      = Int.toBytes 4 (0#32).toInt ++ Int.toBytes 4 (0#32).toInt := by decide
  have e0 : (BitVec.setWidth 32 0#64).toInt = ((0 : Nat) : Int) := by decide
  have e32 : (BitVec.setWidth 32 32#64).toInt = ((32 : Nat) : Int) := by decide
  rw [h8, Val.append_eq _ _ _ (t₀.regs.get64 .rsi + 166184#64) (by simp only [Int.toBytes_length,
    BitVec.add_assoc, BitVec.reduceAdd]) (by simp only [Int.toBytes_length]; decide)] at hm
  have es32 : BitVec.setWidth 32 4294967295#64 = BitVec.allOnes 32 := by decide
  have es16 : BitVec.setWidth 16 65535#64 = BitVec.allOnes 16 := by decide
  simp only [e0, e32, es32, es16] at hm
  have hT : TabW x.turnoff.spSet t₀ = TabW x t₀ := rfl
  have hF : FnW e x.turnoff.spSet t₀ = FnW e x t₀ := rfl
  have hA : AcW x.turnoff.spSet t₀ = AcW x t₀ := rfl
  have hO : OutW x.turnoff.spSet t₀ = OutW x t₀ := rfl
  have hP : PsW x.turnoff.spSet t₀ = PsW x t₀ := rfl
  simp only [Mm, ApplyF, hT, hF, hA, hO, hP]
  simp only [ScW, DScW, FrD, sbrA, dA, Args.d, Args.turnoff, Args.spSet, arg1, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, Nat.reduceMul, Nat.reduceAdd]
  sep_close hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L6f32_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L6f32_2" ⟨"ff_aac_sbr_apply.L6f32_2", B.L6f32_2, some "ff_aac_sbr_apply.L6fbe"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hb, hm⟩ := T.L6f32_2.mp hs
  clear hs
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  have hp0 := BitVec.ofInt_ofBytes_toBytes 32 4 rfl x.turnoff.spSet.pushed
  simp only [B.L6f32_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9]
  all_goals try sep_vals hm
  all_goals try sep_mem hm
  all_goals try simp_conds [CondCode.interp, StatusFlags.from_result, hp0, Int64.toBitVec_ofNat_norm,
    BitVec.setWidth_zero, BitVec.sub_zero, BitVec.ofNat_eq_ofNat, beq_iff_eq, decide_eq_true_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
    bne_iff_ne, ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not,
    BitVec.zero_eq, beq_eq_false_iff_ne]
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L676e"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L676e") ?_
                 refine ⟨isSome_at L.L676e, ?_, ?_⟩; rw [T.L676e])
  all_goals try (left; goal_has_str "ff_aac_sbr_apply.L6825"; refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L6825") ?_
                 refine ⟨isSome_at L.L6825, ?_, ?_⟩; rw [T.L6825])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, x.turnoff.spSet, Or.inr rfl, Or.inl hb, by assumption, (IdLive.turnoff).spSet, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L74de (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74de" ⟨"ff_aac_sbr_apply.L74de", B.L74de, some "ff_aac_sbr_apply.L74e9"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨⟨hC, hid⟩, ⟨hrsp, hrbp⟩, h9, hm⟩ := T.L74de.mp hs
  have hid' := PLift.up hid; clear hid
  clear hs
  simp only [Mm, ApplyF, ScW, sbrA, arg1, TabW_push, FnW_push, AcW_push, OutW_push, BitVec.add_assoc,
    BitVec.reduceAdd] at hm h9
  have e0 : BitVec.setWidth 32 0#64 = 0#32 := by decide
  have hC' : ApplyC { x.push with ready := 0 } t₀ := hC.push
  have hC'' := PLift.up hC'; clear hC'
  simp only [B.L74de]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  vcgen
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, { x.push with ready := 0 }, ⟨Args.Keep.rfl', hid'.down⟩,
    hC''.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, sbrA, arg1, TabW, FnW, AcW, OutW, PsW, e0, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L74e9 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9" ⟨"ff_aac_sbr_apply.L74e9", B.L74e9, some "ff_aac_sbr_apply.L74e9_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, y, hK, hCy, hm⟩ := T.L74e9.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  simp only [B.L74e9]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, h9]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_1])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9, arg1]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, lab]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrD, FrS1, sbrA, arg0, arg1, arg3, arg4, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try edge_step
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L74e9_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_1" ⟨"ff_aac_sbr_apply.L74e9_1", B.L74e9_1, some "ff_aac_sbr_apply.L74e9_2"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp, h14⟩, h9, hax, y, hK, hCy, hm⟩ := T.L74e9_1.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9
  simp only [B.L74e9_1]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hds : (0#64).replaceLow (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (((if x.extRate.toInt < x.sampleRate.toInt then 1 else 0 : Nat)) : Int)))))
      = BitVec.ofNat 64 (if x.extRate.toInt < x.sampleRate.toInt then 1 else 0) := by
    split <;> decide
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try (rename_i v hv; simp only [AddrIndex.offset64_none, Int64.toBitVec_neg_ofNat_norm,
    Width.bytes, hrbp, z, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv)
  all_goals try (simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.reduceLeDiff] at hv)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h14,
      and_self, h9, hax]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try simp_loads [AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Nat.reducePow,
    Nat.reduceMod, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h9, h14, z]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, hds]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_2])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    hax, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS1, FrS2, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L74e9_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_2" ⟨"ff_aac_sbr_apply.L74e9_2", B.L74e9_2, some "ff_aac_sbr_apply.L74e9_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, hax, h12, h13, y, hK, hCy, hm⟩ := T.L74e9_2.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9 h12 h13
  simp only [B.L74e9_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hr15 : ∀ a c : BitVec 64, a + BitVec.setWidth 64 (c - a) = c := by
    intro a c; rw [BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have ez : BitVec.setWidth 64 0#32 = 0#64 := by decide
  have hlsb : ∀ v : BitVec 64, (v.replaceLow (BitVec.setWidth 8 1#64)).getLsbD 0 = true := by
    intro v
    have h := congrArg (fun u : BitVec 8 => u.getLsbD 0) (BitVec.setWidth_replaceLow8 v (BitVec.setWidth 8 1#64))
    simp only [BitVec.getLsbD_setWidth] at h
    simpa using h
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      and_self, h9, hax, h12, h13]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_3])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    hax, h12, h13, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, lab,
    Int64.toBitVec_sub, hr15]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self,
    BitVec.setWidth_eq, ez, BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hlsb, decide_true]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS2, FrS3, FrL, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L74e9_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_3" ⟨"ff_aac_sbr_apply.L74e9_3", B.L74e9_3, some "ff_aac_sbr_apply.L74e9_4"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, h12, h13, h15, hax, y, hK, hCy, hm⟩ := T.L74e9_3.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9 h12 h13 hax
  simp only [B.L74e9_3]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      and_self, h9, h12, h13, h15, hax]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L74e9_4])
  all_goals try (refine ⟨hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    h12, h13, h15, hax, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, lab,
    BitVec.sub_add_cancel]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS3, FrS4, FrL, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L74e9_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L74e9_4" ⟨"ff_aac_sbr_apply.L74e9_4", B.L74e9_4, some "ff_aac_sbr_apply.L7682"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, ⟨hrsp, hrbp⟩, h9, h12, h13, h15, y, hK, hCy, hm⟩ := T.L74e9_4.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ScW, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h9 h12 h13
  have hsp : (1 ?@ (t₀.regs.get64 .rsp - 248#64) ⋆ 7 ?@ (t₀.regs.get64 .rsp - 247#64))
      = 8 ?@ (t₀.regs.get64 .rsp - 248#64) := by
    rw [show (8 : Nat) = 1 + 7 from rfl, Mem.Block.split _ 1 7 (by decide)]
    congr 2
    apply BitVec.eq_of_toNat_eq
    simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  simp only [FrS4] at hm
  rw [hsp] at hm
  simp only [B.L74e9_4]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hr15 : ∀ a c : BitVec 64, a + BitVec.setWidth 64 (c - a) = c := by
    intro a c; rw [BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  have ez : BitVec.setWidth 64 0#32 = 0#64 := by decide
  have hlsb : ∀ v : BitVec 64, (v.replaceLow (BitVec.setWidth 8 1#64)).getLsbD 0 = true := by
    intro v
    have h := congrArg (fun u : BitVec 8 => u.getLsbD 0) (BitVec.setWidth_replaceLow8 v (BitVec.setWidth 8 1#64))
    simp only [BitVec.getLsbD_setWidth] at h
    simpa using h
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      and_self, h9, h12, h13, h15]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_mem hm
  all_goals try (simp only [Mem.sub_add_add_lit, BitVec.reduceSub, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]; done)
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L7682])
  all_goals try (refine ⟨0, hC, ⟨?_, ?_⟩, by decide, ?_, ?_, ?_, ?_, y, ⟨hK'.down.1, ChLive.zero hK'.down.2⟩, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self, h9,
    h12, h13, h15, arg1, sbrA, BitVec.add_assoc, BitVec.reduceAdd]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hax, lab,
    Int64.toBitVec_sub, hr15]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.xor_self,
    BitVec.setWidth_eq, ez, BitVec.ofNat_eq_ofNat]; done)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hlsb, decide_true]; done)
  all_goals try (simp only [Mm, ApplyF, ScW, FrS4, FrL, sbrA, arg0, arg1, arg3, arg4, dsN, BitVec.add_assoc,
    BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] at hm ⊢; sep_close hm)
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a02 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a02" ⟨"ff_aac_sbr_apply.L9a02", B.L9a02, some "ff_aac_sbr_apply.L9a02_1"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hPs, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, h9, h12, y, hK, hCy, hm⟩ := T.L9a02.mp hs
  clear hs
  have hkm : y.kx1 + y.m1 ≤ 64 := hCy.1.2.2.2.1
  have hPW : PsWF y.psc y.psh := hCy.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpl : y.psc.length = 764 := hPW.1
  have ha1 : isAligned 32 (t₀.regs.get64 .rsi) = true := hCy.2.1
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; have hPW' := PLift.up hPW; clear hK hCy hPW
  simp only [Mm, ApplyF, ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm h12
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hR := PLift.up (⟨hrsp, hrbp, h9, h12⟩ : _ ∧ _ ∧ _ ∧ _)
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
    y.psc =@ (t₀.regs.get64 .rsi + 343840#64), 4 ?@ (t₀.regs.get64 .rsi + 344604#64),
    133200 ?@ (t₀.regs.get64 .rsi + 344608#64), y.psh =@ (t₀.regs.get64 .rsi + 477808#64),
    76 ?@ (t₀.regs.get64 .rsi + 477876#64),
    19456 ?@ (t₀.regs.get64 .rsi + 509024#64), 19456 ?@ (t₀.regs.get64 .rsi + 528480#64), e.PsTab] as Rc hRc
  have hpsl : s₀.dmem.loadInt (t₀.regs.get64 .rsi + 343840#64) 4
      = some (Int.ofBytes ((y.psc.drop 0).take 4)) := by
    have h0 : (0 : Nat) = (t₀.regs.get64 .rsi + 343840#64 - (t₀.regs.get64 .rsi + 343840#64)).toNat := by
      rw [BitVec.sub_self, BitVec.toNat_zero]
    rw [h0]
    sep_mem hm
    all_goals first | rfl | (rw [hpl]; (try rw [BitVec.sub_self, BitVec.toNat_zero]); decide)
  have hRc' := PLift.up hRc
  clear hRc
  dsimp only
  simp only [B.L9a02]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at ({ R := Rc, psc := y.psc, psh := y.psh } : PsArgs) "ff_ps_apply" hPs]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try (have e := hRc'.down; subst e)
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, h9, h12, hpsl, BitVec.add_assoc] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (simp only [Option.isSome_some]; done)
  case vc4 =>
    obtain ⟨hrsp, hrbp, h9, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a85") ?_
    refine ⟨isSome_at L.L9a85, ?_, Or.inr ⟨?_, ?_⟩⟩
    rotate_left
    · simp only [lex_var] at hn ⊢; exact hn
    · simp only [lex_var]; decide
    rw [T.L9a85]
    refine ⟨ch, c0, hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, h12, sbrA, arg0, arg1, dsN,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd]; done)
    · simp only [Mm, ApplyF, ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm
  case vc6 =>
    obtain ⟨hrsp, hrbp, h9, h12⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a69") ?_
    refine ⟨isSome_at L.L9a69, ?_, Or.inr ⟨?_, ?_⟩⟩
    rotate_left
    · simp only [lex_var] at hn ⊢; exact hn
    · simp only [lex_var]; decide
    rw [T.L9a69]
    refine ⟨ch, c0, hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, h12, sbrA, arg0, arg1, dsN,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, BitVec.reduceAdd]; done)
    · simp only [Mm, ApplyF, ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm
  case vc10 =>
    obtain ⟨hrsp, hrbp, h9, h12⟩ := hR.down
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc,
        PsApplyF, PsApplyPre, CallPre, arg0, arg1, arg2]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc,
        PsApplyC, arg0, arg1, arg2, arg3]
      refine ⟨?_, ?_, hPW'.down, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al16 (syn_al32 _ _ ha1 (by decide)),
        syn_al16 (syn_al32 _ _ ha1 (by decide))⟩
      · simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast, BitVec.toNat_setWidth,
          BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      · exact ps_gate2 ‹some (Int.ofBytes _) = some _› ‹CondCode.z.interp _ = false›
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        AddrIndex.offset64_none, z, hrsp, hrbp, h9, h12, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd,
        BitVec.reduceAdd, Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.add_assoc, PsApplyPost, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      obtain ⟨h', hl, h6, hm2⟩ := ps_post_ex3 hm'
      clear hm'
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', -, h14', -⟩ := hsv
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a02_1]
      refine ⟨ch, c0, hC, ⟨hrsp', hrbp'⟩, ?_, ?_, ?_, { y with psh := h' }, hK'.down,
        ⟨ps_sbrwf_post hCy'.down.1 hl h6, hCy'.down.2⟩, ?_⟩
      · rw [hb']; try simp only [arg0]
      · rw [h12']; try simp only [sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h14']; try simp only [dsN]
      simp only [PsApplyF, Blocks, arg0, arg1, arg2, MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, h9, h12, BitVec.add_assoc, BitVec.reduceAdd] at hm2
      simp only [Mm, ApplyF]
      rw [show TabW { y with psh := h' } t₀ = TabW y t₀ from rfl, show OutW { y with psh := h' } t₀ = OutW y t₀ from rfl]
      simp only [ArrW, PsW, FrCs, FnW, AcW, ScW, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a02_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a02_1" ⟨"ff_aac_sbr_apply.L9a02_1", B.L9a02_1, some "ff_aac_sbr_apply.L9a50"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, y, hK, hCy, hm⟩ := T.L9a02_1.mp hs
  clear hs
  simp only [B.L9a02_1]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  left
  refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9a7d") ?_
  refine ⟨isSome_at L.L9a7d, ?_, Or.inr ⟨?_, ?_⟩⟩
  rotate_left
  · simp only [lex_var] at hn ⊢; exact hn
  · simp only [lex_var]; decide
  rw [T.L9a7d]
  exact ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, y, hK, hCy, hm⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a69 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a69" ⟨"ff_aac_sbr_apply.L9a69", B.L9a69, some "ff_aac_sbr_apply.L9a7d"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hMc, -⟩ := hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, hax, y, hK, hCy, hm⟩ := T.L9a69.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  simp only [Mm, ApplyF, ArrW, FrCs, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm hax h12
  rw [call_res k hSt] at hm
  simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd] at hm
  have hsl : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 176#64) 8) = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rsi + 509024#64).toInt)) := by
    sep_mem hm
    exact Eq.refl _
  sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 464#64), Reserve k (t₀.regs.get64 .rsp - 464#64),
    19456 ?@ (t₀.regs.get64 .rsi + 528480#64), 19456 ?@ (t₀.regs.get64 .rsi + 509024#64)] as Rc hRc
  have hRc' := PLift.up hRc
  clear hRc
  dsimp only
  simp only [B.L9a69]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen [MachineWP.call_proc_spec_at Rc "memcpy" hMc]
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.sub_sub_eight, BitVec.reduceAdd, BitVec.add_zero,
      Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp, and_self, hbx, h12, h14, hax, hsl]
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff]
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  all_goals try sep_mem hm
  case vc1 => simp only [hsl, Option.isSome_some]
  case vc2 =>
    rename_i v hv
    simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none, z, hrbp,
      Int64.toBitVec_neg_ofNat_norm, Nat.reducePow, Nat.reduceMod, Nat.reduceSub] at hv
    simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
      Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at hv
    rw [hsl, Option.some.injEq] at hv
    subst hv
    have hw : (BitVec.setWidth 64 (BitVec.setWidth 32 19456#64)).toNat = 19456 := by decide
    have hv8 := BitVec.ofInt_ofBytes_toBytes 64 8 rfl (t₀.regs.get64 .rsi + 509024#64)
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 2
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd]
      first | sep_mem hm | (simp -implicitDefEqProofs only [BitVec.toNat_ofNat]; decide) | trivial
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, hax, hsl, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd,
        Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        BitVec.add_assoc, Option.getD_some, hw, hv8]
      sep_mem hm
      sep_close hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true,
        ite_false, z, hrsp, hrbp, hax, hsl, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight, Nat.reduceAdd, BitVec.reduceAdd,
        Blocks, BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
        BitVec.add_assoc, Option.getD_some, hw, hv8] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have zc8 : ∀ (a : BitVec 64) (c : Nat), 8 ≤ c → c ≤ 2 ^ 64 →
          a - BitVec.ofNat 64 c + 8 = a - BitVec.ofNat 64 (c - 8) := by
        intro a c h h'; rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl]
        apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
      simp only [zc8, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', -, h14', -⟩ := hsv
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a7d]
      refine ⟨ch, c0, hC, ⟨hrsp', hrbp'⟩, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩
      · rw [hb']; simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, hbx]
      · rw [h12']; simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, h12, sbrA,
          arg1, BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h14']; simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_false, h14]
      have e := hRc'.down
      subst e
      simp only [Mm, ApplyF, ArrW, FrCs, Blocks, sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [call_res k hSt]
      simp only [BitVec.sub_sub_ofNat, Nat.reduceAdd]
      sep_close hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a7d (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a7d" ⟨"ff_aac_sbr_apply.L9a7d", B.L9a7d, some "ff_aac_sbr_apply.L9a85"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, hbx, h12, h14, y, hK, hCy, hm⟩ := T.L9a7d.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  have hR := PLift.up (⟨hrsp, hrbp, hbx, h12, h14⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [Mm, FrCs] at hm
  simp only [B.L9a7d]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      hbx, h12, h14] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at *
  all_goals try sep_mem hm
  all_goals try (refine ⟨?_, ?_⟩; rw [T.L9a85])
  all_goals try (obtain ⟨hrsp, hrbp, hbx, h12, h14⟩ := hR.down
                 refine ⟨ch, c0, hC, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_⟩)
  all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hbx, h12, h14,
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
  all_goals try (simp only [Mm, FrCs] at hm ⊢; sep_close hm)
  all_goals try var_step
  done

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a85 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85" ⟨"ff_aac_sbr_apply.L9a85", B.L9a85, some "ff_aac_sbr_apply.L9a85_1"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, h9, hbx, h12, h14, y, hK, hCy, hm⟩ := T.L9a85.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  have hR := PLift.up (⟨hrsp, hrbp, h9, hbx, h12, h14⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [Mm] at hm
  rw [res_args k hSt] at hm
  simp only [ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [B.L9a85]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hsp : ∀ a : BitVec 64, BitVec.setWidth 64 32#64 + (a - 488#64) = a - 456#64 := by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]; apply BitVec.eq_of_toNat_eq
    simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrs : ∀ a : BitVec 64, BitVec.setWidth 64 269664#64 + a = a + 269664#64 := by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      h9, hbx, h12, h14, Width.bytes, Width.bytesv, BitVec.add_assoc, arg0, arg1, sbrA] at *
  all_goals try simp only [hsp, hrs] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  all_goals (
    obtain ⟨hrsp, hrbp, h9, hbx, h12, h14⟩ := hR.down
    refine ⟨?_, by var_step⟩
    rw [T.L9a85_1]
    refine ⟨ch, c0, hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, h9, hbx, h12, h14,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, sbrA, arg0, arg1, arg3, arg4,
        BitVec.add_assoc, BitVec.reduceAdd, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]; done)
    simp only [MmS, SynArgs, c8, Mm, ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, dsN,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] at hm ⊢
    sep_close hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a85_1 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_1" ⟨"ff_aac_sbr_apply.L9a85_1", B.L9a85_1, some "ff_aac_sbr_apply.L9a85_2"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQ0, hQ1, -⟩ := hc
  have hQ := syn_qspec (x := x) hQ0 hQ1
  clear hQ0 hQ1
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, hbx, h15, h13, h12, h14, y, hK, hCy, hdi, hsi, hcx, hdx, h8, h9, hm⟩ :=
    T.L9a85_1.mp hs
  clear hs
  have hdy : dsN y = dsN x := by simp only [dsN, hK.2.2.2.1, hK.2.2.2.2.2.2.2]
  have hB : (1280 ?@ (t₀.regs.get64 .rsi + 558560#64) : Mem 64 → Prop)
      = 256 ?@ (t₀.regs.get64 .rsi + 558560#64) ⋆ (256 ?@ (t₀.regs.get64 .rsi + 558816#64)
        ⋆ 768 ?@ (t₀.regs.get64 .rsi + 559072#64)) := by
    rw [show (1280 : Nat) = 256 + (256 + 768) from rfl, Block.split _ 256 (256 + 768) (by decide),
      Block.split _ 256 768 (by decide)]
    simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
  have hB' := PLift.up hB; clear hB
  simp only [MmS, SynArgs] at hm
  rw [c8_div _ _ (syn_dsN_le x), res_qmf k (t₀.regs.get64 .rsp - 0x1e8#64) (by (try simp only [applyNeed] at hSt); bv_omega)] at hm
  simp only [ApplyF, ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
    hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
    BitVec.ofNat_eq_ofNat] at hm
  rw [hB'.down] at hm
  have hq := qv_carve (t₀.regs.get64 .rsi + 166432#64) (dsN x) y.d0.vOff
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
  rw [hq] at hm
  have hq' := PLift.up hq; clear hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (syn_dsN_le x) with hd | hd
  · rw [syn_win0 hd] at hm
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 496#64), Reserve (304 + k) (t₀.regs.get64 .rsp - 496#64),
      19456 ?@ (t₀.regs.get64 .rsi + 509024#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64),
      qmfVSize (dsN x) y.d0.vOff ?@ (t₀.regs.get64 .rsi + 166432#64),
      cell4 (t₀.regs.get64 .rsi + 180896#64) y.d0.vOff,
      (8192 >>> dsN x) ?@ t₀.regs.get64 .rcx, (2560 >>> dsN x) ?@ qmfWin (dsN x),
      4 ?@ lab "LCPI15_1", 16 ?@ lab "ps_mask2", 16 ?@ lab "ff_ps_neg",
      FnCell (t₀.regs.get64 .rsi + 559888#64) e.fs.qfs.negOdd64,
      FnCell (t₀.regs.get64 .rsi + 559912#64) e.fs.qfs.deintNeg,
      FnCell (t₀.regs.get64 .rsi + 559920#64) e.fs.qfs.deintBfly,
      FnCell y.fdsp e.fs.qfs.fmul, FnCell (y.fdsp + 48#64) e.fs.qfs.fmulAdd, e.Ctx y.synCtx, e.TxTab,
      c8 (t₀.regs.get64 .rsp - 488#64) (t₀.regs.get64 .rsi + 558560#64),
      c8 (t₀.regs.get64 .rsp - 480#64) (t₀.regs.get64 .rsi + 166432#64),
      c8 (t₀.regs.get64 .rsp - 472#64) (t₀.regs.get64 .rsi + 180896#64),
      Int.toBytes 4 (dsN x : Int) =@ (t₀.regs.get64 .rsp - 464#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    simp only [B.L9a85_1]
    vcgen [MachineWP.call_proc_spec_at
      ({ R := Rc, mdctBuf := t₀.regs.get64 .rsi + 558560#64, v0 := t₀.regs.get64 .rsi + 166432#64,
         vOff := t₀.regs.get64 .rsi + 180896#64, off := y.d0.vOff } : QmfArgs) "sbr_qmf_synthesis" hQ]
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    all_goals try subst s₀
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        Nat.reduceSub]
      sep_mem hm
      sep_close hm
    · obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hD0, -, -⟩, ha1, hsA0, ha3, ha4, -, -, -, -, hds, hneg, ⟨-, hus, hm2⟩, -, -⟩ := hCy
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv1, hv2, -⟩ := hD0
      simp only [sbrA, arg1, arg3, arg4] at ha1 hsA0 ha3 ha4
      simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfC, qmfWin, hd, Nat.one_ne_zero, ite_true, ite_false, Nat.reduceShiftRight, Int64.ofBitVec_toBitVec]
      exact ⟨by decide, trivial, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al32 _ _ ha1 (by decide),
        syn_al32 _ _ ha1 (by decide), ha3, ‹_›, hm2, hneg, hv1, hv2⟩
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have e := hRc'.down; subst e
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', h13', h14', h15'⟩ := hsv
      sep_pull hm' [VOffW (t₀.regs.get64 .rsi + 180896#64)] as F hF
      obtain ⟨v, hw1, hw2, hm2⟩ := voffw_cell hm'
      subst hF
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a85_2]
      refine ⟨ch, c0, hC, by rw [hrsp']; bv_omega, hrbp', ?_, ?_, ?_, ?_, ?_, y, hK, hCy, v, hw1, hw2, ?_⟩
      · rw [hb']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hbx, arg1]
      · rw [h15']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h15, arg0]
      · rw [h13']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h13, sbrA,
          BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h12']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12, sbrA,
          BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h14']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h14, dsN]
      simp only [Mm, ApplyF]
      rw [show ScW (y.setV0 v) t₀ = ScW y t₀ from rfl, show TabW (y.setV0 v) t₀ = TabW y t₀ from rfl,
        show AcW (y.setV0 v) t₀ = AcW y t₀ from rfl, show OutW (y.setV0 v) t₀ = OutW y t₀ from rfl,
        show FnW e (y.setV0 v) t₀ = FnW e y t₀ from rfl, show PsW (y.setV0 v) t₀ = PsW y t₀ from rfl]
      rw [res_args k hSt, BitVec.sub_sub_ofNat,
        res_qmf k (t₀.regs.get64 .rsp - 0x1c8#64 - 32#64) (by (try simp only [applyNeed] at hSt); bv_omega)]
      simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
        Args.setV0, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
        BitVec.ofNat_eq_ofNat]
      rw [hB'.down, hq'.down]
      have h8 : (8 ?@ (t₀.regs.get64 .rsp - 464#64) : Mem 64 → Prop)
          = 4 ?@ (t₀.regs.get64 .rsp - 464#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 460#64) := by
        rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide),
          syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide)]
      rw [h8]
      simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide), Nat.reduceSub] at hm2
      simp only [c4, cell4, FnCell, lab, dsN, qmfWin] at hm2 ⊢
      have hd0 := hd
      try simp only [dsN] at hd
      simp only [hd, ite_true, Nat.reduceShiftRight] at hm2 ⊢
      simp only [FrCs, hd0, BitVec.ofNat_eq_ofNat] at hm2 ⊢
      try simp only [PsW] at hm2 ⊢
      sep_close hm2
  · rw [syn_win1 hd] at hm
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 496#64), Reserve (304 + k) (t₀.regs.get64 .rsp - 496#64),
      19456 ?@ (t₀.regs.get64 .rsi + 509024#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64),
      qmfVSize (dsN x) y.d0.vOff ?@ (t₀.regs.get64 .rsi + 166432#64),
      cell4 (t₀.regs.get64 .rsi + 180896#64) y.d0.vOff,
      (8192 >>> dsN x) ?@ t₀.regs.get64 .rcx, (2560 >>> dsN x) ?@ qmfWin (dsN x),
      4 ?@ lab "LCPI15_1", 16 ?@ lab "ps_mask2", 16 ?@ lab "ff_ps_neg",
      FnCell (t₀.regs.get64 .rsi + 559888#64) e.fs.qfs.negOdd64,
      FnCell (t₀.regs.get64 .rsi + 559912#64) e.fs.qfs.deintNeg,
      FnCell (t₀.regs.get64 .rsi + 559920#64) e.fs.qfs.deintBfly,
      FnCell y.fdsp e.fs.qfs.fmul, FnCell (y.fdsp + 48#64) e.fs.qfs.fmulAdd, e.Ctx y.synCtx, e.TxTab,
      c8 (t₀.regs.get64 .rsp - 488#64) (t₀.regs.get64 .rsi + 558560#64),
      c8 (t₀.regs.get64 .rsp - 480#64) (t₀.regs.get64 .rsi + 166432#64),
      c8 (t₀.regs.get64 .rsp - 472#64) (t₀.regs.get64 .rsi + 180896#64),
      Int.toBytes 4 (dsN x : Int) =@ (t₀.regs.get64 .rsp - 464#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    simp only [B.L9a85_1]
    vcgen [MachineWP.call_proc_spec_at
      ({ R := Rc, mdctBuf := t₀.regs.get64 .rsi + 558560#64, v0 := t₀.regs.get64 .rsi + 166432#64,
         vOff := t₀.regs.get64 .rsi + 180896#64, off := y.d0.vOff } : QmfArgs) "sbr_qmf_synthesis" hQ]
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    all_goals try subst s₀
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        Nat.reduceSub]
      sep_mem hm
      sep_close hm
    · obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hD0, -, -⟩, ha1, hsA0, ha3, ha4, -, -, -, -, hds, hneg, ⟨-, hus, hm2⟩, -, -⟩ := hCy
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv1, hv2, -⟩ := hD0
      simp only [sbrA, arg1, arg3, arg4] at ha1 hsA0 ha3 ha4
      simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfC, qmfWin, hd, Nat.one_ne_zero, ite_true, ite_false, Nat.reduceShiftRight, Int64.ofBitVec_toBitVec]
      exact ⟨by decide, trivial, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al32 _ _ ha1 (by decide),
        syn_al32 _ _ ha1 (by decide), ha3, ‹_›, hm2, hneg, hv1, hv2⟩
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have e := hRc'.down; subst e
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', h13', h14', h15'⟩ := hsv
      sep_pull hm' [VOffW (t₀.regs.get64 .rsi + 180896#64)] as F hF
      obtain ⟨v, hw1, hw2, hm2⟩ := voffw_cell hm'
      subst hF
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a85_2]
      refine ⟨ch, c0, hC, by rw [hrsp']; bv_omega, hrbp', ?_, ?_, ?_, ?_, ?_, y, hK, hCy, v, hw1, hw2, ?_⟩
      · rw [hb']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hbx, arg1]
      · rw [h15']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h15, arg0]
      · rw [h13']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h13, sbrA,
          BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h12']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h12, sbrA,
          BitVec.add_assoc, BitVec.reduceAdd]
      · rw [h14']; try simp only [MachineData.pushRa, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, h14, dsN]
      simp only [Mm, ApplyF]
      rw [show ScW (y.setV0 v) t₀ = ScW y t₀ from rfl, show TabW (y.setV0 v) t₀ = TabW y t₀ from rfl,
        show AcW (y.setV0 v) t₀ = AcW y t₀ from rfl, show OutW (y.setV0 v) t₀ = OutW y t₀ from rfl,
        show FnW e (y.setV0 v) t₀ = FnW e y t₀ from rfl, show PsW (y.setV0 v) t₀ = PsW y t₀ from rfl]
      rw [res_args k hSt, BitVec.sub_sub_ofNat,
        res_qmf k (t₀.regs.get64 .rsp - 0x1c8#64 - 32#64) (by (try simp only [applyNeed] at hSt); bv_omega)]
      simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
        Args.setV0, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
        BitVec.ofNat_eq_ofNat]
      rw [hB'.down, hq'.down]
      have h8 : (8 ?@ (t₀.regs.get64 .rsp - 464#64) : Mem 64 → Prop)
          = 4 ?@ (t₀.regs.get64 .rsp - 464#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 460#64) := by
        rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide),
          syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide)]
      rw [h8]
      simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide), Nat.reduceSub] at hm2
      simp only [c4, cell4, FnCell, lab, dsN, qmfWin] at hm2 ⊢
      have hd0 := hd
      try simp only [dsN] at hd
      simp only [hd, Nat.one_ne_zero, ite_false, Nat.reduceShiftRight] at hm2 ⊢
      simp only [FrCs, hd0, BitVec.ofNat_eq_ofNat] at hm2 ⊢
      try simp only [PsW] at hm2 ⊢
      sep_close hm2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a85_2 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_2" ⟨"ff_aac_sbr_apply.L9a85_2", B.L9a85_2, some "ff_aac_sbr_apply.L9a85_3"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, hbx, h15, h13, h12, h14, y, hK, hCy, v, hw1, hw2, hm⟩ := T.L9a85_2.mp hs
  clear hs
  have hK' := PLift.up hK; have hCy' := PLift.up hCy; clear hK hCy
  have hW := PLift.up (⟨hw1, hw2⟩ : _ ∧ _); clear hw1 hw2
  have hR := PLift.up (⟨hrsp, hrbp, hbx, h15, h13, h12, h14⟩ : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
  simp only [Mm] at hm
  rw [res_args k hSt] at hm
  simp only [ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    BitVec.add_assoc, BitVec.reduceAdd] at hm
  simp only [B.L9a85_2]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hsp : ∀ a : BitVec 64, BitVec.setWidth 64 32#64 + (a - 488#64) = a - 456#64 := by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]; apply BitVec.eq_of_toNat_eq
    simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hrs : ∀ a : BitVec 64, BitVec.setWidth 64 269664#64 + a = a + 269664#64 := by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst s₀
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, BitVec.reduceAdd, BitVec.add_zero,
      BitVec.sub_sub_eight, Int64.toBitVec_neg_ofNat_norm, Int64.toBitVec_ofNat_norm, z, hrsp, hrbp,
      hbx, h15, h13, h12, h14, Width.bytes, Width.bytesv, BitVec.add_assoc, arg0, arg1, sbrA] at *
  all_goals try simp only [hsp, hrs] at *
  all_goals try simp only [BitVec.sub_add_ofNat_wrap, BitVec.sub_sub_ofNat, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_vals hm
  all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec] at *
  all_goals try sep_mem hm
  case vc11 =>
    obtain ⟨hrsp, hrbp, hbx, h15, h13, h12, h14⟩ := hR.down
    refine ⟨?_, by var_step⟩
    rw [T.L9a85_3]
    refine ⟨ch, c0, hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, y, hK'.down, hCy'.down, ?_, ?_, ?_, ?_, ?_, ?_, v, hW.down.1, hW.down.2, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hbx, h15, h13, h12, h14,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, sbrA, arg0, arg1, arg3, arg4,
        BitVec.add_assoc, BitVec.reduceAdd, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]; done)
    simp only [MmS, SynArgs, c8, Mm, ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, dsN,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] at hm ⊢
    sep_close hm
  case vc2 =>
    obtain ⟨hrsp, hrbp, hbx, h15, h13, h12, h14⟩ := hR.down
    left
    refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9b24") ?_
    refine ⟨isSome_at L.L9b24, ?_, Or.inr ⟨?_, ?_⟩⟩
    rotate_left
    · simp only [lex_var] at hn ⊢; exact hn
    · simp only [lex_var]; decide
    rw [T.L9b24]
    refine ⟨ch, c0, hC, ⟨?_, ?_⟩, y.setV0 v, hK'.down, applyc_setV0 hCy'.down hW.down.1 hW.down.2, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, hbx, h15, h13, h12, h14,
        BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Int64.ofBitVec_toBitVec, sbrA, arg0, arg1, arg3, arg4,
        BitVec.add_assoc, BitVec.reduceAdd, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat]; done)
    simp only [Mm]
    rw [res_args k hSt]
    simp only [MmS, SynArgs, c8, Mm, ApplyF, FrCs, FnW, AcW, FnCell, sbrA, dA, arg0, arg1, arg4, dsN,
        BitVec.sub_sub_ofNat, Nat.reduceAdd, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul] at hm ⊢
    sep_close hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a85_3 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_3" ⟨"ff_aac_sbr_apply.L9a85_3", B.L9a85_3, some "ff_aac_sbr_apply.L9a85_4"⟩ := by
  info_off
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hQ0, hQ1, -⟩ := hc
  have hQ := syn_qspec (x := x) hQ0 hQ1
  clear hQ0 hQ1
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, hbx, h15, h13, h12, h14, y, hK, hCy, hdi, hsi, hcx, hdx, h8, h9, v, hw1, hw2, hm⟩ :=
    T.L9a85_3.mp hs
  clear hs
  have hdy : dsN y = dsN x := by simp only [dsN, hK.2.2.2.1, hK.2.2.2.2.2.2.2]
  have hB : (1280 ?@ (t₀.regs.get64 .rsi + 558560#64) : Mem 64 → Prop)
      = 256 ?@ (t₀.regs.get64 .rsi + 558560#64) ⋆ (256 ?@ (t₀.regs.get64 .rsi + 558816#64)
        ⋆ 768 ?@ (t₀.regs.get64 .rsi + 559072#64)) := by
    rw [show (1280 : Nat) = 256 + (256 + 768) from rfl, Block.split _ 256 (256 + 768) (by decide),
      Block.split _ 256 768 (by decide)]
    simp only [BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
  have hB' := PLift.up hB; clear hB
  simp only [MmS, SynArgs, ApplyF] at hm
  rw [show ScW (y.setV0 v) t₀ = ScW y t₀ from rfl, show TabW (y.setV0 v) t₀ = TabW y t₀ from rfl,
    show AcW (y.setV0 v) t₀ = AcW y t₀ from rfl, show OutW (y.setV0 v) t₀ = OutW y t₀ from rfl,
    show FnW e (y.setV0 v) t₀ = FnW e y t₀ from rfl, show PsW (y.setV0 v) t₀ = PsW y t₀ from rfl] at hm
  rw [c8_div _ _ (syn_dsN_le x), res_qmf k (t₀.regs.get64 .rsp - 0x1e8#64) (by (try simp only [applyNeed] at hSt); bv_omega)] at hm
  simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
    Args.setV0, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
    BitVec.ofNat_eq_ofNat] at hm
  rw [hB'.down] at hm
  have hq := qv_carve (t₀.regs.get64 .rsi + 255200#64) (dsN x) y.d1.vOff
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hq
  rw [hq] at hm
  have hq' := PLift.up hq; clear hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (syn_dsN_le x) with hd | hd
  · rw [syn_win0 hd] at hm
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 496#64), Reserve (304 + k) (t₀.regs.get64 .rsp - 496#64),
      19456 ?@ (t₀.regs.get64 .rsi + 528480#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64),
      qmfVSize (dsN x) y.d1.vOff ?@ (t₀.regs.get64 .rsi + 255200#64),
      cell4 (t₀.regs.get64 .rsi + 269664#64) y.d1.vOff,
      (8192 >>> dsN x) ?@ t₀.regs.get64 .r8, (2560 >>> dsN x) ?@ qmfWin (dsN x),
      4 ?@ lab "LCPI15_1", 16 ?@ lab "ps_mask2", 16 ?@ lab "ff_ps_neg",
      FnCell (t₀.regs.get64 .rsi + 559888#64) e.fs.qfs.negOdd64,
      FnCell (t₀.regs.get64 .rsi + 559912#64) e.fs.qfs.deintNeg,
      FnCell (t₀.regs.get64 .rsi + 559920#64) e.fs.qfs.deintBfly,
      FnCell y.fdsp e.fs.qfs.fmul, FnCell (y.fdsp + 48#64) e.fs.qfs.fmulAdd, e.Ctx y.synCtx, e.TxTab,
      c8 (t₀.regs.get64 .rsp - 488#64) (t₀.regs.get64 .rsi + 558560#64),
      c8 (t₀.regs.get64 .rsp - 480#64) (t₀.regs.get64 .rsi + 255200#64),
      c8 (t₀.regs.get64 .rsp - 472#64) (t₀.regs.get64 .rsi + 269664#64),
      Int.toBytes 4 (dsN x : Int) =@ (t₀.regs.get64 .rsp - 464#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    simp only [B.L9a85_3]
    vcgen [MachineWP.call_proc_spec_at
      ({ R := Rc, mdctBuf := t₀.regs.get64 .rsi + 558560#64, v0 := t₀.regs.get64 .rsi + 255200#64,
         vOff := t₀.regs.get64 .rsi + 269664#64, off := y.d1.vOff } : QmfArgs) "sbr_qmf_synthesis" hQ]
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    all_goals try subst s₀
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        Nat.reduceSub]
      sep_mem hm
      sep_close hm
    · obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hD0, -⟩, ha1, hsA0, ha3, ha4, -, -, -, -, hds, hneg, ⟨-, hus, hm2⟩, -, -⟩ := hCy
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv1, hv2, -⟩ := hD0
      simp only [sbrA, arg1, arg3, arg4] at ha1 hsA0 ha3 ha4
      simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfC, qmfWin, hd, Nat.one_ne_zero, ite_true, ite_false, Nat.reduceShiftRight, Int64.ofBitVec_toBitVec]
      exact ⟨by decide, trivial, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al32 _ _ ha1 (by decide),
        syn_al32 _ _ ha1 (by decide), ha4, ‹_›, hm2, hneg, hv1, hv2⟩
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have e := hRc'.down; subst e
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', h13', h14', h15'⟩ := hsv
      sep_pull hm' [VOffW (t₀.regs.get64 .rsi + 269664#64)] as F hF
      obtain ⟨v', hw1', hw2', hm2⟩ := voffw_cell hm'
      subst hF
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a85_4]
      refine ⟨ch, c0, hC, by rw [hrsp']; bv_omega, hrbp', (y.setV0 v).setV1 v', hK,
        applyc_setV1 (applyc_setV0 hCy hw1 hw2) hw1' hw2', ?_⟩
      simp only [Mm, ApplyF]
      rw [show ScW ((y.setV0 v).setV1 v') t₀ = ScW y t₀ from rfl, show TabW ((y.setV0 v).setV1 v') t₀ = TabW y t₀ from rfl,
        show AcW ((y.setV0 v).setV1 v') t₀ = AcW y t₀ from rfl, show OutW ((y.setV0 v).setV1 v') t₀ = OutW y t₀ from rfl,
        show FnW e ((y.setV0 v).setV1 v') t₀ = FnW e y t₀ from rfl]
      rw [res_args k hSt, BitVec.sub_sub_ofNat,
        res_qmf k (t₀.regs.get64 .rsp - 0x1c8#64 - 32#64) (by (try simp only [applyNeed] at hSt); bv_omega)]
      simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
        Args.setV0, Args.setV1, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
        BitVec.ofNat_eq_ofNat]
      rw [hB'.down, hq'.down]
      have h8 : (8 ?@ (t₀.regs.get64 .rsp - 464#64) : Mem 64 → Prop)
          = 4 ?@ (t₀.regs.get64 .rsp - 464#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 460#64) := by
        rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide),
          syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide)]
      rw [h8]
      simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide), Nat.reduceSub] at hm2
      simp only [c4, cell4, FnCell, lab, dsN, qmfWin] at hm2 ⊢
      have hd0 := hd
      try simp only [dsN] at hd
      simp only [hd, ite_true, Nat.reduceShiftRight] at hm2 ⊢
      simp only [FrCs, hd0, BitVec.ofNat_eq_ofNat] at hm2 ⊢
      try simp only [PsW] at hm2 ⊢
      sep_close hm2
  · rw [syn_win1 hd] at hm
    sep_pull hm [8 ?@ (t₀.regs.get64 .rsp - 496#64), Reserve (304 + k) (t₀.regs.get64 .rsp - 496#64),
      19456 ?@ (t₀.regs.get64 .rsi + 528480#64),
      256 ?@ (t₀.regs.get64 .rsi + 558560#64), 256 ?@ (t₀.regs.get64 .rsi + 558816#64),
      qmfVSize (dsN x) y.d1.vOff ?@ (t₀.regs.get64 .rsi + 255200#64),
      cell4 (t₀.regs.get64 .rsi + 269664#64) y.d1.vOff,
      (8192 >>> dsN x) ?@ t₀.regs.get64 .r8, (2560 >>> dsN x) ?@ qmfWin (dsN x),
      4 ?@ lab "LCPI15_1", 16 ?@ lab "ps_mask2", 16 ?@ lab "ff_ps_neg",
      FnCell (t₀.regs.get64 .rsi + 559888#64) e.fs.qfs.negOdd64,
      FnCell (t₀.regs.get64 .rsi + 559912#64) e.fs.qfs.deintNeg,
      FnCell (t₀.regs.get64 .rsi + 559920#64) e.fs.qfs.deintBfly,
      FnCell y.fdsp e.fs.qfs.fmul, FnCell (y.fdsp + 48#64) e.fs.qfs.fmulAdd, e.Ctx y.synCtx, e.TxTab,
      c8 (t₀.regs.get64 .rsp - 488#64) (t₀.regs.get64 .rsi + 558560#64),
      c8 (t₀.regs.get64 .rsp - 480#64) (t₀.regs.get64 .rsi + 255200#64),
      c8 (t₀.regs.get64 .rsp - 472#64) (t₀.regs.get64 .rsi + 269664#64),
      Int.toBytes 4 (dsN x : Int) =@ (t₀.regs.get64 .rsp - 464#64)] as Rc hRc
    have hRc' := PLift.up hRc
    clear hRc
    simp only [B.L9a85_3]
    vcgen [MachineWP.call_proc_spec_at
      ({ R := Rc, mdctBuf := t₀.regs.get64 .rsi + 558560#64, v0 := t₀.regs.get64 .rsi + 255200#64,
         vOff := t₀.regs.get64 .rsi + 269664#64, off := y.d1.vOff } : QmfArgs) "sbr_qmf_synthesis" hQ]
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    rotate_left 3
    all_goals try subst s₀
    · try simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      sep_mem hm
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost]
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        Nat.reduceSub]
      sep_mem hm
      sep_close hm
    · obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hD0, -⟩, ha1, hsA0, ha3, ha4, -, -, -, -, hds, hneg, ⟨-, hus, hm2⟩, -, -⟩ := hCy
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv1, hv2, -⟩ := hD0
      simp only [sbrA, arg1, arg3, arg4] at ha1 hsA0 ha3 ha4
      simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfC, qmfWin, hd, Nat.one_ne_zero, ite_true, ite_false, Nat.reduceShiftRight, Int64.ofBitVec_toBitVec]
      exact ⟨by decide, trivial, syn_al16 (syn_al32 _ _ ha1 (by decide)), syn_al32 _ _ ha1 (by decide),
        syn_al32 _ _ ha1 (by decide), ha4, ‹_›, hm2, hneg, hv1, hv2⟩
    · simp only [MachineData.pushRa, Width.bytesv, Width.bytes, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
          hrsp, hrbp, hbx, h15, h13, h12, h14, hdi, hsi, hcx, hdx, h8, h9, BitVec.sub_sub_ofNat, BitVec.sub_sub_eight,
          Nat.reduceAdd, BitVec.reduceAdd, Blocks, BitVec.add_assoc, sbrA, arg0, arg1, arg2, arg3, arg4, arg5,
          QmfF, QmfData, QmfData', QmfArgCells, QmfFPost, qmfNeed, QmfPre, QmfPost, LeafPre, CallPre, CallPost] at hpost
      obtain ⟨hrsp', hrbp', hsv, hm'⟩ := hpost
      have e := hRc'.down; subst e
      try simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), Nat.reduceSub] at hrsp'
      obtain ⟨hb', h12', h13', h14', h15'⟩ := hsv
      sep_pull hm' [VOffW (t₀.regs.get64 .rsi + 269664#64)] as F hF
      obtain ⟨v', hw1', hw2', hm2⟩ := voffw_cell hm'
      subst hF
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨?_, by var_step⟩
      rw [T.L9a85_4]
      refine ⟨ch, c0, hC, by rw [hrsp']; bv_omega, hrbp', (y.setV0 v).setV1 v', hK,
        applyc_setV1 (applyc_setV0 hCy hw1 hw2) hw1' hw2', ?_⟩
      simp only [Mm, ApplyF]
      rw [show ScW ((y.setV0 v).setV1 v') t₀ = ScW y t₀ from rfl, show TabW ((y.setV0 v).setV1 v') t₀ = TabW y t₀ from rfl,
        show AcW ((y.setV0 v).setV1 v') t₀ = AcW y t₀ from rfl, show OutW ((y.setV0 v).setV1 v') t₀ = OutW y t₀ from rfl,
        show FnW e ((y.setV0 v).setV1 v') t₀ = FnW e y t₀ from rfl]
      rw [res_args k hSt, BitVec.sub_sub_ofNat,
        res_qmf k (t₀.regs.get64 .rsp - 0x1c8#64 - 32#64) (by (try simp only [applyNeed] at hSt); bv_omega)]
      simp only [ArrW, DArrW, DScW, OutW, CstW, DspW, FnW, Blocks, sbrA, dA, arg0, arg1, arg3, arg4,
        Args.setV0, Args.setV1, hdy, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, BitVec.sub_sub_ofNat,
        BitVec.ofNat_eq_ofNat]
      rw [hB'.down, hq'.down]
      have h8 : (8 ?@ (t₀.regs.get64 .rsp - 464#64) : Mem 64 → Prop)
          = 4 ?@ (t₀.regs.get64 .rsp - 464#64) ⋆ 4 ?@ (t₀.regs.get64 .rsp - 460#64) := by
        rw [show (8 : Nat) = 4 + 4 from rfl, Block.split _ 4 4 (by decide),
          syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide)]
      rw [h8]
      simp only [syn_subadd _ _ _ (by decide : 8 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 16 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 24 ≤ 496) (by decide), syn_subadd _ _ _ (by decide : 32 ≤ 496) (by decide),
        syn_subadd _ _ _ (by decide : 4 ≤ 464) (by decide), Nat.reduceSub] at hm2
      simp only [c4, cell4, FnCell, lab, dsN, qmfWin] at hm2 ⊢
      have hd0 := hd
      try simp only [dsN] at hd
      simp only [hd, Nat.one_ne_zero, ite_false, Nat.reduceShiftRight] at hm2 ⊢
      simp only [FrCs, hd0, BitVec.ofNat_eq_ofNat] at hm2 ⊢
      try simp only [PsW] at hm2 ⊢
      sep_close hm2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9a85_4 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9a85_4" ⟨"ff_aac_sbr_apply.L9a85_4", B.L9a85_4, some "ff_aac_sbr_apply.L9b24"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, hrsp, hrbp, y, hK, hCy, hm⟩ := T.L9a85_4.mp hs
  clear hs
  have hK' := PLift.up hK; clear hK
  simp only [Mm] at hm
  rw [show y.R = x.R from hK'.down.1] at hm
  have hm' := fpost_of hK'.down hCy.1 hm
  clear hm
  simp only [B.L9a85_4]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hsp : PLift (∀ a : BitVec 64, BitVec.setWidth 64 440#64 + (a - 488#64) = a - 48#64) := ⟨by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  vcgen
  all_goals try subst s₀
  left
  refine Table.ofLabels_at (l := "ff_aac_sbr_apply.L9b2b") ?_
  refine ⟨isSome_at L.L9b2b, ?_, Or.inr ⟨?_, ?_⟩⟩
  rotate_left
  · simp only [lex_var] at hn ⊢; exact hn
  · simp only [lex_var]; decide
  rw [T.L9b2b]
  refine ⟨hC, ?_, ?_, ?_⟩
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hsp.down]
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp]
  · simp only [FrCs] at hm'
    simp only [FrRaw]
    sep_close hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_L9b24 (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b24" ⟨"ff_aac_sbr_apply.L9b24", B.L9b24, some "ff_aac_sbr_apply.L9b2b"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨ch, c0, hC, ⟨hrsp, hrbp⟩, y, hK, hCy, hm⟩ := T.L9b24.mp hs
  clear hs
  have hK' := PLift.up hK; clear hK
  simp only [Mm] at hm
  rw [show y.R = x.R from hK'.down.1] at hm
  have hm' := fpost_of hK'.down hCy.1 hm
  clear hm
  simp only [B.L9b24]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  have hsp : PLift (∀ a : BitVec 64, BitVec.setWidth 64 408#64 + (a - 456#64) = a - 48#64) := ⟨by
    intro a; rw [BitVec.setWidth_eq, BitVec.add_comm]; apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega⟩
  vcgen
  all_goals try subst s₀
  refine ⟨?_, by var_step⟩
  rw [T.L9b2b]
  refine ⟨hC, ?_, ?_, ?_⟩
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hsp.down]
  · simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrbp]
  · simp only [FrCs] at hm'
    simp only [FrRaw]
    sep_close hm'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000 in
theorem blk_L9b2b (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.L9b2b" ⟨"ff_aac_sbr_apply.L9b2b", B.L9b2b, some "ff_aac_sbr_apply.done"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hC, hrsp, hrbp, hm⟩ := T.L9b2b.mp hs
  clear hs
  dsimp only
  simp only [B.L9b2b]
  have z : ∀ a : BitVec 64, a + 0 = a := fun a => BitVec.add_zero a
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, AddrIndex.offset64_none,
      Width.bytes, Width.bytesv, BitVec.reduceAdd, z, hrsp, hrbp, and_self] at *
  all_goals try simp only [BitVec.sub_add_ofNat_cancel, BitVec.sub_ofNat_add_eight, Nat.reduceAdd,
    Nat.reducePow, Nat.reduceSub, Nat.reduceLeDiff] at *
  all_goals try sep_mem hm
  case vc7 =>
    sep_vals hm
    refine ⟨?_, by var_step⟩
    rw [T.done]
    refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, BitVec.sub_zero,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
    simp only [applyNeed]
    rw [reserve_frame k hSt, frame_split]
    sep_close hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000 in
theorem blk_done (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)
    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : applyNeed k ≤ (t₀.regs.get64 .rsp).toNat) :
    BlockOb k e x ra t₀ "ff_aac_sbr_apply.done" ⟨"ff_aac_sbr_apply.done", B.done, some "ff_aac_sbr_apply.L9b36"⟩ := by
  info_off
  clear hc
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨hs, hn⟩ := hs₀
  obtain ⟨hrsp, hrbp, hsv, hm⟩ := T.done.mp hs
  clear hs
  dsimp only
  simp only [B.done]
  try (have p_hm : PLift _ := ⟨hm⟩; clear hm)
  try (have p_hm0 : PLift _ := ⟨hm0⟩; clear hm0)
  vcgen
  all_goals try (have hm := p_hm.down; clear p_hm)
  all_goals try (have hm0 := p_hm0.down; clear p_hm0)
  all_goals try subst_vars
  all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hrsp, hrbp, and_self]
  case vc1 =>
    simp only [MachineData.retAddr_eq, hrsp, Width.bytes, Option.isSome_map]
    sep_mem hm
  case vc2 =>
    rename_i a ha
    right
    refine ⟨?_, rfl, trivial, hsv, ?_⟩
    · revert ha
      simp only [MachineData.retAddr_eq, hrsp, Width.bytes]
      sep_mem hm
      simp only [Option.map_some, Option.some.injEq, Width.bits, BitVec.ofInt_ofBytes_toBytes 64 8 rfl,
        Int64.ofBitVec_toBitVec]
      exact fun h => h.symm
    · sep_close hm

end Kraken.Examples.Sbr.Apply
