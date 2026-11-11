import Kraken.InfoOff
import Kraken.X64.Examples.Sbr.Parse.ResetTable
import Kraken.X64.Examples.Sbr.Parse.ResetModel

/-!
# `sbr_reset`: the `av_log` calls of the failure paths (shard B)

At a call inside the body `rsp = rsp₀ - 0x578`; the callee's return slot and reservation are
carved off the top of the `reserve` atom (`Mm_callF`).
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
theorem reserve_le {m : Mem 64} {d : Nat} {r : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ Reserve d r ⋆ F) : d ≤ r.toNat :=
  Reserve.le_head h

/-- What `Mm` keeps beside a callee's return slot, reservation and `Ext`. -/
abbrev CallF (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) : Mem 64 → Prop :=
  Reserve 0x450 (t₀.regs.get64 .rsp - 0x578#64 - 8#64 - BitVec.ofNat 64 k) ⋆ Mx_call k e a ra t₀ st fr

/-- A callee's frame inside `Mm` (`k` bytes of the reservation, below the return slot). -/
theorem Mm_callF (k : Nat) (e : REnv) (a : RArgs) (ra : Int64) (t₀ : MachineData) (st : St)
    (fr : List UInt8) (hd : 8 + tlimNeed k ≤ (t₀.regs.get64 .rsp - 0x578#64).toNat) :
    Mm k e a ra t₀ st fr = 8 ?@ (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x578#64 - 8#64) ⋆ (e.Ext ⋆ CallF k e a ra t₀ st fr)) := by
  have hd8 : k ≤ (t₀.regs.get64 .rsp - 0x578#64 - BitVec.ofNat 64 8).toNat := by
    unfold tlimNeed at hd; bv_omega
  rw [Mm_call, Reserve_split 8 (tlimNeed k) _ (by omega)]
  have e1 : Reserve (tlimNeed k) (t₀.regs.get64 .rsp - 0x578#64 - BitVec.ofNat 64 8)
      = Reserve k (t₀.regs.get64 .rsp - 0x578#64 - 8#64)
        ⋆ Reserve 0x450 (t₀.regs.get64 .rsp - 0x578#64 - 8#64 - BitVec.ofNat 64 k) := by
    rw [show tlimNeed k = k + 0x450 by unfold tlimNeed; omega,
      Reserve_split k 0x450 _ hd8, Reserve_eq k _ hd8]
  rw [e1]
  simp only [CallF]
  ac_rfl

set_option maxRecDepth 100000 in
/-- The last `av_log` before `sbr_turnoff`. -/
theorem blk_L1d48 (k : Nat) (e : REnv) (hAv : AvLogSpec e.Ext k) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d48" ⟨"sbr_reset.L1d48", B.L1d48, some "sbr_reset.L1d4d"⟩ := by
  info_off
  measure_hb "L1d48"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩, hbx⟩ := T.L1d48.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1d48]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "av_log" hAv]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨hsp', hbp', ⟨hbx', h12', -, -, -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L1d4d.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [hbx', hbx]
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

set_option maxRecDepth 100000 in
/-- `av_log` (the error of `sbr_make_f_master`). -/
theorem blk_L1cff (k : Nat) (e : REnv) (hAv : AvLogSpec e.Ext k) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1cff" ⟨"sbr_reset.L1cff", B.L1cff, some "sbr_reset.L1d0b"⟩ := by
  info_off
  measure_hb "L1cff"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L1cff.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1cff]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "av_log" hAv]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨hsp', hbp', ⟨-, h12', -, -, h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L1d0b.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h15', h15]
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

set_option maxRecDepth 100000 in
/-- `av_log` (the errors of `sbr_make_f_derived`). -/
theorem blk_L1d2a (k : Nat) (e : REnv) (hAv : AvLogSpec e.Ext k) (a : RArgs) (ra : Int64)
    (t₀ : MachineData) :
    BlockOb k e a ra t₀ "sbr_reset.L1d2a" ⟨"sbr_reset.L1d2a", B.L1d2a, some "sbr_reset.L1d31"⟩ := by
  info_off
  measure_hb "L1d2a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨hs, hn⟩ := hs₀
    obtain ⟨⟨hC, ⟨hrsp, hrbp⟩, h12, h15, st, fr, hM, hsp, hfm, hF, hm⟩, hdi⟩ := T.L1d2a.mp hs
    clear hs
    have hd := reserve_le (focus (Mm_reserve ..) hm)
    rw [Mm_callF _ _ _ _ _ _ _ hd] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x578#64 - 8#64 := by
      rw [hrsp]
    simp only [B.L1d2a]
    vcgen [MachineWP.call_proc_spec_at (CallF k e a ra t₀ st fr) "av_log" hAv]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [e8]; exact hpush _
    · rw [e8] at hpost
      obtain ⟨hsp', hbp', ⟨-, h12', -, -, h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨T.L1d31.mpr ⟨hC, ⟨?_, ?_⟩, ?_, ?_, st, fr, hM, hsp, hfm, hF, ?_⟩, by var_step⟩
      · rw [hsp']; bv_omega
      · rw [hbp', hrbp]
      · rw [h12', h12]
      · rw [h15', h15]
      · show Mm k e a ra t₀ st fr s'.dmem
        rw [Mm_callF _ _ _ _ _ _ _ hd]; exact hm'

end Kraken.Examples.Sbr.Reset
