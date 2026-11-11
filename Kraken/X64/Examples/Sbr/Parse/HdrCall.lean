import Kraken.X64.Examples.Sbr.Parse.HdrEnd

/-!
# `read_sbr_header`: the call of `sbr_make_f_tablelim`

`L105a` saves `gb` in `r14` and calls `sbr_make_f_tablelim(sbr)` under its contract `TlimSpec`:
the callee is given the cell `bs_limiter_bands`, the footprint `TlT sbr` and the frame `Fc` of
everything else, and its reservation is the return slot at `r - 0x30` with the `k` bytes below.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Hdr

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm
open Kraken.Examples.Sbr.HdrLib

/-- What the callee does not own. -/
abbrev Fc (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt) :
    Mem 64 → Prop :=
  SbX_lb (arg0 t₀) (usacOf t₀) st ⋆ (GbW (arg1 t₀) x st.i ⋆ (Blocks [(x.buf, x.L)] ⋆ (Fm ⋆ Rest x.R ra t₀)))

omit [CodeEnv] in
theorem M_tl (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop)
    (st : HSt) (Tl : Mem 64 → Prop) :
    M k x ra t₀ Fm st Tl = 8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ (cell4 (arg0 t₀ + 0x2c#64) st.lb ⋆ (Tl ⋆ Fc x ra t₀ Fm st))) := by
  simp only [M, MU, MtU, Fc]
  rw [SbW_lb]
  ac_rfl

theorem blk_L105a (k : Nat) (_hk : k ≤ 2 ^ 32) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (htl : TlimSpec TlT TlT' TlC k) (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.L105a" := by
  cfg_block
  measure_hb "L105a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, hB, hA, hSB, ⟨hL, hne, h0⟩, hm⟩, hn⟩ := hs₀
    have hsx : sp = x.sp ∧ x.reset = 0#32 := by
      simp only [rsOf] at h0
      by_cases h : sp = x.sp
      · simp only [h, ↓reduceIte] at h0; exact ⟨h, h0⟩
      · simp [h] at h0
    have htc : TlC lb (arg0 t₀) :=
      hC.2.2.2.2.2 hsx.2 (hsx.1 ▸ hA.2.1) lb hL.1 hne
    rw [M_tl] at hm
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrbx, hr8, h12, h13, h15⟩ := hR
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hrsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e48 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 48#64 := by
      rw [hrsp]; show _ - 40#64 - 8#64 = _; bv_omega
    have e40 : t₀.regs.get64 .rsp - 48#64 + (8 : BitVec 64) = t₀.regs.get64 .rsp - 40#64 := by
      bv_omega
    vcgen [MachineWP.call_proc_spec_at (Fc x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
      (St i sp amp (rsOf x sp) lb lg ip sm), lb) "sbr_make_f_tablelim" htl]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
    · rw [hrdi, e48]; exact hpush _
    · rw [hrdi]; exact htc
    · obtain ⟨hsp', hbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      rw [hrdi, e48] at hm'
      refine ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, St i sp amp (rsOf x sp) lb lg ip sm,
        ⟨rfl, rfl, hA, hSB, rfl, hL, hB⟩, ⟨hne, h0⟩, ?_⟩, Nat.le_refl 0⟩
      · rw [hsp', e48, e40]
      · rw [hbp', hrbp]
      · rw [hbx', hrbx]
      · rw [h12', h12]
      · rw [h13', h13]
      · rw [h15', h15]
      · rw [h14', hrsi]
      · exact (congrFun (M_tl k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp (rsOf x sp) lb lg ip sm) (TlT' lb (arg0 t₀))) _).mpr hm'
    · exact hld

end Kraken.Examples.Sbr.Hdr
