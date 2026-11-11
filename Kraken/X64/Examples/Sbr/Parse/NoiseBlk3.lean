import Kraken.X64.Examples.Sbr.Parse.NoiseFrame

/-!
# `read_sbr_noise`: the error path (`av_log`) and the copy of the last row
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L6667 (k : Nat) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k)
    (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6667" := by
  cfg_block
  measure_hb "L6667"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, i, hi, hm⟩, hn⟩ := hs₀
    have hL := LcL.of hm hR.2.1
    have hav := T_ld_av hm
    have pR : PLift _ := ⟨hR⟩
    obtain ⟨F, hF⟩ := T_ext k Ext x ra t₀ (Loc x t₀) (Saved t₀) i
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hR.1, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e60 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 0x60#64 := by
      rw [hR.1]; show _ - 0x58#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      nnorm
      simp only [hL.ac, Option.isSome_some]
    case vc2 =>
      nnorm
      rename_i v hv
      simp only [hL.ac, Option.some.injEq] at hv
      subst hv
      simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hav, Option.isSome_some]
    case vc3 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e60]; exact hpush _
      · rw [e60] at hpost
        obtain ⟨hsp', hbp', -, hm'⟩ := hpost
        have hmT : s'.dmem =⋆ T k Ext x ra t₀ (Loc x t₀) (Saved t₀) i :=
          (congrFun hF s'.dmem).mpr hm'
        vcgen
        all_goals try dsimp only [reduceTable, reduceVar] at *
        all_goals try subst_vars
        left
        apply Table.ofLabels_at
        dsimp only [reduceTable, reduceVar]
        refine ⟨by decide, ⟨⟨hC, ?_, ?_, i, hi, T_blank hmT⟩, ?_⟩, Or.inr ⟨rfl, by decide +kernel⟩⟩ <;>
          try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        · rw [hsp']; bv_omega
        · rw [hbp']; exact pR.down.2.1
        · right; rfl

theorem blk_L6694 (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_noise.L6694" := by
  cfg_block
  measure_hb "L6694"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨⟨hC, hsp, hbp, i, hi, hm⟩, h9, h8, hax⟩, hn⟩ := hs₀
    have hnn : x.nn ≤ 2 := hC.1
    have p8 : PLift _ := ⟨h8⟩
    have p9 : PLift _ := ⟨h9⟩
    have pax : PLift _ := ⟨hax⟩
    have psp : PLift _ := ⟨hsp⟩
    have pbp : PLift _ := ⟨hbp⟩
    have hz := Kraken.Examples.Sbr.Dtdf.zx_nat x.nn (by omega)
    have h5 := lea5 x.nn (by omega)
    have o1 : (t₀.regs.get64 .rcx + BitVec.ofNat 64 (5 * x.nn) + 88660#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * x.nn + 4 := by simp only [arg3]; bv_omega
    have o2 : (t₀.regs.get64 .rcx + 88660#64 - (arg3 t₀ + 0x15a50#64)).toNat = 4 := by
      simp only [arg3]; bv_omega
    have o3 : (t₀.regs.get64 .rcx + BitVec.ofNat 64 (5 * x.nn) + 88656#64
        - (arg3 t₀ + 0x15a50#64)).toNat = 5 * x.nn := by simp only [arg3]; bv_omega
    have o4 : (t₀.regs.get64 .rcx + 88656#64 - (arg3 t₀ + 0x15a50#64)).toNat = 0 := by
      simp only [arg3]; bv_omega
    have hl1 := T_ld_nfq hm (t₀.regs.get64 .rcx + BitVec.ofNat 64 (5 * x.nn) + 88660#64) 1
      (by rw [o1]; omega)
    have hl2 := T_ld_nfq hm (t₀.regs.get64 .rcx + 88660#64) 1 (by rw [o2]; omega)
    have hst1 := fun v => T_st_nfq hm (t₀.regs.get64 .rcx + 88660#64) 1 (by rw [o2]; omega) v
    have hl3 := fun v => T_ld_nfq (hst1 v)
      (t₀.regs.get64 .rcx + BitVec.ofNat 64 (5 * x.nn) + 88656#64) 4 (by rw [o3]; omega)
    have hl4 := fun v => T_ld_nfq (hst1 v) (t₀.regs.get64 .rcx + 88656#64) 4 (by rw [o4]; omega)
    have hfin := fun v w => T_st_nfq (hst1 v) (t₀.regs.get64 .rcx + 88656#64) 4
      (by rw [o4]; omega) w
    have P : PLift _ := ⟨hfin⟩
    clear hst1 hfin hm o1 o2 o3 o4
    vcgen
    all_goals try subst_vars
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals nnorm
    all_goals try simp only [h8, h9, hz, h5] at *
    case vc1 => exact hl1
    case vc2 => exact hl2
    case vc3 => exact hl3 _
    case vc4 => exact hl4 _
    case vc5 =>
      refine ⟨⟨⟨hC, ?_, ?_, i, hi, P.down _ _⟩, ?_⟩, Nat.le.refl⟩ <;>
        try simp only [RetV, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact psp.down
      · exact pbp.down
      · left; rw [pax.down]; rfl

end Kraken.Examples.Sbr.Noise
