import Kraken.X64.Examples.Sbr.Parse.PsBlkT1Lib
import Kraken.X64.Examples.Sbr.Parse.PsBlkHNLib

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- The `iid` check failed: `av_log`, then `r15d = bits_left`, `rbx = ps`, to `0x1479`. -/
theorem blk_L10d6 (k : Nat) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L10d6" := by
  cfg_block
  measure_hb "L10d6"
    intro n
    simp only [tab_L10d6, var_L10d6]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, h68, hR⟩, hn⟩ := hs₀
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
      pnorm
      simp only [e1]
      exact Fr_f_isSome hm hf 0x60 8 (by omega)
    case vc2 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e48]; exact hpush _
      · rw [e48] at hpost
        obtain ⟨hsp', hbp', -, hm'⟩ := hpost
        have hm'' : s'.dmem =⋆ Fr k Ext x ra t₀ f c x.idx := (congrFun hF s'.dmem).mpr hm'
        have ea : s'.regs.get64 .rbp + 18446744073709551572#64
            = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x74 := by
          rw [hbp', hbp]; exact fr_addr _ 44 (by omega) (by omega)
        have eb : s'.regs.get64 .rbp + 18446744073709551560#64
            = t₀.regs.get64 .rsp - 0xa8#64 + BitVec.ofNat 64 0x68 := by
          rw [hbp', hbp]; exact fr_addr _ 56 (by omega) (by omega)
        have La := Fr_f_load hm'' hf 0x74 4 (by omega)
        have Lb := Fr_f_load hm'' hf 0x68 8 (by omega)
        rw [← ea] at La
        rw [← eb] at Lb
        vcgen
        all_goals try call_simp
        all_goals try dsimp only at *
        all_goals try t1norm at *
        all_goals try simp only [La, Lb, Option.some.injEq, Option.isSome_some] at *
        all_goals try subst_vars
        t1_jump "ff_ps_read_data.L1479"
        refine ⟨⟨c, f, ⟨hC, ⟨?_, by t1r; rw [hbp', hbp], hf, hP, hbl, h08, hid⟩, hm''⟩,
          by t1r; exact h68, hR⟩, by t1r; simp only [BitVec.setWidth_32_64_32]; exact hbl⟩
        t1r
        rw [hsp', BitVec.sub_add_ofNat_cancel _ _ _ (by omega) (by omega)]

set_option maxRecDepth 20000 in
/-- The `icc` check of the extra envelope failed: `av_log`, to `0x1479` (`rbx`, `r15` kept). -/
theorem blk_L132a (k : Nat) (Ext : Mem 64 → Prop) (hAv : AvLogSpec Ext k) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L132a" := by
  cfg_block
  measure_hb "L132a"
    intro n
    simp only [tab_L132a, var_L132a]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨c, f, ⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, hbx, hR⟩, h15⟩, hn⟩ := hs₀
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
      pnorm
      simp only [e1]
      exact Fr_f_isSome hm hf 0x60 8 (by omega)
    case vc2 =>
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
          ?_, hR⟩, ?_⟩
        · (try t1r)
          rw [hsp', BitVec.sub_add_ofNat_cancel _ _ _ (by omega) (by omega)]
        · (try t1r); rw [hbx']; first | exact hbx | (t1r; exact hbx)
        · (try t1r); rw [h15']; first | exact h15 | (t1r; exact h15)

end Kraken.Examples.Sbr.Ps
