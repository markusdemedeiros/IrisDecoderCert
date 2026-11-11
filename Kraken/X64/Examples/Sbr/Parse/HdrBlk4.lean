import Kraken.X64.Examples.Sbr.Parse.HdrEnd

/-!
# `read_sbr_header`: the block obligations of the call and the epilogue

`L1054` tests `bs_reset` before the call; `L105a` calls `sbr_make_f_tablelim` (in
`HdrCall`); `L1062` restores `gb`; `L1065` computes the return value and pops; `done` returns.
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

omit [CodeEnv] in
theorem M_ret {k : Nat} {x : HArgs} {ra : Int64} {t₀ : MachineData} {Fm : Mem 64 → Prop}
    {st : HSt} {Tl : Mem 64 → Prop} :
    M k x ra t₀ Fm st Tl = RetCell ra (t₀.regs.get64 .rsp) ⋆ Mt k x t₀ Fm st Tl x.R := by
  simp only [M, MU, Mt, MtU, Rest]; ac_rfl

theorem blk_L1054 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.L1054" := by
  cfg_block
  measure_hb "L1054"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, i, sp, amp, lb, lg, ip, sm, hB, hA, hSB, ⟨hL, hne⟩, hm⟩, hn⟩ := hs₀
    have hld := M_ld_reset hm
    have hE : rsOf x sp ≠ 0#32 → s₀.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
        (St i sp amp (rsOf x sp) lb lg ip sm)
        (TlOut TlT TlT' x t₀ (St i sp amp (rsOf x sp) lb lg ip sm)) := by
      intro h
      rw [TlOut, if_neg (fun hc => h hc.2)]
      exact hm
    have hRh : ∀ s : MachineData, s = s₀ → Rs x t₀ s := fun _ h => h ▸ hR
    obtain ⟨hrdi, hrsi, hrsp, hrbp, hrest⟩ := hR
    simp only [arg0] at hld
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try simp only [hrdi, hld, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl, CondCode.interp,
      StatusFlags.from_result, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff,
      BitVec.reduceSetWidth] at *
    · rename_i hz
      have hne0 : rsOf x sp ≠ 0#32 := fun h => by
        simp only [rsOf] at h; rw [h] at hz; revert hz; decide
      left
      refine ⟨"read_sbr_header.L1065", rfl, by decide, ⟨hC, ?_, ?_, St i sp amp (rsOf x sp) lb lg ip sm,
        ⟨rfl, rfl, hA, hSB, rfl, hL, hB⟩, hE hne0⟩, Or.inr ⟨by trivial, by decide⟩⟩
      · obtain ⟨_, _, hsp, hbp, hbx, _, h12, h13, h15⟩ := hRh _ rfl
        simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact ⟨hsp, hbp, hbx, h12, h13, h15⟩
      · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact (hRh _ rfl).2.1
    · rename_i hz
      have h0 : rsOf x sp = 0#32 := by
        simp only [rsOf]; revert hz; generalize (if sp = x.sp then x.reset else 1#32) = v
        intro hz; simpa using hz
      exact ⟨⟨hC, ⟨trivial, hrsi, hrsp, hrbp, hrest⟩, i, sp, amp, lb, lg, ip, sm, hB, hA, hSB,
        ⟨hL, hne, h0⟩, hm⟩, trivial⟩

theorem blk_L1062 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.L1062" := by
  cfg_block
  measure_hb "L1062"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hr14, st, hO, hc, hm⟩, hn⟩ := hs₀
    have hE : s₀.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp)) st (TlOut TlT TlT' x t₀ st) := by
      rw [TlOut, if_pos hc]; exact hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    exact ⟨⟨hC, hR, hr14, st, hO, hE⟩, Nat.le_refl 0⟩

theorem blk_L1065 (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.L1065" := by
  cfg_block
  measure_hb "L1065"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hrsi, st, hO, hm⟩, hn⟩ := hs₀
    have hli := M_ld_i hm
    obtain ⟨p1, p2, p3⟩ := M_pop _ hm
    have hF := M_forget hC.1 hm
    obtain ⟨hrsp, hrbp, hrbx, h12, h13, h15⟩ := hR
    simp only [arg1] at hli
    have a1 : BitVec.setWidth 64 16#64 + (t₀.regs.get64 .rsp - 40#64) = t₀.regs.get64 .rsp - 0x18#64 := by
      rw [BitVec.setWidth_eq]; bv_omega
    have a2 : t₀.regs.get64 .rsp - 0x18#64 + 8#64 = t₀.regs.get64 .rsp - 0x10#64 := by bv_omega
    have a3 : t₀.regs.get64 .rsp - 0x10#64 + 8#64 = t₀.regs.get64 .rsp - 0x8#64 := by bv_omega
    have a4 : t₀.regs.get64 .rsp - 0x8#64 + 8#64 = t₀.regs.get64 .rsp := by bv_omega
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at *
    all_goals try simp only [hrsi, hrsp, hrbp, hrbx, hli] at *
    all_goals try simp only [a1, a2, a3, a4, p1, p2, p3, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 32 4 rfl] at *
    refine ⟨⟨trivial, trivial, ⟨trivial, h12, h13, trivial, h15⟩, st, hdrOut_of hO ?_, hF⟩, Nat.le_refl 0⟩
    simp only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Nat.reduceLeDiff]

theorem blk_done (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k TlT TlT' TlC x ra t₀ "read_sbr_header.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hsp, hbp, hsv, st, hO, hm⟩, hn⟩ := hs₀
    rw [M_ret] at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length 8 _) (by omega)
    have hpost := Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right
    refine ⟨rfl, ?_⟩
    exact ⟨by rw [hsp]; rfl, hbp, hsv, st, hO, hpost⟩

end Kraken.Examples.Sbr.Hdr
