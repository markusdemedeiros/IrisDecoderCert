import Kraken.X64.Examples.Sbr.Parse.UsacSpec

/-!
# `ff_aac_sbr_config_usac`: the proof

`sbr_turnoff(sbr)` (l.58-68): eight stores and `return 0`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

/-- The state after `sbr_turnoff`. -/
def cfgSt (st : USt) : USt :=
  { st with x := st.x.turnoff, h := st.h.turnoff, u := 0#32,
            sp := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff] }

omit [CodeEnv] in
theorem cfg_out (A : UA) (hm : MI (A.2.x, A.2.h)) (hs : SpOk A.2) :
    (cfgSt A.2).x = A.2.x.turnoff ∧ ((cfgSt A.2).x, (cfgSt A.2).h) = stOff (A.2.x, A.2.h)
      ∧ MI ((cfgSt A.2).x, (cfgSt A.2).h) ∧ SpOk (cfgSt A.2) ∧ UKeep A.2.x (cfgSt A.2).x := by
  refine ⟨rfl, rfl, (mi_turnoff (s := (A.2.x, A.2.h)) hm.1).1, ?_, ?_⟩
  · obtain ⟨-, -, -, hlb, hl⟩ := hs
    exact ⟨rfl, rfl, rfl, hlb, hl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

abbrev ctable (A : UA) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "ff_aac_sbr_config_usac", s => s = t₀ ∧ ConfigPre A ra t₀
  | "ff_aac_sbr_config_usac.done", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32 ∧ MI (A.2.x, A.2.h) ∧ SpOk A.2
      ∧ (s.dmem =⋆ RetCell ra (t₀.regs.get64 .rsp)
          ⋆ (Reserve 0 (t₀.regs.get64 .rsp) ⋆ (UF A.1 (cfgSt A.2) ⋆ A.1.R)))
  | _, _ => False

abbrev CBlockOb (A : UA) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt cbody l = some blk → ∀ n : Nat,
    ⦃ fun s => ctable A ra t₀ l s ∧ (fun _ _ => 0) l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => ctable A ra t₀ l' s ∧ (fun _ _ => 0) l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt cbody l').isSome
          ∧ ctable A ra t₀ l' s ∧ Program.EdgeLt cbody (fun _ _ => 0) l n l' s) a s
        ∨ (a = ra ∧ ConfigPost A ra t₀ s) ⦄

omit [CodeEnv] in
theorem merge44 (a b : BitVec 64) (hb : b = a + 4#64) (v w : BitVec 32) (R : Mem 64 → Prop) :
    (Int.toBytes 4 v.toInt =@ a ⋆ (Int.toBytes 4 w.toInt =@ b ⋆ R))
      = ((Int.toBytes 4 v.toInt ++ Int.toBytes 4 w.toInt) =@ a ⋆ R) := by
  rw [← Std.ExtHashMap.sep_assoc, Val.append_eq _ _ a b (by rw [hb, Int.toBytes_length])
    (by simp [Int.toBytes_length])]

omit [CodeEnv] in
theorem sp6 {l : List UInt8} (h : l.length = 6) :
    ∃ b0 b1 b2 b3 b4 b5, l = [b0, b1, b2, b3, b4, b5] := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5], _ => exact ⟨b0, b1, b2, b3, b4, b5, rfl⟩

theorem cblk_entry (A : UA) (ra : Int64) (t₀ : MachineData) :
    CBlockOb A ra t₀ "ff_aac_sbr_config_usac" := by
  cfg_block
  measure_hb "cfg_entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hm, hmi, hsp, hc⟩, hn⟩ := hs₀
    simp only [UF, SHW, TWc, DSc, DRaw, AcU, GbU, RdU, sA, dAc, BitVec.add_assoc, BitVec.reduceAdd,
      Nat.reduceMul, Nat.reduceAdd] at hm
    rw [merge44 (A.1.c + 166180#64) (A.1.c + 166184#64) (by bv_omega)] at hm
    obtain ⟨b0, b1, b2, b3, b4, b5, hsp6⟩ := sp6 hsp.1
    rw [hsp6] at hm
    simp only [List.take, List.drop] at hm
    have p_hm : PLift _ := ⟨hm⟩; clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, hc]
    all_goals try simp only [BitVec.add_zero]
    all_goals try sep_mem hm
    case vc9 =>
      refine ⟨⟨trivial, trivial, by simp, by simp, hmi, hsp, ?_⟩, Nat.le_refl _⟩
      simp only [UF, SHW, TWc, DSc, DRaw, AcU, GbU, RdU, sA, dAc, BitVec.add_assoc,
        BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd, cfgSt, Args.turnoff]
      rw [merge44 (A.1.c + 166180#64) (A.1.c + 166184#64) (by bv_omega)]
      simp only [c4, cell4, Hid.turnoff, List.take, List.drop, BitVec.toInt_zero] at hm ⊢
      simp only [BitVec.reduceSetWidth, BitVec.reduceToInt, Int.reduceNeg] at hm ⊢
      have e1 : Int.toBytes 4 (-1) = [255, 255, 255, 255] := by decide
      have e2 : Int.toBytes 2 (-1) = [255, 255] := by decide
      have e3 : Int.toBytes 8 0 = Int.toBytes 4 0 ++ Int.toBytes 4 0 := by decide
      have e4 : Int.toBytes 4 ((32 : Nat) : Int) = Int.toBytes 4 32 := rfl
      have e5 : Int.toBytes 4 ((0 : Nat) : Int) = Int.toBytes 4 0 := rfl
      rw [e1, e2, e3] at hm
      rw [e4, e5]
      sep_close hm

theorem cblk_done (A : UA) (ra : Int64) (t₀ : MachineData) :
    CBlockOb A ra t₀ "ff_aac_sbr_config_usac.done" := by
  cfg_block
  measure_hb "cfg_done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hsp, hbp, hsv, hax, hmi, hspo, hm⟩, hn⟩ := hs₀
    have hpost : s₀.dmem =⋆ 8 ?@ t₀.regs.get64 .rsp ⋆ (Reserve 0 (t₀.regs.get64 .rsp)
        ⋆ (UF A.1 (cfgSt A.2) ⋆ A.1.R)) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    generalize Reserve 0 (t₀.regs.get64 .rsp) ⋆ (UF A.1 (cfgSt A.2) ⋆ A.1.R) = Q at hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by grind_cells'
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
    obtain ⟨-, hst, hmi', hsp', hk⟩ := cfg_out A hmi hspo
    refine ⟨rfl, cfgSt A.2, hst, hmi', hsp', hk, ?_, ?_⟩
    · exact hax
    · exact ⟨by rw [hsp]; rfl, hbp, hsv, hpost⟩

/-- **`ff_aac_sbr_config_usac`**: `sbr_turnoff`, the model's `Config` step. -/
theorem configSpec_holds (hpl : Program.PlacedIn cbody) : ConfigSpec := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := cbody) ctable ConfigPost
    (hblocks := ?_) (hpre := fun A ra t h => ⟨rfl, h⟩) (hpost := fun _ _ _ _ h => h)
  intro A ra t₀ l blk hblk
  have hmem := Program.isSome_blockAt cbody l
  cfg_view hblk as hview
  rw [hblk, hview] at hmem
  replace hmem := hmem.symm
  clear hview
  simp only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
    List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
  obtain rfl | rfl := hmem
  · exact cblk_entry A ra t₀ blk hblk
  · exact cblk_done A ra t₀ blk hblk

end Kraken.Examples.Sbr.Usac
