import Kraken.X64.Examples.Sbr.Parse.UsacBlk17
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the header's start

`indep_flag` into its local (`LocR` becomes `LocI`), the branch on it. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The local of `indep_flag`, raw and set. -/
theorem um_split_loc (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Sg : Mem 64 → Prop)
    (st : USt) (iv : BitVec 32) :
    ∃ R, Split (4 ?@ (t₀.regs.get64 .rsp - 0x34#64)) R
        (UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) Sg st)
      ∧ Split (cell4 (t₀.regs.get64 .rsp - 0x34#64) iv) R
        (UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st) := by
  simp only [UM, LocR, LocI]
  exact ⟨_, Split.right (Split.right (Split.right (Split.left (Split.right (Split.right
      (Split.right (Split.last _ _) _) _) _) _) _) _) _,
    Split.right (Split.right (Split.right (Split.left (Split.right (Split.right
      (Split.right (Split.last _ _) _) _) _) _) _) _) _⟩

/-- Storing `indep_flag` into its local. -/
theorem um_storeLoc {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) Sg st)
    (a : BitVec 64) (ha : a = t₀.regs.get64 .rsp - 0x34#64) (iv : BitVec 32) :
    m.storeInt a 4 iv.toInt =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) iv) Sg st := by
  obtain ⟨R, hs, hs'⟩ := um_split_loc k A ra t₀ Sg st iv
  rw [hs', ha]
  exact Block.storeInt_val h hs iv.toInt

/-- The local of `indep_flag` is there. -/
theorem um_loadLoc {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) Sg st)
    (a : BitVec 64) (ha : a = t₀.regs.get64 .rsp - 0x34#64) :
    (m.loadInt a 4).isSome = true := by
  obtain ⟨R, hs, -⟩ := um_split_loc k A ra t₀ Sg st 0#32
  rw [hs] at h
  rw [ha]
  exact Block.loadInt_isSome h (by simp)

/-- `indep_flag` into its local; `0` goes to the first flag, else the flags are not read. -/
theorem blk_L33a3 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L33a3" := by
  cfg_block
  measure_hb "L33a3"
    intro n
    simp only [tbl_L33a3, var_L33a3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hdx, hcx, hr9⟩, h15⟩ := hs₀.1
    obtain rfl := hs₀.2
    have hst := fun a ha w => um_storeLoc hm a ha w
    have hld := fun a ha => um_loadLoc hm a ha
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2
    have lp2 : ∀ a (ha : a = t₀.regs.get64 .rsp - 0x34#64) (w : BitVec 32),
        (s₀.dmem.storeInt a 4 w.toInt).loadInt (A.1.g + 16#64) 4
          = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      intro a ha w
      have h := um_storeLoc hm a ha w
      simp only [UM, UF, GbU] at h
      sep_mem h <;> rfl
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    have hbpC : PLift (s₀.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) := ⟨hbp⟩
    have hof' : s₀.regs.get64 .rbp + (-44 : Int64).toBitVec = t₀.regs.get64 .rsp - 0x34#64 := by
      rw [hbp, show (-44 : Int64).toBitVec = -44#64 from rfl]; bv_omega
    generalize UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) (Sv t₀) st = P at hm
    vcgen
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14, hcx, hr9,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hld _ (by rw [hbpC.down, show (-44 : Int64).toBitVec = -44#64 from rfl]; bv_omega)
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L33ba], by decide⟩⟩
      rw [tbl_L33ba]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st, hI, ⟨hP, ?_⟩, hst _ ?hof _⟩, ?_, ?_⟩, ?_⟩
      case hof => rw [hbpC.down, show (-44 : Int64).toBitVec = -44#64 from rfl]; bv_omega
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbpC.down | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15
        | (have hx := ‹loadInt (storeInt _ _ 4 _) (A.1.g + 16#64) 4 = some _›
           rw [lp2 _ hof' _] at hx
           obtain rfl := Option.some.inj hx
           simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt])
    · rw [lp2 _ (by rw [hbpC.down, show (-44 : Int64).toBitVec = -44#64 from rfl]; bv_omega) _]; rfl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3410], by decide⟩⟩
      rw [tbl_L3410]
      refine ⟨⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, st, hI, ⟨hP, ?_⟩, hst _ ?hof _⟩, ?_, ?_, ?_⟩, ?_⟩
      case hof => rw [hbpC.down, show (-44 : Int64).toBitVec = -44#64 from rfl]; bv_omega
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      all_goals first
        | exact hsp | exact hbpC.down | exact h12 | exact hbx | exact h14c.down
        | exact h13 | exact hdx | exact h15
        | (have hx := ‹loadInt (storeInt _ _ 4 _) (A.1.g + 16#64) 4 = some _›
           rw [lp2 _ hof' _] at hx
           obtain rfl := Option.some.inj hx
           simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt])

end Kraken.Examples.Sbr.Usac
