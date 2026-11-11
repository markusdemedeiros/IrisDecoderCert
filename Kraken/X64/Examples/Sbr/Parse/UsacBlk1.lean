import Kraken.X64.Examples.Sbr.Parse.UsacModel
import Kraken.X64.Examples.Sbr.Parse.UsacTbl1
import Kraken.X64.Examples.Sbr.Parse.UsacTbl5
import Kraken.X64.Examples.Sbr.Parse.UsacTbl6

/-!
# `ff_aac_sbr_decode_usac_data`: the prologue, the first stores, the return paths

The prologue (`entry`), `L3361` (`reset = 0`, `usac = 1`), `L3388` (`sample_rate`, `id_aac`),
the jump `L3aac`, the epilogue `L3ef1`, the `ret` (`done`) and the trap `L3f00`. A block
rewrites the table and the variant at its own labels only (`tbl_*`, `var_*`), and the footprint
is split into the cells it touches and one `Mem.Hid` atom (`uf_ru`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
-- the shared `simp` sets of the block proofs name lemmas some goals do not need
set_option linter.unusedSimpArgs false

namespace Kraken.Examples.Sbr.Usac

variable [CodeEnv]

/-! ## The footprint around the first scalar fields -/

/-- `UF` without `sampleRate`, `idAac`, `usac`, `reset` and `ext_sample_rate`. -/
def UFr (q : UQ) (st : USt) : Mem 64 → Prop :=
  let s := sA q.c
  cell4 (s + 0x4#64) st.x.start ⋆ (cell4 (s + 0x8#64) st.x.ready
    ⋆ (4 ?@ (s + 0x14#64) ⋆ (st.sp.take 4 =@ (s + 0x1c#64)
    ⋆ (st.sp.drop 4 =@ (s + 0x20#64) ⋆ (2 ?@ (s + 0x22#64)
    ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (4 ?@ (s + 0x28#64)
    ⋆ (cell4 (s + 0x2c#64) (BitVec.ofNat 32 st.h.lb) ⋆ (c4 (s + 0x30#64) st.x.limGains
    ⋆ (cell4 (s + 0x34#64) st.x.interpol ⋆ (cell4 (s + 0x38#64) st.x.smooth
    ⋆ (cell4 (s + 0x3c#64) st.x.coupling ⋆ (c4 (s + 0x40#64) st.x.k0 ⋆ (16 ?@ (s + 0x44#64)
    ⋆ (c4 (s + 0x54#64) st.x.kx0 ⋆ (c4 (s + 0x58#64) st.x.kx1 ⋆ (c4 (s + 0x5c#64) st.x.m0
    ⋆ (c4 (s + 0x60#64) st.x.m1 ⋆ (cell4 (s + 0x64#64) st.x.pushed
    ⋆ (24 ?@ (s + 0x68#64)
    ⋆ (TWc q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DSc q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (Int.toBytes 8 st.x.avctx.toInt =@ (q.a + 0x8#64)
    ⋆ (GbU q st.i ⋆ RdU q)))))))))))))))))))))))))))

theorem uf_ru (q : UQ) (st : USt) :
    UF q st = cell4 (q.c + 0x28920#64) st.x.sampleRate ⋆ (cell4 (q.c + 0x2892c#64) st.x.idAac
      ⋆ (cell4 (q.c + 0x28930#64) st.u ⋆ (cell4 (q.c + 0x28938#64) st.x.reset
      ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate ⋆ Mem.Hid (UFr q st))))) := by
  simp only [UF, SHW, UFr, AcU, Mem.Hid, sA, BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

/-! ## The prologue -/

/-- The memory the prologue does not touch. -/
abbrev EntryH (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x50#64) ⋆ (Reserve (cneed k) (r - 0x50#64) ⋆ (UF A.1 A.2 ⋆ (LocR r
    ⋆ (RetCell ra r ⋆ A.1.R))))

theorem entry_pre (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) (Bs (t₀.regs.get64 .rsp)) A.2 =
      8 ?@ (t₀.regs.get64 .rsp - 0x8#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x10#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x18#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x20#64)
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x28#64) ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x30#64)
      ⋆ Mem.Hid (EntryH k A ra t₀)))))) := by
  simp only [UM, Bs, EntryH, Mem.Hid]
  ac_rfl

theorem entry_post (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) (Sv t₀) A.2 =
      c8 (t₀.regs.get64 .rsp - 0x8#64) (t₀.regs.get64 .rbp)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x10#64) (t₀.regs.get64 .r15)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x18#64) (t₀.regs.get64 .r14)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x20#64) (t₀.regs.get64 .r13)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x28#64) (t₀.regs.get64 .r12)
      ⋆ (c8 (t₀.regs.get64 .rsp - 0x30#64) (t₀.regs.get64 .rbx)
      ⋆ Mem.Hid (EntryH k A ra t₀)))))) := by
  simp only [UM, Sv, EntryH, Mem.Hid]
  ac_rfl

omit [CodeEnv] in
theorem u_sub_sub (a b c : BitVec 64) : a - b - c = a - (b + c) := by bv_omega

/-- `ud1`: unreachable, its assertion is `False`. -/
theorem blk_L3f00 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3f00" := by
  cfg_block
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  rw [tbl_L3f00] at hs₀
  exact False.elim hs₀.1

/-- The prologue: six pushes, `sub $0x18,%rsp`. -/
theorem blk_entry (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data" := by
  cfg_block
  measure_hb "entry"
    intro n
    simp only [tbl_entry, var_entry, tbl_L3361, var_L3361]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hF, hm⟩, rfl⟩ := hs₀
    rw [entry_pre] at hm
    simp only [T_L3361, entry_post]
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, u_sub_sub, BitVec.reduceAdd, BitVec.reduceSetWidth] at *
    all_goals grind_cells'

/-! ## `L3361` -/

/-- The state after the two stores of `L3361`. -/
abbrev st1 (st : USt) : USt := { st with x := { st.x with reset := 0#32 }, u := 1#32 }

theorem ufr_st1 (q : UQ) (st : USt) : UFr q (st1 st) = UFr q st := rfl

/-- `L3361`: the arguments to their registers, `sbr->reset = 0`, `sbr->usac = 1`. -/
theorem blk_L3361 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3361" := by
  cfg_block
  measure_hb "L3361"
    intro n
    simp only [tbl_L3361, var_L3361, tbl_L3388, var_L3388]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, hsp, hbp, hdi, hsi, hdx, hcx, h8, h9, hm⟩, rfl⟩ := hs₀
    simp only [UM, uf_ru] at hm
    obtain ⟨hC, ha0, ha1, ha2, ha3, hstk⟩ := hF
    simp only [T_L3388, At, UM, uf_ru]
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, AddrIndex.offset64_none, BitVec.add_zero,
      BitVec.ofNat_eq_ofNat, hsi, hdi, hdx, hcx, h8, h9, ha0, ha1, ha2, ha3, hsp, hbp]
    all_goals try simp only [BitVec.add_zero]
    all_goals try sep_mem hm
    case vc3 =>
      refine ⟨⟨⟨⟨⟨hC, trivial, trivial, trivial, trivial, hstk⟩,
        ⟨trivial, trivial, trivial, trivial, trivial⟩,
        trivial, st1 A.2, ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hC.2.1, hC.2.2.1⟩,
        ⟨mi_reset 0#32 hC.1, rfl, rfl⟩, ?_⟩, trivial, trivial, trivial, trivial, trivial, trivial⟩,
        ?_⟩, Nat.le_refl _⟩
      rotate_left
      · apply BitVec.eq_of_toNat_eq; simp [chv, arg4]
      simp only [ufr_st1]
      simp only [BitVec.reduceSetWidth] at hm
      sep_close hm

/-! ## `L3388` -/

/-- The state after `L3388`: `sample_rate`, `id_aac`. -/
abbrev st2 (t₀ : MachineData) (st : USt) : USt :=
  { st with x := { st.x with sampleRate := st.x.extRate, idAac := idv t₀ } }

theorem ufr_st2 (q : UQ) (t₀ : MachineData) (st : USt) : UFr q (st2 t₀ st) = UFr q st := rfl

omit [CodeEnv] in
/-- `xor %eax,%eax; cmp $0x2,%r8d; sete %al`: `id_aac`. -/
theorem sete2 (v y : BitVec 32) (f : StatusFlags.from_result.Remaining) :
    BitVec.setWidth 32 ((BitVec.setWidth 64 (y ^^^ y)).replaceLow
      (BitVec.ofNat 8 (CondCode.z.interp (StatusFlags.from_result (v - 2#32) f)).toNat))
      = if v = 2#32 then 1#32 else 0#32 := by
  rw [CondCode.interp_z, StatusFlags.zf_from_result_sub, BitVec.xor_self]
  by_cases h : v = 2#32
  · subst h; rfl
  · have h' : (v == 2#32) = false := by simpa using h
    rw [h', show (if v = 2#32 then 1#32 else 0#32) = 0#32 from by simp [h]]; rfl

omit [CodeEnv] in
theorem sw6432 (v : BitVec 32) : (v.setWidth 64).setWidth 32 = v := by
  apply BitVec.eq_of_toNat_eq; simp

theorem blk_L3388 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3388" := by
  cfg_block
  measure_hb "L3388"
    intro n
    simp only [tbl_L3388, var_L3388, tbl_L33a3, var_L33a3]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hS, hm⟩, hdi, hsi, hdx, hcx, h8, h9⟩,
      h15⟩, rfl⟩ := hs₀
    simp only [UM, uf_ru] at hm
    have hl : s₀.dmem.loadInt (A.1.a + 22516#64) 4
        = some (Int.ofBytes (Int.toBytes 4 st.x.extRate.toInt)) := by
      sep_mem hm <;> rfl
    simp only [T_L33a3, At, UM, uf_ru]
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, hsi, hdi, hdx, hcx, h8, h9, hsp, hbp, h12, hbx, h14,
      h13, hl,
      Option.some.injEq, BitVec.reduceSetWidth] at *
    all_goals try simp only [BitVec.add_zero]
    all_goals try subst_vars
    all_goals try sep_mem hm
    case vc1 => rfl
    case vc4 =>
      simp only [BitVec.ofInt_ofBytes_toBytes 32 4 rfl, sw6432, sete2] at hm ⊢
      obtain ⟨hmi, hr, hu⟩ := hS
      refine ⟨⟨⟨⟨hF, ⟨trivial, trivial, trivial, trivial, trivial⟩, trivial, st2 t₀ st, hI,
        ⟨⟨mi_srid _ _ hmi, hr, hu⟩, rfl⟩, ?_⟩, trivial, trivial, trivial⟩, h15⟩, Nat.le_refl _⟩
      simp only [ufr_st2, idv, chv, arg4]
      sep_close hm


/-! ## The return paths -/

/-- `jmp L3ef1`. -/
theorem blk_L3aac (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3aac" := by
  cfg_block
  measure_hb "L3aac"
    intro n
    simp only [tbl_L3aac, var_L3aac]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨h, rfl⟩ := hs₀
    vcgen
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ?_, Or.inl (by rw [var_L3ef1]; decide)⟩
    rw [tbl_L3ef1]; exact h

omit [CodeEnv] in
theorem ep_offs (t : BitVec 64) : 24#64 + (t - 72#64) = t - 48#64 ∧ t - 48#64 + 8#64 = t - 40#64
    ∧ t - 40#64 + 8#64 = t - 32#64 ∧ t - 32#64 + 8#64 = t - 24#64
    ∧ t - 24#64 + 8#64 = t - 16#64 ∧ t - 16#64 + 8#64 = t - 8#64 ∧ t - 8#64 + 8#64 = t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> bv_omega

/-- The epilogue: `add $0x18,%rsp`, six pops. -/
theorem blk_L3ef1 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L3ef1" := by
  cfg_block
  measure_hb "L3ef1"
    intro n
    simp only [tbl_L3ef1, var_L3ef1, tbl_done, var_done]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, hsp, st, hO, hm⟩, rfl⟩ := hs₀
    simp only [UM, Sv, LocI] at hm
    have po := ep_offs (t₀.regs.get64 .rsp)
    have l1 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 48#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbx).toInt)) := by sep_mem hm <;> rfl
    have l2 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 40#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r12).toInt)) := by sep_mem hm <;> rfl
    have l3 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 32#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r13).toInt)) := by sep_mem hm <;> rfl
    have l4 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 24#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r14).toInt)) := by sep_mem hm <;> rfl
    have l5 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 16#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .r15).toInt)) := by sep_mem hm <;> rfl
    have l6 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 8#64) 8
        = some (Int.ofBytes (Int.toBytes 8 (t₀.regs.get64 .rbp).toInt)) := by sep_mem hm <;> rfl
    simp only [T_done, UM, LocR, Bs]
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true,
      ite_false, Int64.toBitVec_ofNat_norm, hsp, BitVec.reduceSetWidth, po.1, po.2.1, po.2.2.1,
      po.2.2.2.1, po.2.2.2.2.1, po.2.2.2.2.2.1, po.2.2.2.2.2.2, l1, l2, l3, l4, l5, l6,
      Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, and_true, true_and]
    exact ⟨⟨hF, st, hO, by sep_close hm⟩, Nat.zero_le _⟩

theorem blk_done (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.done" := by
  cfg_block
  measure_hb "done"
    intro n
    simp only [tbl_done, var_done]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hF, hsp, hbp, hsv, st, hO, hm⟩, rfl⟩ := hs₀
    simp only [UM] at hm
    have hpost : s₀.dmem =⋆ 8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (Reserve (cneed k)
        (t₀.regs.get64 .rsp - 0x50#64) ⋆ (UF A.1 st ⋆ (LocR (t₀.regs.get64 .rsp)
        ⋆ (Bs (t₀.regs.get64 .rsp) ⋆ (8 ?@ (t₀.regs.get64 .rsp) ⋆ A.1.R))))) := by
      sep_close hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) := by
      sep_mem hm <;> rfl
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    generalize table k A ra t₀ = T
    generalize var = V
    vcgen
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right; left
    refine ⟨rfl, st, hO, ?_, ?_, ?_, hpost⟩
    all_goals try simp only [hsp, hbp, hsv, and_self]
    all_goals first | rfl | exact hO

end Kraken.Examples.Sbr.Usac
