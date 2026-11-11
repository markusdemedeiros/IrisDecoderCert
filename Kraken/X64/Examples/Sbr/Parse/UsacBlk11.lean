import Kraken.X64.Examples.Sbr.Parse.UsacBlk10
import Kraken.X64.Examples.Sbr.Parse.GridBlk2
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the bit reads

The inlined `get_bits1`: `index` and `size_in_bits_plus8` are loaded, one byte of the
bitstream at `buffer + index / 8` is read (inside the buffer by `index ≤ size_in_bits_plus8`
and `GbC`), and `index + (index < size_in_bits_plus8)` is stored back (`um_storeI`, `idx_le`).
`L36c7` (single channel) reads one bit, sets `r15 = &data[0]` and branches on the bit. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- `UF` without the reader's index cell. -/
abbrev UFxI (q : UQ) (st : USt) : Mem 64 → Prop :=
  SHW q.c st ⋆ (TWc q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DSc q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (AcU q.a st.x ⋆ ((Int.toBytes 8 q.buf.toInt =@ q.g
    ⋆ (4 ?@ (q.g + 0xc#64) ⋆ cell4 (q.g + 0x10#64) q.p8)) ⋆ RdU q)))))))

theorem uf_i (q : UQ) (st : USt) : UF q st = cell4 (q.g + 8#64) st.i ⋆ UFxI q st := by
  simp only [UF, GbU, UFxI]; ac_rfl

/-- Storing the reader's index. -/
theorem um_storeI {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) (v : BitVec 32) :
    m.storeInt (A.1.g + 8#64) 4 v.toInt =⋆ UM k A ra t₀ Lc Sg { st with i := v } := by
  have e : ∀ st' : USt, UM k A ra t₀ Lc Sg st' = cell4 (A.1.g + 8#64) st'.i
      ⋆ (8 ?@ (t₀.regs.get64 .rsp - 0x50#64) ⋆ (Reserve (cneed k) (t₀.regs.get64 .rsp - 0x50#64)
      ⋆ (UFxI A.1 st' ⋆ (Lc ⋆ (Sg ⋆ (RetCell ra (t₀.regs.get64 .rsp) ⋆ A.1.R)))))) := by
    intro st'; simp only [UM, uf_i]; ac_rfl
  rw [e] at h ⊢
  exact storeInt_sep _ 4 _ _ m ⟨h, Int.toBytes_length 4 _⟩ v.toInt

/-- The bitstream out of the frame. -/
theorem um_blocks {m : Mem 64} {k : Nat} {A : UA} {ra : Int64} {t₀ : MachineData}
    {Lc Sg : Mem 64 → Prop} {st : USt} (h : m =⋆ UM k A ra t₀ Lc Sg st) :
    ∃ F, m =⋆ Blocks [(A.1.buf, A.1.L), (lab "ceil_log2", 6)] ⋆ F := by
  simp only [UM, UF, RdU] at h
  obtain ⟨F, h⟩ := Parse.pick_r h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_ll h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_lr h
  obtain ⟨F, h⟩ := Parse.pick_ll h
  exact ⟨F, h⟩

omit [CodeEnv] in
/-- The reader's `setl` comparison of `index` with `size_in_bits_plus8`. -/
theorem flag_l (i p : BitVec 32) (hi : i.toNat < 2 ^ 31) (hp : p.toNat < 2 ^ 31) :
    ((i - p).msb != ((i - p).signed != i.signed - p.signed)) = decide (i.toNat < p.toNat) := by
  simp only [BitVec.signed, BitVec.msb_eq_decide, BitVec.toInt_eq_toNat_bmod]
  by_cases h : i.toNat < p.toNat
  · have e : (i - p).toNat = 2 ^ 32 - p.toNat + i.toNat := by
      rw [BitVec.toNat_sub]; omega
    simp only [e, h, decide_true]
    have h1 : (((2 ^ 32 - p.toNat + i.toNat : Nat) : Int).bmod (2 ^ 32))
        = (i.toNat : Int) - p.toNat := by
      rw [Int.bmod_def]; split <;> omega
    have h2 : ((↑i.toNat : Int).bmod (2 ^ 32)) = (i.toNat : Int) := by
      rw [Int.bmod_def]; split <;> omega
    have h3 : ((↑p.toNat : Int).bmod (2 ^ 32)) = (p.toNat : Int) := by
      rw [Int.bmod_def]; split <;> omega
    have h4 : 2 ^ (32 - 1) ≤ 2 ^ 32 - p.toNat + i.toNat := by omega
    simp only [h1, h2, h3, h4, decide_true, bne_self_eq_false, Bool.bne_false]
  · have e : (i - p).toNat = i.toNat - p.toNat := by
      rw [BitVec.toNat_sub]; omega
    simp only [e, h, decide_false]
    have h1 : (((i.toNat - p.toNat : Nat) : Int).bmod (2 ^ 32)) = (i.toNat : Int) - p.toNat := by
      rw [Int.bmod_def]; split <;> omega
    have h2 : ((↑i.toNat : Int).bmod (2 ^ 32)) = (i.toNat : Int) := by
      rw [Int.bmod_def]; split <;> omega
    have h3 : ((↑p.toNat : Int).bmod (2 ^ 32)) = (p.toNat : Int) := by
      rw [Int.bmod_def]; split <;> omega
    have h4 : ¬ 2 ^ (32 - 1) ≤ i.toNat - p.toNat := by omega
    simp only [h1, h2, h3, h4, decide_false, bne_self_eq_false]

omit [CodeEnv] in
/-- The new `index` stays below `size_in_bits_plus8`. -/
theorem idx_le (i p z : BitVec 32) (cf af : Bool) (hi : i.toNat ≤ p.toNat) (hp : p.toNat < 2 ^ 31) :
    (i + BitVec.setWidth 32 ((BitVec.setWidth 64 (z ^^^ z)).replaceLow
      (BitVec.ofNat 8 (CondCode.l.interp (StatusFlags.from_result (i - p)
        { cf := cf, af := af, of := (i - p).signed != i.signed - p.signed })).toNat))).toNat
      ≤ p.toNat := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.xor_self]
  rw [flag_l i p (by omega) hp]
  by_cases h : i.toNat < p.toNat
  · simp only [h, decide_true]
    have : (BitVec.setWidth 32 ((BitVec.setWidth 64 0#32).replaceLow
        (BitVec.ofNat 8 (true).toNat))) = 1#32 := by decide
    rw [this, BitVec.toNat_add]; simp; omega
  · simp only [h, decide_false]
    have : (BitVec.setWidth 32 ((BitVec.setWidth 64 0#32).replaceLow
        (BitVec.ofNat 8 (false).toNat))) = 0#32 := by decide
    rw [this, BitVec.add_zero]; exact hi

/-- A bit read; `r15 = &sbr->data[0]`. -/
theorem blk_L36c7 (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    BlockOb k A ra t₀ "ff_aac_sbr_decode_usac_data.L36c7" := by
  cfg_block
  measure_hb "L36c7"
    intro n
    simp only [tbl_L36c7, var_L36c7]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hF, ⟨hsp, hbp, h12, hbx, h14⟩, h13, st, hI, hP, hm⟩, hch⟩, rfl⟩ := hs₀
    have hp : A.1.p8.toNat < 2 ^ 31 := hF.1.2.2.2.1.1
    have hoff := Parse.rd_off st.i A.1.p8 A.1.L hI.2.2 hF.1.2.2.2.1.2.1
    obtain ⟨F, hB⟩ := um_blocks hm
    have hbl := Blocks.loadInt_isSome hB (Blocks.Inside.base_add (n := 1)
      (x := (st.i.ushiftRight 3).setWidth 64) (by omega))
    have hst := um_storeI hm
    have hm2 := hm
    simp only [UM, UF, GbU] at hm2
    have li : s₀.dmem.loadInt (A.1.g + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 st.i.toInt)) := by
      sep_mem hm2 <;> rfl
    have lp : s₀.dmem.loadInt (A.1.g + 16#64) 4
        = some (Int.ofBytes (Int.toBytes 4 A.1.p8.toInt)) := by
      sep_mem hm2 <;> rfl
    have lb : s₀.dmem.loadInt A.1.g 8 = some (Int.ofBytes (Int.toBytes 8 A.1.buf.toInt)) := by
      sep_mem hm2 <;> rfl
    clear hm2 hB
    have h14c : PLift (s₀.regs.get64 .r14 = A.1.g) := ⟨h14⟩
    generalize UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st = P at hm
    vcgen [Parse.shl_cl32_havoc]
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, h14,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try simp only [li, lp, lb, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *
    · exact hbl
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inr ⟨by rw [var_L3933], by decide⟩⟩
      rw [tbl_L3933]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · simp only [ite_true, hbx, dAc, sA, BitVec.add_assoc]; rfl
    · refine ⟨?_, by rw [var_L36fa]; decide⟩
      rw [tbl_L36fa]
      refine ⟨⟨hF, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, _, ?inv, ?sm, hst _⟩, ?_⟩
      case inv => exact ⟨hI.1, hI.2.1, idx_le _ _ _ _ _ hI.2.2 hp⟩
      case sm => exact hP
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false]
      · exact hsp
      · exact hbp
      · exact h12
      · exact hbx
      · exact h14c.down
      · exact h13
      · simp only [ite_true, hbx, dAc, sA, BitVec.add_assoc]; rfl

end Kraken.Examples.Sbr.Usac
