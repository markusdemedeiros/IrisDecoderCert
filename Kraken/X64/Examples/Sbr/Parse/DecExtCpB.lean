import Kraken.X64.Examples.Sbr.Parse.DecExtCpeH
import Kraken.X64.Examples.Sbr.HfAssemble.Cells

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the coupled channel pair (model facts)

The byte copies `cpA`..`cpE` of the inlined `copy_sbr_grid(&data[1], &data[0])` are `copyGrid`
(`cpE_eq`), so they take `CInv0` to `EInv` (`cp_einv`); the two `memcpy` of `bs_invf_mode`
(`invfShift`, then `invfCouple`) keep `EInv`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

omit [CodeEnv] in
theorem old_eq (l : List UInt8) (j : Nat) (h : j < l.length) : old l j = l[j] := by
  simp [old, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

omit [CodeEnv] in
/-- The five copies are `copy_sbr_grid(&data[1], &data[0])`. -/
theorem cpE_eq {d0 d1 : DV} (hd0 : DWF False d0) (hd1 : DWF False d1) :
    cpE d0 d1 = copyGrid d1 d0 := by
  obtain ⟨a1, -, a3, a4, -⟩ := hd0
  obtain ⟨b1, -, b3, b4, b5, -⟩ := hd1
  have f : ((d1.freqRes.set 0 (d1.freqRes.getD d1.nenv 0)).take 1 ++ (d0.freqRes.drop 1).take 8)
      = mk 9 (fun j => if j = 0 then old d1.freqRes d1.nenv else old d0.freqRes j) := by
    apply List.ext_getElem
    · simp [mk, a1, b1]
    · intro i h₁ h₂
      simp only [mk, List.getElem_map, List.getElem_range]
      simp only [List.length_append, List.length_take, List.length_set, List.length_drop, a1,
        b1] at h₁
      by_cases hi : i = 0
      · subst hi
        rw [List.getElem_append_left (by simp [b1])]
        simp [List.getElem_take, old]
      · rw [List.getElem_append_right (by simp [b1]; omega)]
        simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_set, b1,
          hi, ↓reduceIte]
        rw [old_eq _ _ (by omega)]
        congr 1; omega
  have t : ((d0.te.take 8 ++ (d1.te.set 9 (d1.te.getD d1.nenv 0)).drop 8).set 8 (d0.te.getD 8 0))
      = mk 10 (fun j => if j = 9 then old d1.te d1.nenv else old d0.te j) := by
    apply List.ext_getElem
    · simp [mk, a3, b3]
    · intro i h₁ h₂
      simp only [mk, List.getElem_map, List.getElem_range]
      simp only [List.length_set, List.length_append, List.length_take, List.length_drop, a3,
        b3] at h₁
      rw [List.getElem_set]
      by_cases h8 : i = 8
      · subst h8; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm h8)]
        by_cases hlt : i < 8
        · rw [List.getElem_append_left (by simp [a3]; omega)]
          simp [List.getElem_take, show i ≠ 9 by omega,
            List.getElem?_eq_getElem (show i < d0.te.length by omega)]
        · have h9 : i = 9 := by omega
          subst h9
          rw [List.getElem_append_right (by simp [a3])]
          simp [List.getElem_drop, a3]
  have q : (d0.tq.take 2 ++ d1.tq.drop 2).set 2 (d0.tq.getD 2 0) = mk 3 (fun j => old d0.tq j) := by
    apply List.ext_getElem
    · simp [mk, a4, b4]
    · intro i h₁ h₂
      simp only [mk, List.getElem_map, List.getElem_range]
      simp only [List.length_set, List.length_append, List.length_take, List.length_drop, a4,
        b4] at h₁
      rw [List.getElem_set]
      by_cases h2 : i = 2
      · subst h2; simp
      · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm h2),
          List.getElem_append_left (by simp [a4]; omega)]
        simp [List.getElem_take, List.getElem?_eq_getElem (show i < d0.tq.length by omega)]
  unfold cpE cpD cpC cpB2 cpB cpA copyGrid
  simp only [f, t, q]

omit [CodeEnv] in
theorem dwf_invfShift {v : DV} (h : DWF False v) : DWF False (invfShift v) := by
  unfold invfShift
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, -⟩ := h
  refine ⟨b1, mk_length _ _, b3, b4, b5, b6, b7, fun i hi => ?_, b9, b10, b11, b12, b13, b14, b15,
    False.elim⟩
  rw [u8_mk]; have := b8 i hi; (repeat' split) <;> bnd

omit [CodeEnv] in
/-- The copy takes `CInv0` to `EInv`: `copy_wf`, a live channel 1. -/
theorem cp_einv {PI : List UInt8 → Prop} {X : XA} {e : DS} (hC : CInv0 PI X e) :
    EInv PI X (e.setCh true (cpE e.a.d0 e.a.d1)) := by
  rw [setCh_true]
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, g0, g1⟩, i1⟩, hL0, hok, hP, hK, hsi, -, -⟩ := hC
  rw [cpE_eq a3 a4]
  obtain ⟨c1, c2, c3, -⟩ := copy_wf a3 g0 a4 g1
  exact ⟨⟨⟨a1, a2, a3, c1, a5, g0, c2⟩, i1⟩, ⟨fun _ => hL0, fun _ => c3 hL0⟩, hok, hP, hK, hsi⟩

omit [CodeEnv] in
/-- The first `memcpy` keeps `EInv`. -/
theorem einv_shift {PI : List UInt8 → Prop} {X : XA} {d : DS} (hE : EInv PI X d) :
    EInv PI X (d.setCh true (invfShift d.a.d1)) := by
  rw [setCh_true]
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, g0, g1⟩, i1⟩, ⟨l0, l1⟩, hok, hP, hK, hsi⟩ := hE
  exact ⟨⟨⟨a1, a2, a3, dwf_invfShift a4, a5, g0, g1⟩, i1⟩, ⟨l0, l1⟩, hok, hP, hK, hsi⟩

omit [CodeEnv] in
/-- The second `memcpy` keeps `EInv`. -/
theorem einv_couple {PI : List UInt8 → Prop} {X : XA} {d : DS} (hE : EInv PI X d) :
    EInv PI X (d.setCh true (invfCouple d.a.d0 d.a.d1)) := by
  rw [setCh_true]
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, g0, g1⟩, i1⟩, ⟨l0, l1⟩, hok, hP, hK, hsi⟩ := hE
  exact ⟨⟨⟨a1, a2, a3, dwf_invfCouple a3 a4, a5, g0, g1⟩, i1⟩,
    ⟨l0, fun h => live_invfCouple (l1 h)⟩, hok, hP, hK, hsi⟩

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem zext9_all : ∀ n : Nat, n < 9 →
    BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n := by
  decide

omit [CodeEnv] in
theorem zext9 {n : Nat} (h : n ≤ 8) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n :=
  zext9_all n (by omega)

omit [CodeEnv] in
/-- `cmp $0x9,%rax; jae` on `rax ≤ 8`. -/
theorem nc9_all : ∀ n : Nat, n < 9 → CondCode.nc.interp (StatusFlags.from_result
    (BitVec.ofNat 64 n - BitVec.setWidth 64 (Int64.toBitVec 9))
    { cf := (BitVec.ofNat 64 n - BitVec.setWidth 64 (Int64.toBitVec 9)).unsigned
          != (BitVec.ofNat 64 n).unsigned - (BitVec.setWidth 64 (Int64.toBitVec 9)).unsigned,
      af := ((BitVec.ofNat 64 n - BitVec.setWidth 64 (Int64.toBitVec 9)).take 4).unsigned
          != ((BitVec.ofNat 64 n).take 4).unsigned
            - ((BitVec.setWidth 64 (Int64.toBitVec 9)).take 4).unsigned,
      of := (BitVec.ofNat 64 n - BitVec.setWidth 64 (Int64.toBitVec 9)).signed
          != (BitVec.ofNat 64 n).signed - (BitVec.setWidth 64 (Int64.toBitVec 9)).signed })
    = false := by
  decide

omit [CodeEnv] in
theorem sw8 (x : BitVec 8) : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 x)) = x := by
  bv_omega

omit [CodeEnv] in
/-- A byte loaded with `movzbl` and stored back with `mov %cl`. -/
theorem b1_of (bs : List UInt8) (h : bs.length = 1) :
    Int.toBytes 1 (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32
      (BitVec.ofInt 8 (Int.ofBytes bs))))).toInt = bs := by
  rw [sw8]; exact tb_ofInt 1 bs h

omit [CodeEnv] in
theorem tk1 (l : List UInt8) (j : Nat) (h : j < l.length) : (l.drop j).take 1 = [l.getD j 0] := by
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.take_zero,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

omit [CodeEnv] in
theorem splice1 (l : List UInt8) (j : Nat) (b : UInt8) (h : j < l.length) :
    l.set j b = l.take j ++ [b] ++ l.drop (j + 1) := by
  rw [List.set_eq_take_append_cons_drop, ite_eq_left_iff.mpr (fun h' => absurd h h')]; simp

omit [CodeEnv] in
/-- The offset of an indexed access `r + (n + c)` in the cell at `r + c`. -/
theorem off_n (r : BitVec 64) (n c : Nat) (h : n < 2 ^ 32) :
    (r + (BitVec.ofNat 64 n + BitVec.ofNat 64 c) - (r + BitVec.ofNat 64 c)).toNat = n := by
  rw [show r + (BitVec.ofNat 64 n + BitVec.ofNat 64 c) - (r + BitVec.ofNat 64 c)
    = BitVec.ofNat 64 n by bv_omega]
  simp only [BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem tk_take (l : List UInt8) (k n : Nat) (h : n < k) :
    ((l.take k).drop n).take 1 = (l.drop n).take 1 := by
  rw [List.drop_take, List.take_take]; congr 1; omega

omit [CodeEnv] in
theorem sbrS_c1 (d : DS) (v : DV) (s : BitVec 64) : SbrS (d.setCh true v) s = SbrS d s := rfl
omit [CodeEnv] in
theorem tabF_c1 (d : DS) (v : DV) (s : BitVec 64) : TabF (d.setCh true v).a s = TabF d.a s := rfl
omit [CodeEnv] in
theorem acF_c1 (d : DS) (v : DV) (ac : BitVec 64) (sr : BitVec 32) :
    AcF ac (d.setCh true v).a sr = AcF ac d.a sr := rfl
omit [CodeEnv] in
theorem c1_d0 (d : DS) (v : DV) : (d.setCh true v).a.d0 = d.a.d0 := rfl
omit [CodeEnv] in
theorem c1_d1 (d : DS) (v : DV) : (d.setCh true v).a.d1 = v := rfl
omit [CodeEnv] in
theorem c1_psc (d : DS) (v : DV) : (d.setCh true v).a.psc = d.a.psc := rfl
omit [CodeEnv] in
theorem c1_avctx (d : DS) (v : DV) : (d.setCh true v).a.avctx = d.a.avctx := rfl

open Lean Meta Elab Tactic in
/-- `val_split h a`: `hsplit : Mem.Split (bs =@ a) R H` for the known cell at `a` of
`h : m =⋆ H`. -/
elab "val_split " h:ident a:term : tactic => withMainContext do
  let hf ← getFVarFromUserName h.getId
  let ty ← instantiateMVars (← inferType hf)
  let a ← Lean.Elab.Tactic.elabTerm a none
  let some hs ← HfAssemble.Cells.findSplit ty.appFn! (fun leaf => do
      if leaf.isAppOfArity ``Mem.Val 3 then HfAssemble.Cells.sameAddr (leaf.getArg! 1) a
      else pure false)
    | throwError "val_split: no cell"
  let g ← getMainGoal
  let (_, g') ← (← g.assert `hsplit (← inferType hs) hs).intro1P
  replaceMainGoal [g']

/-- A frame goal `s.regs.get64 r = …` (also an address `sbrA t₀ + c`). -/
macro "fr_c" : tactic => `(tactic| (
  (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sbrA, arg0, arg1,
    BitVec.add_assoc, BitVec.reduceAdd]) <;> first | rfl | assumption | trivial))

theorem blk_L591 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L591" := by
  cfg_block
  measure_hb "L591"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hC0, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    have hn8 : d.a.d1.nenv ≤ 8 := hC0.1.1.2.2.2.1.2.2.2.2.1
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    case vc1 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, Int64.toBitVec_ofNat_norm]
      sep_mem hmu
    all_goals rename_i v hx hc
    all_goals
      have hv : v = Int.ofBytes (Int.toBytes 4 (d.a.d1.nenv : Int)) := by
        have hmu := p_h0.down
        simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
        simp only [h14, Int64.toBitVec_ofNat_norm] at hx
        sep_vals hmu
        first | rfl | (simp only [Option.some.injEq] at hx; exact hx.symm)
    all_goals subst hv
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      BitVec.ofInt32_ofBytes_toBytes4, zext9 hn8] at hc ⊢
    case vc2 =>
      rw [nc9_all _ (by omega)] at hc
      exact absurd hc (by decide)
    case vc3 =>
      to_tableC tableC.match_1.eq_37
      refine ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hC0, rfl⟩, hrb, p_h0.down⟩, h12, h13⟩,
        Nat.le_of_eq (var_L5a2 _)⟩



theorem blk_L5a2 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L5a2" := by
  cfg_block
  measure_hb "L5a2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hC0, hax⟩, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    have hD1 : DWF False d.a.d1 := hC0.1.1.2.2.2.1
    have hn8 := hD1.2.2.2.2.1
    have hfr := hD1.1
    have hte := hD1.2.2.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have hsp9 : d.a.d1.te =@ (t₀.regs.get64 .rsi + 343804#64)
        = (d.a.d1.te.take 9 =@ (t₀.regs.get64 .rsi + 343804#64)
          ⋆ d.a.d1.te.drop 9 =@ (t₀.regs.get64 .rsi + 343813#64)) := by
      have e := Val.append_eq (d.a.d1.te.take 9) (d.a.d1.te.drop 9) (t₀.regs.get64 .rsi + 343804#64)
        (t₀.regs.get64 .rsi + 343813#64) (by rw [List.length_take, hte]; bv_omega)
        (by simp only [List.length_take, List.length_drop, hte]; omega)
      rw [List.take_append_drop] at e
      exact e
    rw [hsp9] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; have hm0 := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hax, h13, Width.bytes, BitVec.mul_one, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try
      (simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add, List.length_drop, hte, hfr]
       omega)
    all_goals try omega
    case vc5 =>
      rename_i s v1 v2 hx1 hx2
      val_split hm0 (t₀.regs.get64 .rsi + 255084#64)
      have L1 := _root_.Mem.Val.loadInt_slice_split
        (a := t₀.regs.get64 .rsi + (BitVec.ofNat 64 d.a.d1.nenv + 255084#64)) (n := 1) hm0 hsplit
        (by rw [off_n _ _ _ (by omega)]; omega) (by omega)
      rw [off_n _ _ _ (by omega)] at L1
      rw [L1, Option.some.injEq] at hx1
      subst hx1
      have hm1 := _root_.Mem.Val.storeInt_slice_split (a := t₀.regs.get64 .rsi + 255084#64)
        (n := 1) hm0 hsplit (by simp only [BitVec.sub_self, BitVec.toNat_zero]; omega) (by omega)
        (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8
          (Int.ofBytes ((d.a.d1.freqRes.drop d.a.d1.nenv).take 1)))))).toInt
      clear hsplit
      val_split hm1 (t₀.regs.get64 .rsi + 343804#64)
      have L2 := _root_.Mem.Val.loadInt_slice_split
        (a := t₀.regs.get64 .rsi + (BitVec.ofNat 64 d.a.d1.nenv + 343804#64)) (n := 1) hm1 hsplit
        (by rw [off_n _ _ _ (by omega)]; simp only [List.length_take, hte]; omega)
        (by simp only [List.length_take, hte]; omega)
      rw [off_n _ _ _ (by omega), tk_take _ _ _ (by omega)] at L2
      rw [L2, Option.some.injEq] at hx2
      subst hx2
      clear hm1 hsplit hm0
      to_tableC tableC.match_1.eq_38
      refine ⟨⟨⟨hC, ⟨by fr_c, by fr_c, by fr_c⟩, i0, gi, d.setCh true (cpA d.a.d1), ih,
        ⟨d, hC0, rfl⟩, hrb, ?_⟩, by fr_c, by fr_c, by fr_c⟩, Nat.le_of_eq (var_L5cc _)⟩
      simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add] at hm
      rw [b1_of _ (by simp; omega), b1_of _ (by simp; omega), tk1 _ _ (by omega),
        tk1 _ _ (by omega), ← splice1 d.a.d1.freqRes 0 _ (by omega)] at hm
      simp only [List.take_zero, List.nil_append, List.drop_drop, Nat.reduceAdd] at hm
      have hj : d.a.d1.te.set 9 (d.a.d1.te.getD d.a.d1.nenv 0) =@ (t₀.regs.get64 .rsi + 343804#64)
          = (d.a.d1.te.take 9 =@ (t₀.regs.get64 .rsi + 343804#64)
            ⋆ ([d.a.d1.te.getD d.a.d1.nenv 0] ++ d.a.d1.te.drop 10)
              =@ (t₀.regs.get64 .rsi + 343813#64)) := by
        rw [splice1 _ _ _ (by omega), List.append_assoc]
        exact Val.append_eq _ _ _ _ (by rw [List.length_take, hte]; bv_omega)
          (by simp only [List.length_take, List.length_drop, List.length_append,
            List.length_singleton, hte]; omega)
      simp only [T, LocW, GbR, GbW, DecF, SbrF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, DataF, cpA, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [hj]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
      simp only [tk1 _ _ (show d.a.d1.nenv < d.a.d1.freqRes.length by omega),
        tk1 _ _ (show d.a.d1.nenv < d.a.d1.te.length by omega)]
end Kraken.Examples.Sbr.DecExt
