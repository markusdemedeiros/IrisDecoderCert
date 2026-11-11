import Kraken.X64.Examples.Sbr.Parse.DecExtMem

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: `sbr_turnoff` (inlined)
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
/-- `start` and `ready` as one 8-byte cell (the `movq $0`). -/
theorem sr_merge (a : BitVec 64) (c : Nat) (y z : BitVec 32) (F : Mem 64 → Prop) :
    cell4 (a + BitVec.ofNat 64 c) y ⋆ (cell4 (a + BitVec.ofNat 64 (c + 4)) z ⋆ F)
      = (Int.toBytes 4 y.toInt ++ Int.toBytes 4 z.toInt) =@ (a + BitVec.ofNat 64 c) ⋆ F := by
  rw [val_split2 (a + BitVec.ofNat 64 c) (a + BitVec.ofNat 64 (c + 4)) y z
    (by rw [BitVec.add_assoc, ← BitVec.ofNat_add])]
  ac_rfl

omit [CodeEnv] in
theorem sr_merge4 (a : BitVec 64) (y z : BitVec 32) (F : Mem 64 → Prop) :
    cell4 (a + 166180#64) y ⋆ (cell4 (a + 166184#64) z ⋆ F)
      = (Int.toBytes 4 y.toInt ++ Int.toBytes 4 z.toInt) =@ (a + 166180#64) ⋆ F :=
  sr_merge a 166180 y z F

omit [CodeEnv] in
theorem TabF_sr (x : Args) (a b : BitVec 32) (p : BitVec 64) :
    TabF { x with start := a, ready := b } p = TabF x p := rfl

omit [CodeEnv] in
theorem AcF_sr (x : Args) (a b sr : BitVec 32) (p : BitVec 64) :
    AcF p { x with start := a, ready := b } sr = AcF p x sr := rfl

omit [CodeEnv] in
theorem tb8_zero : Int.toBytes 4 (0#32).toInt ++ Int.toBytes 4 (0#32).toInt
    = Int.toBytes 8 (0#64).toInt := by decide

theorem blk_L527 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L527" := by
  cfg_block
  measure_hb "L527"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, hI, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, SbrS, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    simp only [sr_merge4] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, trivial, d.off1, ih, ⟨d, hI, rfl⟩, hih, ?_⟩,
      Nat.le_of_eq (var_L53d _)⟩
    simp only [DecF, SbrF, SbrS, sbrA, arg0, arg1, DS.off1, TabF_sr, AcF_sr, BitVec.add_assoc,
      BitVec.reduceAdd]
    simp only [sr_merge4, BitVec.ofNat_eq_ofNat, tb8_zero]
    sep_close hm


omit [CodeEnv] in
theorem TabF_to (x : Args) (p : BitVec 64) : TabF x.turnoff p = TabF x p := rfl

omit [CodeEnv] in
theorem AcF_to (x : Args) (sr : BitVec 32) (p : BitVec 64) : AcF p x.turnoff sr = AcF p x sr := rfl

omit [CodeEnv] in
theorem tb_32 : Int.toBytes 4 (32#32).toInt = Int.toBytes 4 ((32 : Nat) : Int) := by decide

omit [CodeEnv] in
theorem z1 : Int.toBytes 4 (BitVec.ofNat 32 0).toInt = Int.toBytes 4 0 := by decide
omit [CodeEnv] in
theorem z2 : Int.toBytes 4 (0 : BitVec 32).toInt = Int.toBytes 4 0 := by decide
omit [CodeEnv] in
theorem z3 : Int.toBytes 4 ((0 : Nat) : Int) = Int.toBytes 4 0 := by decide

omit [CodeEnv] in
theorem tb_0 : Int.toBytes 4 (0#32).toInt = Int.toBytes 4 ((0 : Nat) : Int) := by decide

theorem blk_L53d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L53d" := by
  cfg_block
  measure_hb "L53d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, ⟨d₀, hT, rfl⟩, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, SbrS, sbrA, DS.off1, TabF_sr, AcF_sr, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, trivial, d₀.off2, ih, ⟨d₀, hT, rfl⟩, hih, ?_⟩,
      Nat.le_of_eq (var_L553 _)⟩
    simp only [DecF, SbrF, SbrS, sbrA, arg0, arg1, DS.off2, TabF_to, AcF_to, Args.turnoff,
      BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.reduceSetWidth] at hm
    try simp only [BitVec.ofNat_eq_ofNat] at hm ⊢
    simp only [tb_32] at hm
    simp only [c4, cell4, z1, z2, z3] at hm ⊢
    sep_close hm


theorem blk_L553 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L553" := by
  cfg_block
  measure_hb "L553"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, ⟨d₀, hT, rfl⟩, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, DataF, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    dx_br hm
    sep_pull hm [Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
        =@ (t₀.regs.get64 .rsi + 269672#64),
      Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
        =@ (t₀.regs.get64 .rsi + 180904#64)] as R hR
    have h1 := Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    have h2 := Block.sep_intro (Int.toBytes_length _ _) (by decide) (Mem.ac (H₂ :=
      Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
        =@ (t₀.regs.get64 .rsi + 180904#64) ⋆ (4 ?@ (t₀.regs.get64 .rsi + 269672#64) ⋆ R)) h1)
    subst hR
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, trivial, d₀.off2, ih, ⟨d₀, hT, rfl⟩, hih, ?_⟩,
      Nat.le_of_eq (var_L569 _)⟩
    simp only [T, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
    sep_close h2


omit [CodeEnv] in
/-- `spectrum_params` as the 4 bytes of the `movl` and the 2 of the `movw`. -/
theorem sp_split (l₁ l₂ : List UInt8) (a : BitVec 64) (h1 : l₁.length = 4) (h2 : l₂.length = 2) :
    (l₁ ++ l₂) =@ (a + 166204#64) = l₁ =@ (a + 166204#64) ⋆ l₂ =@ (a + 166208#64) :=
  Val.append_eq _ _ _ _ (by rw [h1, BitVec.add_assoc]; rfl) (by omega)

omit [CodeEnv] in
theorem TabF_lit (x : Args) (p : BitVec 64) :
    TabF { x with start := 0, ready := 0, kx1 := 32, m1 := 0 } p = TabF x p := rfl

omit [CodeEnv] in
theorem AcF_lit (x : Args) (sr : BitVec 32) (p : BitVec 64) :
    AcF p { x with start := 0, ready := 0, kx1 := 32, m1 := 0 } sr = AcF p x sr := rfl

omit [CodeEnv] in
theorem rep6 : List.replicate 6 (0xff : UInt8) = Int.toBytes 4 (BitVec.setWidth 32 4294967295#64).toInt
    ++ Int.toBytes 2 (BitVec.setWidth 16 65535#64).toInt := by decide

theorem einv_off {PI : List UInt8 → Prop} {X : XA} {d₀ : DS} (hT : TInv PI X d₀) :
    EInv PI X d₀.off := by
  obtain ⟨hA, ⟨hl, -, -, hL⟩, hP, hK, hsi⟩ := hT
  obtain ⟨h1, h2⟩ := mi_turnoff (s := (d₀.a, d₀.h)) hA
  exact ⟨h1, h2, ⟨rfl, rfl, rfl, hL⟩, hP, hK, hsi⟩

theorem blk_L569 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L569" := by
  cfg_block
  measure_hb "L569"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, ⟨d₀, hT, rfl⟩, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [T, DecF, SbrF, SbrS, sbrA, DS.off2, TabF_to, AcF_to, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    have hl : d₀.sp.length = 6 := hT.2.1.1
    rw [← List.take_append_drop 4 d₀.sp, sp_split _ _ _ (by simp [hl]) (by simp [hl])] at hm
    have hl4 : (List.take 4 d₀.sp).length = 4 := by simp [hl]
    have hl2 : (List.drop 4 d₀.sp).length = 2 := by simp [hl]
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, BitVec.reduceToNat, Nat.reduceMod, Nat.reduceEqDiff]
    all_goals try (simp only [hl4, hl2, BitVec.sub_self, BitVec.toNat_zero, Nat.reducePow]; omega)
    dx_br hm
    all_goals try (simp only [hl4, hl2, BitVec.sub_self, BitVec.toNat_zero, Nat.reducePow]; omega)
    simp only [BitVec.sub_self, BitVec.toNat_zero, List.take_zero, List.nil_append, Nat.zero_add,
      List.drop_eq_nil_of_le (Nat.le_of_eq hl4), List.drop_eq_nil_of_le (Nat.le_of_eq hl2),
      List.append_nil] at hm
    refine ⟨⟨hC, ⟨trivial, trivial, trivial⟩, trivial, d₀.off, ih, einv_off hT, hih, ?_⟩,
      Nat.le_of_eq (var_L57e _)⟩
    simp only [T, DecF, SbrF, SbrS, sbrA, arg0, arg1, DS.off, TabF_to, AcF_to, Hid.turnoff,
      BitVec.add_assoc, BitVec.reduceAdd]
    rw [rep6, sp_split _ _ _ (by decide) (by decide)]
    simp only [c4, cell4, z1, z2, z3] at hm ⊢
    sep_close hm


/-- `T` with `av_log`'s frame at the head: the return slot, the callee's reservation, `Ext`. -/
theorem T_ext (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (LW : Mem 64 → Prop) (d : DS) (ih : BitVec 32) :
    ∃ F, T kc Ext X ra t₀ FR LW d ih = 8 ?@ (t₀.regs.get64 .rsp - 0x70#64)
      ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Ext ⋆ F)) := by
  refine ⟨LW ⋆ ((SbrF d (sbrA t₀) ⋆ (GhW (arg2 t₀) X ih ⋆ (AvW (arg0 t₀) d.a
    ⋆ (AcF (arg0 t₀) d.a X.sr ⋆ (BufW X.r ⋆ Grid.JtW))))) ⋆ FR (Rest X.R ra t₀)), ?_⟩
  simp only [T, DecF]; ac_rfl

theorem blk_L50b (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hAv : AvLogSpec Ext kc) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L50b" := by
  cfg_block
  measure_hb "L50b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, h12, d, ih, hI, hih, hm⟩, hn⟩ := hs₀
    var_n hn
    have hl1 : (s₀.dmem.loadInt (t₀.regs.get64 .rdi + 8#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, DecF, AvW, arg0] at hm'
      sep_mem hm'
    have hl2 : (s₀.dmem.loadInt (t₀.regs.get64 .rsp - 88#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, LocE] at hm'
      sep_mem hm'
    have hT : TInv PI X d := ⟨hI.1.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2⟩
    obtain ⟨F, hF⟩ := T_ext kc Ext X ra t₀ (Saved t₀) (LocE t₀) d ih
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      simp only [h12, AddrIndex.offset64_none, add_ofNat0]
      rw [show (8 : Int64).toBitVec = 8#64 from rfl]
      exact hl1
    case vc2 =>
      simp only [hbp, AddrIndex.offset64_none, add_ofNat0]
      rw [show t₀.regs.get64 .rsp - 8#64 + (-80 : Int64).toBitVec = t₀.regs.get64 .rsp - 88#64
        from by rw [show (-80 : Int64).toBitVec = -80#64 from rfl]; bv_omega]
      exact hl2
    case vc3 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e70]; exact hpush _
      · rw [e70] at hpost
        obtain ⟨hsp', hbp', ⟨-, h12', -, h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, ?_, d, ih, hT, hih, ?_⟩, Nat.le_of_eq (var_L527 _)⟩
        · rw [hsp']; bv_omega
        all_goals try (first | rw [hbp']; exact hbp | rw [h14']; exact h14 | rw [h12']; exact h12)
        exact (congrFun hF s'.dmem).mpr hm'

end Kraken.Examples.Sbr.DecExt
