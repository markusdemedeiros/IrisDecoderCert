import Kraken.X64.Examples.Sbr.Parse.PsBlkHNAvx

/-!
# `ff_ps_read_data`: the vectorized fixed borders of `num_env = 4` (`0x6d0`)

With the `vmovdqu` store rule and the 16-byte border write.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

section Store
open Lean.Order
variable {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop} {p : Program}

/-- `vmovdqu %xmm, m128`: 16 readable bytes, any alignment. -/
theorem hn_vmovdqu_store_spec (x : AvxReg .W128) (b : Reg64) (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 16).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 16 (s.zmms.get x).toInt } ⦄
      (Directive.instr (.avx .W64 .W128 (.vmovdqu (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx x))) :: p)
    ⦃ Q; E ⦄ :=
  Triple.intro fun s h => by
    simp only [meet_prop_eq_and] at h
    obtain ⟨hsome, hk⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
    intro pc hpl
    obtain ⟨z, rest, hseg, hpl'⟩ := hpl
    rw [after_instr hseg]
    refine step_here hseg (Or.inl ?_)
    simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or]
    simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      hv, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All]
    exact hk _ hpl'

end Store

theorem hn_hdr_wrn {x : PArgs} {c f : List UInt8} (hl : c.length = 764) (o n : Nat) (v : Int)
    (h1 : 44 ≤ o) (h2 : o + n ≤ 0x4c) (hH : HdrOk x c f) (h38 : S38 c f) (hK : Kp x c) :
    HdrOk x (wr c o n v) f ∧ S38 (wr c o n v) f ∧ Kp x (wr c o n v) := by
  have hi : ∀ o', o' + 4 ≤ 44 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' h => i32_wr c o n o' v (by omega) (by omega)
  have hk24 : ((wr c o n v).drop 4).take 0x20 = (c.drop 4).take 0x20 :=
    wr_drop_take_disj c o n 4 0x20 v (by omega) (Or.inl (by omega))
  refine ⟨⟨fun h => ?_, fun h hi4 => ?_⟩, ?_, Kp_wr hK o n v (by omega) h2 (by omega)⟩
  · unfold K24; rw [hk24]; exact hH.1 h
  · rw [hi 4 (by omega)] at hi4; rw [hi 12 (by omega)]; exact hH.2 h hi4
  · unfold S38; rw [hi 40 (by omega)]; exact h38

theorem hn_BS_wrn {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {v : Nat} (hB : BS k Ext x ra t₀ s c f v) (o n : Nat) (w : Int)
    (h1 : 56 ≤ o) (h2 : o + n ≤ 0x4c)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (h13 : s'.regs.get64 .r13 = s.regs.get64 .r13) (h12 : s'.regs.get64 .r12 = s.regs.get64 .r12)
    (hbx : s'.regs.get64 .rbx = s.regs.get64 .rbx) (h10 : s'.regs.get64 .r10 = s.regs.get64 .r10)
    (h8 : Ix x (s'.regs.get64 .r8))
    (hm : s'.dmem =⋆ Fr k Ext x ra t₀ f (wr c o n w) x.idx) :
    BS k Ext x ra t₀ s' (wr c o n w) f v := by
  obtain ⟨⟨⟨hC, ⟨hsp0, hbp0, hf, hP, hbl, h08, hid⟩, -⟩, ⟨h130, h120⟩, hbx0, hK⟩, hH, h38, hv4, hne,
    h58, h100, hb0, -⟩ := hB
  have hcl : c.length = 764 := hP.1
  obtain ⟨hH1, h381, hK1⟩ := hn_hdr_wrn hcl o n w (by omega) h2 hH h38 hK
  refine ⟨⟨⟨hC, ⟨by rw [hsp]; exact hsp0, by rw [hbp]; exact hbp0, hf,
      hn_PsInv_wr_hi hP o n _ (by omega) (by omega), hbl, h08, hid⟩, hm⟩,
    ⟨by rw [h13]; exact h130, by rw [h12]; exact h120⟩, by rw [hbx]; exact hbx0, hK1⟩,
    hH1, h381, hv4, ?_, h58, by rw [h10]; exact h100, ?_, h8⟩
  · show i32 _ 44 = _
    rw [i32_wr _ o n 44 _ (by omega) (by omega)]; exact hne
  · show i32 _ (52 + 4 * 0) = _
    rw [i32_wr _ o n _ _ (by omega) (by omega)]; exact hb0

theorem hn_take_wr_in (c : List UInt8) (o n d : Nat) (v : Int) (hl : o + n ≤ c.length)
    (hd : d + 4 ≤ n) :
    ((wr c o n v).drop (o + d)).take 4 = ((Int.toBytes n v).drop d).take 4 := by
  rw [← wr_drop_take_same c o n v hl, List.drop_take, List.take_take,
    show min 4 (n - d) = 4 by omega, List.drop_drop]

/-- The four fixed borders of `num_env = 4`. -/
abbrev hnV4 : BitVec 128 := 0x0000001f000000170000000f00000007#128

theorem hn_bordTo_vec {c : List UInt8} (hl : c.length = 764) (hb0 : bord c 0 = -1) :
    BordTo (wr c 56 16 hnV4.toInt) 4 := by
  have b0 : bord (wr c 56 16 hnV4.toInt) 0 = -1 := by
    show i32 _ (52 + 4 * 0) = _
    rw [i32_wr _ 56 16 _ _ (by omega) (by omega)]; exact hb0
  have bv : ∀ d, d < 4 → bord (wr c 56 16 hnV4.toInt) (d + 1)
      = (BitVec.ofNat 32 (Nat.ofBytes (((Int.toBytes 16 hnV4.toInt).drop (4 * d)).take 4))).toInt := by
    intro d hd
    show (BitVec.ofNat 32 (Nat.ofBytes (((wr c 56 16 hnV4.toInt).drop (52 + 4 * (d + 1))).take 4))).toInt = _
    rw [show 52 + 4 * (d + 1) = 56 + 4 * d by omega, hn_take_wr_in c 56 16 (4 * d) _ (by omega) (by omega)]
  have b1 : bord (wr c 56 16 hnV4.toInt) 1 = 7 := by rw [bv 0 (by omega)]; decide
  have b2 : bord (wr c 56 16 hnV4.toInt) 2 = 15 := by rw [bv 1 (by omega)]; decide
  have b3 : bord (wr c 56 16 hnV4.toInt) 3 = 23 := by rw [bv 2 (by omega)]; decide
  have b4 : bord (wr c 56 16 hnV4.toInt) 4 = 31 := by rw [bv 3 (by omega)]; decide
  refine ⟨b0, fun e he => ?_, fun e he => ?_⟩
  · have : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · simp only [Nat.zero_add, b0, b1]; omega
    · simp only [Nat.reduceAdd, b1, b2]; omega
    · simp only [Nat.reduceAdd, b2, b3]; omega
    · simp only [Nat.reduceAdd, b3, b4]; omega
  · have : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · simp only [b0]; omega
    · simp only [b1]; omega
    · simp only [b2]; omega
    · simp only [b3]; omega
    · simp only [b4]; omega

set_option maxRecDepth 20000 in
/-- The vector fill: borders `1..4 = 7, 15, 23, 31`; `num_env = 4` exits to the header. -/
theorem blk_L6d0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.L6d0" := by
  cfg_block
  measure_hb "L6d0"
    intro n
    simp only [tab_L6d0, var_L6d0, tab_L715, var_L715, tab_L6f5, var_L6f5]
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hB, hax, hsi, hx0, hx1, hx2⟩, hn⟩ := hs₀
    have hB' := hB
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hf, hP, hbl, h08, hid⟩, hm⟩, ⟨h13, h12⟩, hbx, hKp⟩, hH, h38, hv4, hne,
      h58, h10, hb0, hix⟩ := hB'
    have hcl : c.length = 764 := hP.1
    have hr10 : s₀.regs.get64 .r10 = 4#64 := BitVec.eq_of_toNat_eq (by rw [h10]; rfl)
    have e0 : s₀.regs.get64 .rbx + s₀.regs.get64 .rax * BitVec.ofNat 64 4 + Int64.toBitVec 56
        = arg2 t₀ + BitVec.ofNat 64 56 := by
      rw [hbx, hax]; simp
    have l1 := Fr_c_isSome hm hcl 56 16 (by omega)
    have hst := fun w => Fr_c_store hm hcl 56 16 (by omega) w
    rw [← e0] at l1 hst
    have P := PLift.up hst
    clear hst
    have hV : BitVec.packedBinOp 32 (· + ·)
        (BitVec.packedBinOp 32 (fun x _ => if ((2#128 : BitVec 128).extractLsb' 0 64).toNat > 31 then 0#32
          else x >>> ((2#128 : BitVec 128).extractLsb' 0 64).toNat)
          (BitVec.packedBinOp 32 (fun x _ => if (5 : UInt8).toNat > 31 then 0#32 else x <<< (5 : UInt8).toNat)
            0x00000004000000030000000200000001#128 0x00000004000000030000000200000001#128)
          (BitVec.packedBinOp 32 (fun x _ => if (5 : UInt8).toNat > 31 then 0#32 else x <<< (5 : UInt8).toNat)
            0x00000004000000030000000200000001#128 0x00000004000000030000000200000001#128))
        (BitVec.allOnes 128) = hnV4 := by
      simp [BitVec.packedBinOp] <;> first | rfl | decide
    vcgen [hn_vpsrldx_spec, hn_vmovdqu_store_spec]
    all_goals try call_simp
    all_goals (have hs := ‹_ = s₀›; subst hs)
    case vc1 => exact l1
    case vc2 =>
      rename_i hj _
      rw [hn_nz64, hsi, hax] at hj
      exact absurd hj (by simp)
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L715") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L715 _ _ _ _ _ _).mpr ?_
        refine toHdr (hn_BS_wrn hB 56 16 hnV4.toInt (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          (hn_bordTo_vec hcl hb0)
        all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
        all_goals try rfl
        all_goals try exact hix
        simp only [RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, reduceCtorEq,
          not_false_eq_true, hx0, hx1, hx2]
        first
          | (simp only [hV]; exact P.down _)
          | (simp only [BitVec.packedBinOp]; exact P.down _)
      · rw [var_L715]; subst hn; exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc4 =>
      rename_i hj1 hj2 _
      rw [CondCode.interp_z, StatusFlags.zf_from_result, hsi, hr10] at hj2
      exact absurd hj2 (by simp)

end Kraken.Examples.Sbr.Ps
