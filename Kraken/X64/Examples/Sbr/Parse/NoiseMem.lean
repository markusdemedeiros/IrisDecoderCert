import Kraken.X64.Examples.Sbr.Parse.NoiseBase
import Kraken.X64.Examples.Sbr.Parse.DtdfBase

/-!
# `read_sbr_noise`: the accesses

Each atom of `T` brought to the head by an AC path (`eq_r`/`eq_l`/`eq_h`/`eq_last` of
`DtdfBase.lean`), then one access lemma.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (GbW)
open Kraken.Examples.Sbr.Dtdf (eq_r eq_l eq_h eq_last)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

section
variable {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
  {LF : Mem 64 → Prop} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {i : BitVec 32} {m : Mem 64}

theorem T_slot : ∃ F, T k Ext x ra t₀ LF FR i = 8 ?@ (t₀.regs.get64 .rsp - 0x60#64) ⋆ F :=
  ⟨_, eq_h⟩

theorem T_LF : ∃ F, T k Ext x ra t₀ LF FR i = LF ⋆ F :=
  ⟨_, eq_r (eq_r eq_h)⟩

theorem T_cpl : ∃ F, T k Ext x ra t₀ LF FR i = cell4 (arg1 t₀ + 0x3c#64) x.cpl ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l eq_h)))⟩

theorem T_nq : ∃ F, T k Ext x ra t₀ LF FR i = c4 (arg1 t₀ + 0x4c1e8#64) x.nq ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r eq_h))))⟩

theorem T_nn : ∃ F, T k Ext x ra t₀ LF FR i = c4 (arg3 t₀ + 0x18#64) x.nn ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r eq_h)))))⟩

theorem T_df : ∃ F, T k Ext x ra t₀ LF FR i = 2 ?@ (arg3 t₀ + 0x25#64) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r eq_h))))))⟩

theorem T_nfq : ∃ F, T k Ext x ra t₀ LF FR i = 15 ?@ (arg3 t₀ + 0x15a50#64) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r eq_h)))))))⟩

theorem T_av : ∃ F, T k Ext x ra t₀ LF FR i = c8 (arg0 t₀ + 8#64) x.avctx ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r eq_h))))))))⟩

theorem T_buf : ∃ F, T k Ext x ra t₀ LF FR i = c8 (arg2 t₀) x.buf ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_l (eq_h)))))))))))⟩

theorem T_i (j : BitVec 32) : ∃ F, T k Ext x ra t₀ LF FR i = cell4 (arg2 t₀ + 8#64) i ⋆ F
    ∧ T k Ext x ra t₀ LF FR j = cell4 (arg2 t₀ + 8#64) j ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_h)))))))))))),
    eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_h))))))))))))⟩

theorem T_p8 : ∃ F, T k Ext x ra t₀ LF FR i = cell4 (arg2 t₀ + 0x10#64) x.p8 ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_last)))))))))))))⟩

theorem T_bs : ∃ F, T k Ext x ra t₀ LF FR i = Blocks [(x.buf, x.L)] ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_h)))))))))))⟩

theorem T_vlc : ∃ F, T k Ext x ra t₀ LF FR i = VlcW x.v ⋆ F :=
  ⟨_, eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_r (eq_h))))))))))))⟩

/-! Loads and stores -/

theorem T_ld_nq (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg1 t₀ + 0x4c1e8#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.nq : Int))) := by
  obtain ⟨F, hF⟩ := (T_nq : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_nn (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg3 t₀ + 0x18#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.nn : Int))) := by
  obtain ⟨F, hF⟩ := (T_nn : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_cpl (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg1 t₀ + 0x3c#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.cpl.toInt)) := by
  obtain ⟨F, hF⟩ := (T_cpl : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_av (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg0 t₀ + 8#64) 8 = some (Int.ofBytes (Int.toBytes 8 x.avctx.toInt)) := by
  obtain ⟨F, hF⟩ := (T_av : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem T_ld_buf (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg2 t₀) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := by
  obtain ⟨F, hF⟩ := (T_buf : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem T_ld_i (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg2 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) := by
  obtain ⟨F, hF, -⟩ := (T_i i : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F ∧ _)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_ld_p8 (h : m =⋆ T k Ext x ra t₀ LF FR i) :
    m.loadInt (arg2 t₀ + 0x10#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) := by
  obtain ⟨F, hF⟩ := (T_p8 : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 4 F m h (Int.toBytes_length 4 _) (by omega)

theorem T_st_i (h : m =⋆ T k Ext x ra t₀ LF FR i) (j : BitVec 32) :
    m.storeInt (arg2 t₀ + 8#64) 4 j.toInt =⋆ T k Ext x ra t₀ LF FR j := by
  obtain ⟨F, hF, hF'⟩ := (T_i j : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F ∧ _)
  rw [hF] at h
  rw [hF']
  exact storeInt_sep _ 4 _ _ m ⟨h, Int.toBytes_length 4 _⟩ j.toInt

theorem T_ld_df (h : m =⋆ T k Ext x ra t₀ LF FR i) (a : BitVec 64)
    (ha : (a - (arg3 t₀ + 0x25#64)).toNat + 1 ≤ 2) : (m.loadInt a 1).isSome = true := by
  obtain ⟨F, hF⟩ := (T_df : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact Block.loadInt_isSome h ha

theorem T_ld_nfq (h : m =⋆ T k Ext x ra t₀ LF FR i) (a : BitVec 64) (n : Nat)
    (ha : (a - (arg3 t₀ + 0x15a50#64)).toNat + n ≤ 15) : (m.loadInt a n).isSome = true := by
  obtain ⟨F, hF⟩ := (T_nfq : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact Block.loadInt_isSome h ha

theorem T_st_nfq (h : m =⋆ T k Ext x ra t₀ LF FR i) (a : BitVec 64) (n : Nat)
    (ha : (a - (arg3 t₀ + 0x15a50#64)).toNat + n ≤ 15) (v : Int) :
    m.storeInt a n v =⋆ T k Ext x ra t₀ LF FR i := by
  obtain ⟨F, hF⟩ := (T_nfq : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h ⊢
  exact Block.storeInt h ha v

theorem T_ld_bs (h : m =⋆ T k Ext x ra t₀ LF FR i) (off : BitVec 64) (n : Nat)
    (hin : off.toNat + n ≤ x.L) : (m.loadInt (x.buf + off) n).isSome = true := by
  obtain ⟨F, hF⟩ := (T_bs : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact Blocks.loadInt_isSome h (Blocks.Inside.base_add hin)

theorem T_vlcw (h : m =⋆ T k Ext x ra t₀ LF FR i) : ∃ F, m =⋆ VlcW x.v ⋆ F := by
  obtain ⟨F, hF⟩ := (T_vlc : ∃ F, T k Ext x ra t₀ LF FR i = _ ⋆ F)
  rw [hF] at h
  exact ⟨F, h⟩

/-! The locals -/

theorem L_d : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i
    = c8 (t₀.regs.get64 .rsp - 0x58#64) (arg3 t₀) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l eq_h))⟩

theorem L_d15 : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i
    = c8 (t₀.regs.get64 .rsp - 0x50#64) (arg3 t₀ + 0x15a50#64) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r eq_h)))⟩

theorem L_ac : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i
    = c8 (t₀.regs.get64 .rsp - 0x48#64) (arg0 t₀) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r eq_h))))⟩

theorem L_th : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i
    = c8 (t₀.regs.get64 .rsp - 0x40#64) (TH x t₀).p ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r eq_h)))))⟩

theorem L_blk : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i
    = 8 ?@ (t₀.regs.get64 .rsp - 0x38#64) ⋆ F :=
  ⟨_, eq_r (eq_r (eq_l (eq_r (eq_r (eq_r eq_last)))))⟩

theorem L_ld_d (h : m =⋆ T k Ext x ra t₀ (Loc x t₀) FR i) :
    m.loadInt (t₀.regs.get64 .rsp - 0x58#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) := by
  obtain ⟨F, hF⟩ := (L_d : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem L_ld_d15 (h : m =⋆ T k Ext x ra t₀ (Loc x t₀) FR i) :
    m.loadInt (t₀.regs.get64 .rsp - 0x50#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀ + 0x15a50#64).toInt)) := by
  obtain ⟨F, hF⟩ := (L_d15 : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem L_ld_ac (h : m =⋆ T k Ext x ra t₀ (Loc x t₀) FR i) :
    m.loadInt (t₀.regs.get64 .rsp - 0x48#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀).toInt)) := by
  obtain ⟨F, hF⟩ := (L_ac : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem L_ld_th (h : m =⋆ T k Ext x ra t₀ (Loc x t₀) FR i) :
    m.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8 = some (Int.ofBytes (Int.toBytes 8 (TH x t₀).p.toInt)) := by
  obtain ⟨F, hF⟩ := (L_th : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i = _ ⋆ F)
  rw [hF] at h
  exact loadInt_sep _ _ 8 F m h (Int.toBytes_length 8 _) (by omega)

theorem L_ld_blk (h : m =⋆ T k Ext x ra t₀ (Loc x t₀) FR i) (a : BitVec 64) (n : Nat)
    (ha : (a - (t₀.regs.get64 .rsp - 0x38#64)).toNat + n ≤ 8) : (m.loadInt a n).isSome = true := by
  obtain ⟨F, hF⟩ := (L_blk : ∃ F, T k Ext x ra t₀ (Loc x t₀) FR i = _ ⋆ F)
  rw [hF] at h
  exact Block.loadInt_isSome h ha

end

/-! Packs of load facts at the registers of a state (`def`s, so that `simp … at *` leaves
them alone), and their accessors. -/

section
variable {k : Nat} {Ext : Mem 64 → Prop} {x : NArgs} {ra : Int64} {t₀ : MachineData}
  {LF : Mem 64 → Prop} {FR : (Mem 64 → Prop) → Mem 64 → Prop} {i : BitVec 32} {s : MachineData}

/-- The loads of `*gb` (`index`, `buffer`, `size_in_bits_plus8`). -/
def GbL (x : NArgs) (i : BitVec 32) (s : MachineData) : Prop :=
  s.dmem.loadInt (s.regs.get64 .rdx + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rdx) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rdx + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt))

theorem GbL.of (h : s.dmem =⋆ T k Ext x ra t₀ LF FR i) (hrdx : s.regs.get64 .rdx = arg2 t₀) :
    GbL x i s := by
  unfold GbL; rw [hrdx]; exact ⟨T_ld_i h, T_ld_buf h, T_ld_p8 h⟩

theorem GbL.ld_i (h : GbL x i s) :
    s.dmem.loadInt (s.regs.get64 .rdx + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 i.toInt)) := h.1
theorem GbL.ld_buf (h : GbL x i s) :
    s.dmem.loadInt (s.regs.get64 .rdx) 8 = some (Int.ofBytes (Int.toBytes 8 x.buf.toInt)) := h.2.1
theorem GbL.ld_p8 (h : GbL x i s) :
    s.dmem.loadInt (s.regs.get64 .rdx + 16#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.p8.toInt)) :=
  h.2.2

/-- The load of `sbr->n_q`. -/
def NqL (x : NArgs) (s : MachineData) : Prop :=
  s.dmem.loadInt (s.regs.get64 .rsi + 311784#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.nq : Int)))

theorem NqL.of (h : s.dmem =⋆ T k Ext x ra t₀ LF FR i) (hrsi : s.regs.get64 .rsi = arg1 t₀) :
    NqL x s := by
  unfold NqL; rw [hrsi]; exact T_ld_nq h

theorem NqL.ld (h : NqL x s) :
    s.dmem.loadInt (s.regs.get64 .rsi + 311784#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.nq : Int))) :=
  h

/-- The loads of the locals at `rbp - 0x50`, `-0x48`, `-0x40`, `-0x38`, `-0x30`, `-0x29`. -/
def LcL (x : NArgs) (t₀ : MachineData) (s : MachineData) : Prop :=
  s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551536#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551544#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀ + 0x15a50#64).toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551552#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀).toInt))
  ∧ s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551560#64) 8
      = some (Int.ofBytes (Int.toBytes 8 (TH x t₀).p.toInt))
  ∧ (s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551568#64) 4).isSome = true
  ∧ (s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551575#64) 1).isSome = true

theorem LcL.of (h : s.dmem =⋆ T k Ext x ra t₀ (Loc x t₀) FR i)
    (hbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64) : LcL x t₀ s := by
  unfold LcL; rw [hbp]
  have e1 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551536#64 = t₀.regs.get64 .rsp - 0x58#64 := by
    bv_omega
  have e2 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551544#64 = t₀.regs.get64 .rsp - 0x50#64 := by
    bv_omega
  have e3 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551552#64 = t₀.regs.get64 .rsp - 0x48#64 := by
    bv_omega
  have e4 : t₀.regs.get64 .rsp - 8#64 + 18446744073709551560#64 = t₀.regs.get64 .rsp - 0x40#64 := by
    bv_omega
  rw [e1, e2, e3, e4]
  refine ⟨L_ld_d h, L_ld_d15 h, L_ld_ac h, L_ld_th h, L_ld_blk h _ 4 ?_, L_ld_blk h _ 1 ?_⟩
  · have : t₀.regs.get64 .rsp - 8#64 + 18446744073709551568#64 - (t₀.regs.get64 .rsp - 0x38#64)
        = 0#64 := by bv_omega
    rw [this]; decide
  · have : t₀.regs.get64 .rsp - 8#64 + 18446744073709551575#64 - (t₀.regs.get64 .rsp - 0x38#64)
        = 7#64 := by bv_omega
    rw [this]; decide

theorem LcL.d (h : LcL x t₀ s) : s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551536#64) 8
    = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) := h.1
theorem LcL.d15 (h : LcL x t₀ s) : s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551544#64) 8
    = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀ + 0x15a50#64).toInt)) := h.2.1
theorem LcL.ac (h : LcL x t₀ s) : s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551552#64) 8
    = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀).toInt)) := h.2.2.1
theorem LcL.th (h : LcL x t₀ s) : s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551560#64) 8
    = some (Int.ofBytes (Int.toBytes 8 (TH x t₀).p.toInt)) := h.2.2.2.1
theorem LcL.w (h : LcL x t₀ s) :
    (s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551568#64) 4).isSome = true := h.2.2.2.2.1
theorem LcL.b (h : LcL x t₀ s) :
    (s.dmem.loadInt (s.regs.get64 .rbp + 18446744073709551575#64) 1).isSome = true := h.2.2.2.2.2

end

omit [CodeEnv] in
/-- `lea (%r12,%r12,4)`. -/
theorem lea5 (c : Nat) (hc : c < 2 ^ 60) :
    BitVec.ofNat 64 c + BitVec.ofNat 64 c * 4#64 = BitVec.ofNat 64 (5 * c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
/-- The first-level window `w >> 23`, zero-extended. -/
theorem win9 (w : BitVec 32) : (BitVec.setWidth 64 (w.ushiftRight 23)).toNat < 512 := by
  rw [BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

omit [CodeEnv] in
theorem succ64 (c : Nat) (hc : c + 1 < 2 ^ 64) :
    BitVec.ofNat 64 c + 1#64 = BitVec.ofNat 64 (c + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem add5 (a : BitVec 64) (c : Nat) (hc : 5 * c + 5 < 2 ^ 64) :
    a + BitVec.ofNat 64 (5 * c) + 5#64 = a + BitVec.ofNat 64 (5 * (c + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

omit [CodeEnv] in
theorem nat32to64 (n : Nat) (h : n < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int)) = BitVec.ofNat 64 n := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-- A flag hypothesis of a `cmp`/`test` as an order/equation of the operands' values. -/
macro "flg" h:ident : tactic => `(tactic| (
    simp only [CondCode.interp_nz, CondCode.interp_z,
      CondCode.interp_c, CondCode.interp_nc, StatusFlags.cf_from_result,
      StatusFlags.zf_from_result, BitVec.unsigned_eq] at $h:ident
    simp only [BitVec.sub_cf_eq_decide_lt, BitVec.sub_beq_zero] at $h:ident
    simp only [Bool.not_eq_true', Bool.not_eq_false', Bool.not_eq_eq_eq_not,
      Bool.not_true, Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not,
      BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.ofInt_natCast,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.reduceSetWidth, BitVec.reduceToNat,
      Nat.reducePow, Nat.reduceMod] at $h:ident))

/-- The register/address normalization after `vcgen`. -/
macro "nnorm" : tactic => `(tactic| simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_scale4, AddrIndex.offset64_scale8,
      AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      Nat.reduceSub, BitVec.setWidth_32_64_32] at *)

end Kraken.Examples.Sbr.Noise
