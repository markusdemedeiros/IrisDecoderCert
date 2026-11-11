import Kraken.X64.Examples.Sbr.Parse.EnvFrame
import Kraken.X64.Examples.Sbr.Parse.LibGb
import Kraken.X64.Examples.Sbr.Parse.EnvVar

/-!
# `read_sbr_envelope`: footprint access lemmas

A block brings the cell it touches to the front of `T` with a focus equation
(`T_<atom> : ∃ F, T … = X ⋆ F`, the path through the right-nested footprint) and uses one access
lemma. The frame slots are in `EnvFrame.lean`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (eq_r eq_l eq_h GbW gb_load_buf gb_load_idx gb_load_p8
  gb_store_idx blocks_load)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Env

theorem eq_t {A B : Mem 64 → Prop} : A ⋆ B = B ⋆ A := Std.ExtHashMap.sep_comm _ _

variable [CodeEnv]

section Focus

variable (k : Nat) (Ext : Mem 64 → Prop) (x : EArgs) (ra : Int64) (t₀ : MachineData) (fv : FV)
  (i : BitVec 32)

theorem T_df : ∃ F, T k Ext x ra t₀ fv i = 9 ?@ (arg3 t₀ + 0x1c#64) ⋆ F := by
  simp only [T, EF, ChE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_l (eq_r (eq_r eq_h)))))))⟩

theorem T_fr : ∃ F, T k Ext x ra t₀ fv i = x.v.freqRes =@ (arg3 t₀ + 0xc#64) ⋆ F := by
  simp only [T, EF, ChE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_l (eq_r eq_h))))))⟩

theorem T_nenv : ∃ F, T k Ext x ra t₀ fv i = c4 (arg3 t₀ + 8#64) x.v.nenv ⋆ F := by
  simp only [T, EF, ChE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_l eq_h)))))⟩

theorem T_amp : ∃ F, T k Ext x ra t₀ fv i = cell4 (arg3 t₀ + 0x64#64) x.amp ⋆ F := by
  simp only [T, EF, ChE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_l (eq_r (eq_r (eq_r eq_h))))))))⟩

theorem T_efq : ∃ F, T k Ext x ra t₀ fv i = 432 ?@ (arg3 t₀ + 0x151e0#64) ⋆ F := by
  simp only [T, EF, ChE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_l (eq_r (eq_r (eq_r (eq_r eq_h)))))))))⟩

theorem T_ts : ∃ F, T k Ext x ra t₀ fv i = 12 ?@ (arg3 t₀ + 0x15ab4#64) ⋆ F := by
  simp only [T, EF, ChE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_l (eq_r (eq_r (eq_r (eq_r eq_t)))))))))⟩

theorem T_usac : ∃ F, T k Ext x ra t₀ fv i = cell4 (arg1 t₀ + 0x10#64) x.usac ⋆ F := by
  simp only [T, EF, SbrE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l eq_h))))))⟩

theorem T_it : ∃ F, T k Ext x ra t₀ fv i = cell4 (arg1 t₀ + 0x14#64) x.interTes ⋆ F := by
  simp only [T, EF, SbrE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r eq_h)))))))⟩

theorem T_cpl : ∃ F, T k Ext x ra t₀ fv i = cell4 (arg1 t₀ + 0x3c#64) x.coupling ⋆ F := by
  simp only [T, EF, SbrE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r (eq_r eq_h))))))))⟩

theorem T_n0 : ∃ F, T k Ext x ra t₀ fv i = c4 (arg1 t₀ + 0x4c1e0#64) x.n0 ⋆ F := by
  simp only [T, EF, SbrE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r (eq_r (eq_r eq_h)))))))))⟩

theorem T_n1 : ∃ F, T k Ext x ra t₀ fv i = c4 (arg1 t₀ + 0x4c1e4#64) x.n1 ⋆ F := by
  simp only [T, EF, SbrE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_l (eq_r (eq_r (eq_r eq_t)))))))))⟩

theorem T_gb : ∃ F, T k Ext x ra t₀ fv i = GbE (arg2 t₀) x i ⋆ F := by
  simp only [T, EF]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r eq_h))))))⟩

theorem T_avctx : ∃ F, T k Ext x ra t₀ fv i = c8 (arg0 t₀ + 8#64) x.avctx ⋆ F := by
  simp only [T, EF, InE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r eq_h)))))))⟩

theorem T_buf : ∃ F, T k Ext x ra t₀ fv i = Blocks [(x.buf, x.L)] ⋆ F := by
  simp only [T, EF, InE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r eq_h))))))))⟩

theorem T_vlc : ∃ F, T k Ext x ra t₀ fv i = VlcW x.vt ⋆ F := by
  simp only [T, EF, InE]
  exact ⟨_, eq_r (eq_r (eq_r (eq_r (eq_l (eq_r (eq_r (eq_r (eq_r (eq_r eq_h)))))))))⟩

end Focus

/-! ## Access through `T` -/

section Access

variable {m : Mem 64} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
  {t₀ : MachineData} {fv : FV} {i : BitVec 32}

/-- `bs_df_env[e]` (raw), `e ≤ 8`. -/
theorem T_ld_df (h : m =⋆ T k Ext x ra t₀ fv i) (e : Nat) (he : e ≤ 8) :
    (m.loadInt (arg3 t₀ + BitVec.ofNat 64 e + Int64.toBitVec 28) 1).isSome = true := by
  obtain ⟨F, hF⟩ := T_df k Ext x ra t₀ fv i
  rw [hF] at h
  refine Block.loadInt_isSome h ?_
  rw [show Int64.toBitVec 28 = 28#64 from rfl,
    show arg3 t₀ + BitVec.ofNat 64 e + 28#64 - (arg3 t₀ + 0x1c#64) = BitVec.ofNat 64 e by
      bv_omega]
  rw [BitVec.toNat_ofNat]; omega

/-- `bs_freq_res[e]`, `e ≤ 8`, at `d + e + c` with `c = 0xc + o`, `o ∈ {0, 1}`. -/
theorem T_ld_fr (h : m =⋆ T k Ext x ra t₀ fv i) (hC : EnvC x t₀) (e o : Nat) (he : e + o ≤ 8)
    (c : Int64) (hc : c.toBitVec = BitVec.ofNat 64 (12 + o)) :
    m.loadInt (arg3 t₀ + BitVec.ofNat 64 e + c.toBitVec) 1
      = some (Int.ofBytes [x.v.freqRes.getD (e + o) 0]) := by
  obtain ⟨F, hF⟩ := T_fr k Ext x ra t₀ fv i
  rw [hF] at h
  have hl : x.v.freqRes.length = 9 := hC.1.1
  have e1 : arg3 t₀ + BitVec.ofNat 64 e + c.toBitVec - (arg3 t₀ + 0xc#64)
      = BitVec.ofNat 64 (e + o) := by
    rw [hc]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have := loadInt_slice h (n := 1) (addr := arg3 t₀ + BitVec.ofNat 64 e + c.toBitVec)
    (by rw [e1, BitVec.toNat_ofNat]; omega) (by omega)
  rw [this, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  congr 2
  rw [List.take_one, List.head?_drop, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-- A load of a whole cell of `T` (given its focus equation). -/
theorem T_ld_at {bs : List UInt8} {a : BitVec 64} {F : Mem 64 → Prop}
    (h : m =⋆ T k Ext x ra t₀ fv i) (hF : T k Ext x ra t₀ fv i = (bs =@ a) ⋆ F) (n : Nat)
    (hl : bs.length = n) (hn : n ≤ 16) : m.loadInt a n = some (Int.ofBytes bs) := by
  rw [hF] at h
  exact loadInt_sep _ _ n _ m h hl (by omega)

theorem T_ld_n0 (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg1 t₀ + 0x4c1e0#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.n0 : Int))) := by
  obtain ⟨F, hF⟩ := T_n0 k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_n1 (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg1 t₀ + 0x4c1e4#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.n1 : Int))) := by
  obtain ⟨F, hF⟩ := T_n1 k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_nenv (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg3 t₀ + 8#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.v.nenv : Int))) := by
  obtain ⟨F, hF⟩ := T_nenv k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_usac (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg1 t₀ + 0x10#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.usac.toInt)) := by
  obtain ⟨F, hF⟩ := T_usac k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_it (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg1 t₀ + 0x14#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.interTes.toInt)) := by
  obtain ⟨F, hF⟩ := T_it k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_cpl (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg1 t₀ + 0x3c#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.coupling.toInt)) := by
  obtain ⟨F, hF⟩ := T_cpl k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_amp (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg3 t₀ + 0x64#64) 4 = some (Int.ofBytes (Int.toBytes 4 x.amp.toInt)) := by
  obtain ⟨F, hF⟩ := T_amp k Ext x ra t₀ fv i
  exact T_ld_at h hF 4 (Int.toBytes_length 4 _) (by omega)

theorem T_ld_avctx (h : m =⋆ T k Ext x ra t₀ fv i) :
    m.loadInt (arg0 t₀ + 8#64) 8 = some (Int.ofBytes (Int.toBytes 8 x.avctx.toInt)) := by
  obtain ⟨F, hF⟩ := T_avctx k Ext x ra t₀ fv i
  exact T_ld_at h hF 8 (Int.toBytes_length 8 _) (by omega)

end Access

/-- A 4-byte cell holding a natural number, read back. -/
theorem c4_val (n : Nat) : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 (n : Int)))
    = BitVec.ofNat 32 n := by
  rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_natCast]

/-- A 4-byte cell holding a bit vector, read back. -/
theorem cell4_val (v : BitVec 32) : BitVec.ofInt 32 (Int.ofBytes (Int.toBytes 4 v.toInt)) = v := by
  rw [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt]

/-- The envelope counter as read from its frame slot. -/
theorem fi_eq {s : MachineData} {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32}
    (hbp : s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (h : s.dmem =⋆ T k Ext x ra t₀ fv i) : fi s = fv.f68.toNat := by
  have := T_ld_f68 h
  rw [fa_68, show t₀.regs.get64 .rsp - 0x70#64 = t₀.regs.get64 .rsp - 8#64 - 0x68#64 by
    bv_omega, ← hbp] at this
  simp only [fi, this, Option.getD_some, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]

/-- `fi_eq` for a state written as a structure (after a block's steps). -/
theorem fi_eq' {k : Nat} {Ext : Mem 64 → Prop} {x : EArgs} {ra : Int64}
    {t₀ : MachineData} {fv : FV} {i : BitVec 32} (regs : Reg64s) (zmms) (status) (dmem : Mem 64)
    (hbp : regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64)
    (h : dmem =⋆ T k Ext x ra t₀ fv i) :
    fi { regs := regs, zmms := zmms, status := status, dmem := dmem } = fv.f68.toNat :=
  fi_eq (s := { regs := regs, zmms := zmms, status := status, dmem := dmem }) hbp h

end Kraken.Examples.Sbr.Env
