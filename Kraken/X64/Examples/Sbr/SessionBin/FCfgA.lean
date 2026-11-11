import Kraken.X64.Examples.Sbr.Parse.UsacSpec
import Kraken.X64.Examples.Sbr.SessionBin.FApplyD
import Kraken.X64.Examples.Sbr.SessionBin.FApplyS

/-!
# Footprint conversion for `ff_aac_sbr_config_usac`: the groups

* `DecExt.SbrS` is `Usac.SHW` with `inter_tes` typed (raw in `SHW`) and `spectrum_params` as
  one 6-byte cell (two in `SHW`); both are `SHWr` with the `inter_tes` cell.
* `DecExt.DataF` is `Usac.DSc ⋆ Usac.DRaw`; `DecExt.TabF` is `Usac.TWc`.
* `ArrW`'s first array holds the bytes `UF` names for the reader `*gb` and `ue->sbr`
  (`Carve`), which `ff_aac_sbr_config_usac` does not read.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Usac

namespace Kraken.Examples.Sbr.SessionBin

/-- A 32-bit cell of `n` truncated is the `int` cell of `n`. -/
theorem fc_c4 (a : BitVec 64) (n : Nat) : cell4 a (BitVec.ofNat 32 n) = c4 a n := by
  show (Int.toBytes 4 (BitVec.ofNat 32 n).toInt =@ a) = (Int.toBytes 4 (n : Int) =@ a)
  rw [← Int.toBytes_emod 4 (BitVec.ofNat 32 n).toInt, ← Int.toBytes_emod 4 (n : Int)]
  congr 2
  simp only [Int.take, Nat.reduceMul]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat]
  split <;> omega

/-- `SHW` without the raw `inter_tes` cell, from the values. -/
def SHWr (c : BitVec 64) (x : Args) (u amp : BitVec 32) (lb : Nat) (sp : List UInt8) :
    Mem 64 → Prop :=
  let s := sA c
  cell4 s x.sampleRate ⋆ (cell4 (s + 0x4#64) x.start ⋆ (cell4 (s + 0x8#64) x.ready
    ⋆ (cell4 (s + 0xc#64) x.idAac ⋆ (cell4 (s + 0x10#64) u
    ⋆ (cell4 (s + 0x18#64) x.reset ⋆ (sp.take 4 =@ (s + 0x1c#64)
    ⋆ (sp.drop 4 =@ (s + 0x20#64) ⋆ (2 ?@ (s + 0x22#64)
    ⋆ (cell4 (s + 0x24#64) amp ⋆ (4 ?@ (s + 0x28#64)
    ⋆ (c4 (s + 0x2c#64) lb ⋆ (c4 (s + 0x30#64) x.limGains
    ⋆ (cell4 (s + 0x34#64) x.interpol ⋆ (cell4 (s + 0x38#64) x.smooth
    ⋆ (cell4 (s + 0x3c#64) x.coupling ⋆ (c4 (s + 0x40#64) x.k0 ⋆ (16 ?@ (s + 0x44#64)
    ⋆ (c4 (s + 0x54#64) x.kx0 ⋆ (c4 (s + 0x58#64) x.kx1 ⋆ (c4 (s + 0x5c#64) x.m0
    ⋆ (c4 (s + 0x60#64) x.m1 ⋆ (cell4 (s + 0x64#64) x.pushed
    ⋆ 24 ?@ (s + 0x68#64)))))))))))))))))))))))

theorem fc_shw (c : BitVec 64) (st : USt) :
    SHW c st = 4 ?@ (sA c + 0x14#64) ⋆ SHWr c st.x st.u st.amp st.h.lb st.sp := by
  simp only [SHW, SHWr, fc_c4]; generalize sA c = s; ac_rfl

theorem fc_sp (sp : List UInt8) (a : BitVec 64) (hl : sp.length = 6) :
    sp =@ (a + 0x1c#64) = sp.take 4 =@ (a + 0x1c#64) ⋆ sp.drop 4 =@ (a + 0x20#64) := by
  conv => lhs; rw [← List.take_append_drop 4 sp]
  exact Val.append_eq _ _ _ _ (by rw [List.length_take, hl, BitVec.add_assoc]; rfl)
    (by simp only [List.length_take, List.length_drop, hl]; omega)

theorem fc_sbrS (d : DecExt.DS) (c : BitVec 64) (hl : d.sp.length = 6) :
    DecExt.SbrS d (sA c) = cell4 (sA c + 0x14#64) d.it ⋆ SHWr c d.a d.usac d.amp d.h.lb d.sp := by
  rw [DecExt.SbrS, fc_sp _ _ hl]
  simp only [SHWr]
  generalize sA c = s
  ac_rfl

/-- `DSc` at an address `d`. -/
abbrev DScD (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (4 ?@ (d + 0x3904#64)
    ⋆ (4 ?@ (d + 0x3908#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64))))))))))))))

/-- `DRaw` at an address `d`. -/
abbrev DRawD (d : BitVec 64) : Mem 64 → Prop :=
  3 ?@ (d + 0x15#64) ⋆ (11 ?@ (d + 0x1c#64) ⋆ (3 ?@ (d + 0x61#64) ⋆ (24 ?@ (d + 0x68#64)
    ⋆ (9216 ?@ (d + 0x80#64) ⋆ (5248 ?@ (d + 0x2480#64) ⋆ (20 ?@ (d + 0x390c#64)
    ⋆ (16384 ?@ (d + 0x3920#64) ⋆ (12 ?@ (d + 0x7924#64) ⋆ (38936 ?@ (d + 0x7930#64)
    ⋆ (8040 ?@ (d + 0x11148#64) ⋆ (8064 ?@ (d + 0x130b0#64) ⋆ (432 ?@ (d + 0x15030#64)
    ⋆ (432 ?@ (d + 0x151e0#64) ⋆ (1728 ?@ (d + 0x15390#64) ⋆ (16 ?@ (d + 0x15a50#64)
    ⋆ (60 ?@ (d + 0x15a60#64) ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ 12 ?@ (d + 0x15ab4#64))))))))))))))))))

theorem fc_dataD (v : DV) (d : BitVec 64) : DecExt.DataF v d = DScD v d ⋆ DRawD d := by
  simp only [DecExt.DataF, fa_blk3898, fa_blke178, fa_blk4014, DScD, DRawD, Apply.c8]
  rw [show (16 ?@ (d + 0x15a50#64)) = 15 ?@ (d + 0x15a50#64) ⋆ 1 ?@ (d + 0x15a5f#64) from
    fa_cut _ _ 15 1 (by rw [BitVec.add_assoc]; rfl) (by omega)]
  ac_rfl

theorem fc_dataF (v : DV) (c : BitVec 64) (ch : Nat) :
    DecExt.DataF v (dAc c ch) = DSc c ch v ⋆ DRaw c ch := fc_dataD v (dAc c ch)

theorem fc_tabF (x : Args) (c : BitVec 64) : DecExt.TabF x (sA c) = TWc c x := rfl

/-- An empty block owns nothing. -/
theorem fc_blk0 (a : BitVec 64) : (0 ?@ a) = Std.ExtHashMap.emp := by
  funext m
  apply propext
  constructor
  · rintro ⟨-, bs, hlen, rfl⟩
    rw [List.length_eq_zero_iff.mp hlen]
    show List.At [] a = ∅
    simp [List.At]
  · intro h
    refine ⟨by omega, [], rfl, ?_⟩
    have h' : m = ∅ := h
    rw [h']
    simp [List.At]

/-- The bytes of `X_low` (`ArrW`'s first array) that `UF` names: the reader `*gb` (20 bytes) and
`ue->sbr` (12 bytes). -/
def Carve (s : BitVec 64) : Mem 64 → Prop :=
  8 ?@ (s + 0x4c340#64) ⋆ (4 ?@ (s + 0x4c340#64 + 8#64) ⋆ (4 ?@ (s + 0x4c340#64 + 0xc#64)
    ⋆ (4 ?@ (s + 0x4c340#64 + 0x10#64) ⋆ 12 ?@ (s + 0x4c348#64 + 0xc#64))))

/-- `ArrW` without `Carve`. -/
def ArrRest (t : MachineData) : Mem 64 → Prop :=
  let s := sbrA t
  Blocks [(s + 0x4c360#64, 10208), (s + 0x4eb40#64, 20480),
    (s + 0x53b40#64, 0x4c00), (s + 0x58740#64, 0x4c00), (s + 0x5d340#64, 512),
    (s + 0x5d540#64, 512), (s + 0x5d740#64, 1536), (s + 0x5dd40#64, 1536),
    (s + 0x5e340#64, 384), (s + 0x5e4c0#64, 1536), (s + 0x5eac0#64, 1536),
    (s + 0x5f0c0#64, 1536), (s + 0x5f6c0#64, 1536), (s + 0x5fcc0#64, 1280)]

theorem fc_x10240 (s : BitVec 64) :
    10240 ?@ (s + 0x4c340#64) = Carve s ⋆ 10208 ?@ (s + 0x4c360#64) := by
  rw [show (10240 : Nat) = 8 + (4 + (4 + (4 + (12 + 10208)))) from rfl,
    fa_cut _ (s + 0x4c340#64 + 8#64) 8 _ rfl (by omega),
    fa_cut _ (s + 0x4c340#64 + 0xc#64) 4 _ (by bv_omega) (by omega),
    fa_cut _ (s + 0x4c340#64 + 0x10#64) 4 _ (by bv_omega) (by omega),
    fa_cut _ (s + 0x4c348#64 + 0xc#64) 4 _ (by bv_omega) (by omega),
    fa_cut _ (s + 0x4c360#64) 12 _ (by bv_omega) (by omega)]
  simp only [Carve, Std.ExtHashMap.sep_assoc]

theorem fc_arrW (t : MachineData) : ArrW t = Carve (sbrA t) ⋆ ArrRest t := by
  simp only [ArrW, ArrRest, Blocks]
  generalize sbrA t = s
  rw [fc_x10240, Std.ExtHashMap.sep_assoc]

/-- `Carve` with values: the reader's `buffer`, `index`, `size_in_bits_plus8`, `ue->sbr`. -/
def GbX (s b : BitVec 64) (i p : BitVec 32) (uev : List UInt8) : Mem 64 → Prop :=
  Int.toBytes 8 b.toInt =@ (s + 0x4c340#64) ⋆ (cell4 (s + 0x4c340#64 + 8#64) i
    ⋆ (4 ?@ (s + 0x4c340#64 + 0xc#64) ⋆ (cell4 (s + 0x4c340#64 + 0x10#64) p
    ⋆ uev =@ (s + 0x4c348#64 + 0xc#64))))

variable [CodeEnv] in
theorem fc_blk8_ex (a : BitVec 64) :
    (8 ?@ a) = fun m => ∃ v : BitVec 64, (Int.toBytes 8 v.toInt =@ a) m :=
  block_eq_exists a 8 (by decide)

variable [CodeEnv] in
theorem fc_blk4_ex (a : BitVec 64) : (4 ?@ a) = fun m => ∃ v : BitVec 32, cell4 a v m :=
  block_eq_exists a 4 (by decide)

variable [CodeEnv] in
theorem fc_blk12_ex (a : BitVec 64) :
    (12 ?@ a) = fun m => ∃ v : BitVec 96, (Int.toBytes 12 v.toInt =@ a) m :=
  block_eq_exists a 12 (by decide)

variable [CodeEnv] in
theorem fc_carve_eq (s : BitVec 64) :
    Carve s = fun m => ∃ (v : BitVec 96) (p i : BitVec 32) (b : BitVec 64),
      GbX s b i p (Int.toBytes 12 v.toInt) m := by
  unfold Carve GbX
  rw [fc_blk8_ex (s + 0x4c340#64), fc_blk4_ex (s + 0x4c340#64 + 8#64),
    fc_blk4_ex (s + 0x4c340#64 + 0x10#64), fc_blk12_ex (s + 0x4c348#64 + 0xc#64)]
  simp only [sep_ex_l, sep_ex_r]

variable [CodeEnv] in
theorem fc_carve_ex {s : BitVec 64} {A B R : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ (Carve s ⋆ R))) m) :
    ∃ (b : BitVec 64) (i p : BitVec 32) (v : BitVec 96),
      (A ⋆ (B ⋆ (GbX s b i p (Int.toBytes 12 v.toInt) ⋆ R))) m := by
  rw [fc_carve_eq] at h
  simp only [sep_ex_l, sep_ex_r] at h
  obtain ⟨v, p, i, b, h⟩ := h
  exact ⟨b, i, p, v, h⟩

variable [CodeEnv] in
theorem fc_carve_back {s b : BitVec 64} {i p : BitVec 32} {uev : List UInt8}
    {A B R : Mem 64 → Prop} {m : Mem 64} (hl : uev.length = 12)
    (h : (A ⋆ (B ⋆ (GbX s b i p uev ⋆ R))) m) : (A ⋆ (B ⋆ (Carve s ⋆ R))) m := by
  obtain ⟨v, hv⟩ : ∃ v : BitVec 96, Int.toBytes 12 v.toInt = uev :=
    ⟨BitVec.ofInt 96 (Int.ofBytes uev), toBytes_ofInt_ofBytes 12 uev hl⟩
  subst hv
  rw [fc_carve_eq]
  simp only [sep_ex_l, sep_ex_r]
  exact ⟨v, p, i, b, h⟩

end Kraken.Examples.Sbr.SessionBin
