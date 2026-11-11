import Kraken.X64.Examples.Sbr.Parse.UsacBlk22
open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse
set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true
/-! # `ff_aac_sbr_decode_usac_data`: the footprint at a `read_sbr_grid` call

`UF` is the grid's footprint `Grid.GF` (at the channel's `DV`) and a rest `GR`; after the
call, the grid's footprint at its return values and the same rest are `UF` at the state with
the new channel and `index`. -/
namespace Kraken.Examples.Sbr.Usac
variable [CodeEnv]

/-- The grid's arguments for the channel `v`, the caller's part `R`. -/
abbrev gx (q : UQ) (st : USt) (v : DV) (R : Mem 64 → Prop) : Grid.GArgs :=
  ⟨R, v, st.u, st.amp, st.x.avctx, q.buf, st.i, q.p8, q.L⟩

/-- `SHW` without `sbr->usac` and `bs_amp_res_header` (the grid reads them). -/
def SHWg (c : BitVec 64) (st : USt) : Mem 64 → Prop :=
  let s := sA c
  cell4 s st.x.sampleRate ⋆ (cell4 (s + 0x4#64) st.x.start ⋆ (cell4 (s + 0x8#64) st.x.ready
    ⋆ (cell4 (s + 0xc#64) st.x.idAac ⋆ (4 ?@ (s + 0x14#64)
    ⋆ (cell4 (s + 0x18#64) st.x.reset ⋆ (st.sp.take 4 =@ (s + 0x1c#64)
    ⋆ (st.sp.drop 4 =@ (s + 0x20#64) ⋆ (2 ?@ (s + 0x22#64) ⋆ (4 ?@ (s + 0x28#64)
    ⋆ (cell4 (s + 0x2c#64) (BitVec.ofNat 32 st.h.lb) ⋆ (c4 (s + 0x30#64) st.x.limGains
    ⋆ (cell4 (s + 0x34#64) st.x.interpol ⋆ (cell4 (s + 0x38#64) st.x.smooth
    ⋆ (cell4 (s + 0x3c#64) st.x.coupling ⋆ (c4 (s + 0x40#64) st.x.k0 ⋆ (16 ?@ (s + 0x44#64)
    ⋆ (c4 (s + 0x54#64) st.x.kx0 ⋆ (c4 (s + 0x58#64) st.x.kx1 ⋆ (c4 (s + 0x5c#64) st.x.m0
    ⋆ (c4 (s + 0x60#64) st.x.m1 ⋆ (cell4 (s + 0x64#64) st.x.pushed
    ⋆ 24 ?@ (s + 0x68#64))))))))))))))))))))))

/-- `DSc` without what the grid owns. -/
def DScg (c : BitVec 64) (ch : Nat) (v : DV) : Mem 64 → Prop :=
  let d := dAc c ch
  4 ?@ (d + 0x4#64) ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (c4 (d + 0x7920#64) v.ypos
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64)))))

/-- The rest of `UF` at a grid call on channel 0. -/
def GR0 (q : UQ) (st : USt) : Mem 64 → Prop :=
  SHWg q.c st ⋆ (TWc q.c st.x ⋆ (DScg q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DSc q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
    ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ q.Oth)))))))

/-- The rest of `UF` at a grid call on channel 1. -/
def GR1 (q : UQ) (st : USt) : Mem 64 → Prop :=
  SHWg q.c st ⋆ (TWc q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DScg q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
    ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ q.Oth)))))))

omit [CodeEnv] in
theorem tb4_ofNat (n : Nat) :
    Int.toBytes 4 (BitVec.ofNat 32 n).toInt = Int.toBytes 4 (n : Int) := by
  rw [show BitVec.ofNat 32 n = BitVec.ofInt (8 * 4) (n : Int) by
    apply BitVec.eq_of_toNat_eq; simp]
  exact tb_ofInt 4 _

omit [CodeEnv] in
theorem tb4_toNat (b : BitVec 32) : Int.toBytes 4 (b.toNat : Int) = Int.toBytes 4 b.toInt := by
  rw [← tb4_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

omit [CodeEnv] in
theorem cell4_ofNat (a : BitVec 64) (n : Nat) : cell4 a (BitVec.ofNat 32 n) = c4 a n := by
  simp only [cell4, c4, tb4_ofNat]

omit [CodeEnv] in
theorem raw8 (d : BitVec 64) :
    (8 ?@ (d + 0x3904#64)) = 4 ?@ (d + 0x3904#64) ⋆ 4 ?@ (d + 0x3908#64) := by
  rw [show d + 0x3908#64 = d + 0x3904#64 + BitVec.ofNat 64 4 by
    rw [BitVec.add_assoc]; rfl]
  exact Block.split _ 4 4 (by decide)

omit [CodeEnv] in
/-- `SHW` is the two cells the grid reads and `SHWg`. -/
theorem shw_g (c : BitVec 64) (st : USt) :
    SHW c st = (cell4 (sA c + 0x10#64) st.u ⋆ cell4 (sA c + 0x24#64) st.amp) ⋆ SHWg c st := by
  unfold SHW SHWg
  dsimp only
  generalize (4 ?@ (sA c + 0x28#64)
    ⋆ (cell4 (sA c + 0x2c#64) (BitVec.ofNat 32 st.h.lb) ⋆ (c4 (sA c + 0x30#64) st.x.limGains
    ⋆ (cell4 (sA c + 0x34#64) st.x.interpol ⋆ (cell4 (sA c + 0x38#64) st.x.smooth
    ⋆ (cell4 (sA c + 0x3c#64) st.x.coupling ⋆ (c4 (sA c + 0x40#64) st.x.k0
    ⋆ (16 ?@ (sA c + 0x44#64) ⋆ (c4 (sA c + 0x54#64) st.x.kx0 ⋆ (c4 (sA c + 0x58#64) st.x.kx1
    ⋆ (c4 (sA c + 0x5c#64) st.x.m0 ⋆ (c4 (sA c + 0x60#64) st.x.m1
    ⋆ (cell4 (sA c + 0x64#64) st.x.pushed ⋆ 24 ?@ (sA c + 0x68#64)))))))))))))) = X
  rw [Std.ExtHashMap.sep_assoc]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2]; rw [Std.ExtHashMap.sep_comm_l]

omit [CodeEnv] in
/-- `DSc` of channel `ch` is the grid's `ChW` and `DScg`. -/
theorem dsc_g (c : BitVec 64) (ch : Nat) (v : DV) (i : BitVec 32) :
    DSc c ch v = Grid.ChW (dAc c ch) ⟨i, BitVec.ofNat 32 v.nenv, v.freqRes,
      BitVec.ofNat 32 v.nnoise, v.te, v.tq⟩ ⋆ DScg c ch v := by
  unfold DSc DScg Grid.ChW
  dsimp only
  rw [raw8 (dAc c ch), cell4_ofNat, cell4_ofNat]
  ac_rfl

theorem rdu_g (q : UQ) : RdU q = (Blocks [(q.buf, q.L), (lab "ceil_log2", 6)] ⋆ (Grid.JtW ⋆ q.Ext))
    ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ q.Oth) := by
  unfold RdU
  ac_rfl

/-- `Grid.GF` with the channel and reader addresses `d`, `g` given (the call sites' form). -/
abbrev GFd (Ext : Mem 64 → Prop) (x : Grid.GArgs) (t : MachineData) (d g : BitVec 64)
    (st : Grid.GSt) : Mem 64 → Prop :=
  Grid.ChW d st ⋆ (Grid.GbW g x st.i ⋆ Grid.InW Ext x t)

/-- `UF` at a grid call on channel 0. -/
theorem uf_grid0 (q : UQ) (st : USt) (R : Mem 64 → Prop) (t : MachineData)
    (d g : BitVec 64) (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c) (hg : g = q.g)
    (hd : d = dAc q.c 0) :
    UF q st = GFd q.Ext (gx q st st.x.d0 R) t d g (gx q st st.x.d0 R).st ⋆ GR0 q st := by
  subst hd hg
  unfold GFd Grid.InW Grid.GArgs.st UF GR0 AcU GbU
  rw [h0, h1, shw_g, dsc_g q.c 0 st.x.d0 st.i, rdu_g]
  dsimp only
  generalize Blocks [(q.buf, q.L), (lab "ceil_log2", 6)] ⋆ (Grid.JtW ⋆ q.Ext) = BJ
  generalize q.uev =@ (q.ue + 0xc#64) ⋆ q.Oth = UO
  simp only [Std.ExtHashMap.sep_assoc]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]

/-- `UF` at a grid call on channel 1. -/
theorem uf_grid1 (q : UQ) (st : USt) (R : Mem 64 → Prop) (t : MachineData)
    (d g : BitVec 64) (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c) (hg : g = q.g)
    (hd : d = dAc q.c 1) :
    UF q st = GFd q.Ext (gx q st st.x.d1 R) t d g (gx q st st.x.d1 R).st ⋆ GR1 q st := by
  subst hd hg
  unfold GFd Grid.InW Grid.GArgs.st UF GR1 AcU GbU
  rw [h0, h1, shw_g, dsc_g q.c 1 st.x.d1 st.i, rdu_g]
  dsimp only
  generalize Blocks [(q.buf, q.L), (lab "ceil_log2", 6)] ⋆ (Grid.JtW ⋆ q.Ext) = BJ
  generalize q.uev =@ (q.ue + 0xc#64) ⋆ q.Oth = UO
  simp only [Std.ExtHashMap.sep_assoc]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv =>
    enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [Std.ExtHashMap.sep_comm_l]

/-- The state after a grid on channel 0 that returned `g`. -/
abbrev gs0 (q : UQ) (st : USt) (R : Mem 64 → Prop) (g : Grid.GSt) : USt :=
  { st with i := g.i, x := { st.x with d0 := g.dv (gx q st st.x.d0 R) } }

/-- The state after a grid on channel 1 that returned `g`. -/
abbrev gs1 (q : UQ) (st : USt) (R : Mem 64 → Prop) (g : Grid.GSt) : USt :=
  { st with i := g.i, x := { st.x with d1 := g.dv (gx q st st.x.d1 R) } }

omit [CodeEnv] in
theorem gst_dv (x : Grid.GArgs) (g : Grid.GSt) (R : Mem 64 → Prop) (st : USt) (q : UQ)
    (hi : st.i = g.i) : (gx q st (g.dv x) R).st = g := by
  obtain ⟨i, n, fr, nn, te, tq⟩ := g
  simp only [Grid.GArgs.st, Grid.GSt.dv, hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The grid's footprint at its return values and the rest: `UF` at the new state. -/
theorem uf_post0 (q : UQ) (st : USt) (R : Mem 64 → Prop) (t : MachineData) (g : Grid.GSt)
    (d gb : BitVec 64) (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c) (hg : gb = q.g)
    (hd : d = dAc q.c 0) :
    GFd q.Ext (gx q st st.x.d0 R) t d gb g ⋆ GR0 q st = UF q (gs0 q st R g) := by
  rw [uf_grid0 q (gs0 q st R g) R t d gb h0 h1 hg hd, gst_dv _ _ _ _ _ rfl]
  rfl

theorem uf_post1 (q : UQ) (st : USt) (R : Mem 64 → Prop) (t : MachineData) (g : Grid.GSt)
    (d gb : BitVec 64) (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c) (hg : gb = q.g)
    (hd : d = dAc q.c 1) :
    GFd q.Ext (gx q st st.x.d1 R) t d gb g ⋆ GR1 q st = UF q (gs1 q st R g) := by
  rw [uf_grid1 q (gs1 q st R g) R t d gb h0 h1 hg hd, gst_dv _ _ _ _ _ rfl]
  rfl

end Kraken.Examples.Sbr.Usac
