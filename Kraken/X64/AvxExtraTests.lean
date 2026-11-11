import Kraken.X64.Parser
import Kraken.X64.PrintIntel
import Kraken.X64.Semantics

/-!
# Tests of `vfmadd132ps`, `vinsertf128` and `vpermps`

Parser output, the Intel-syntax printing `tv` re-assembles (`PrintIntel.lean`), and
the lane arithmetic of `vpermps`/`vinsertf128` in `AvxOperation.interp` on concrete
values. The floating-point results of `vfmadd132ps` are checked against hardware by
`Test/asm/test_avx_fma132.S`; `vinsertf128`/`vpermps` also by
`Test/asm/test_avx_insert_perm.S`.
-/

open Kraken.X64.Parser

/-! ## Parser and printer -/

#guard toString (parse("vfmadd132ps (%rdx,%r8),%ymm2,%ymm0")) ==
  toString [Directive.instr (Instr.avx .W64 .W256
    (.vfmadd132ps (.ymm .mm0) (.ymm .mm2)
      (.mem ⟨some (.reg .rdx), some ⟨.r8, .W8⟩, .int64 0⟩)))]

#guard toString (parse("vfmadd132ps 0x20(%rdx,%r8),%ymm3,%ymm1")) ==
  toString [Directive.instr (Instr.avx .W64 .W256
    (.vfmadd132ps (.ymm .mm1) (.ymm .mm3)
      (.mem ⟨some (.reg .rdx), some ⟨.r8, .W8⟩, .int64 32⟩)))]

#guard (parse("vfmadd132ps (%rdx,%r8),%ymm2,%ymm0")).map toString ==
  ["vfmadd132ps ymm0, ymm2, YMMWORD PTR [rdx+r8*1+0]"]

#guard (parse("vinsertf128 $0x1,(%rdx),%ymm0,%ymm0")).map toString ==
  ["vinsertf128 ymm0, ymm0, XMMWORD PTR [rdx+0], 1"]

#guard (parse("vinsertf128 $0x0,%xmm1,%ymm0,%ymm4")).map toString ==
  ["vinsertf128 ymm4, ymm0, xmm1, 0"]

#guard (parse("vpermps %ymm3,%ymm2,%ymm1")).map toString ==
  ["vpermps ymm1, ymm2, ymm3"]

#guard (parse("vpermps 0x20(%rdx),%ymm2,%ymm1")).map toString ==
  ["vpermps ymm1, ymm2, YMMWORD PTR [rdx+32]"]

/-! ## Lane arithmetic -/

/-- The eight floats 1.0 … 8.0 (lane 0 = 1.0). -/
def oneToEight : BitVec 256 :=
  0x41000000_40e00000_40c00000_40a00000_40800000_40400000_40000000_3f800000#256

/-- `pd_reverse` of `float_dsp.asm`: `dd 7, 6, 5, 4, 3, 2, 1, 0`. -/
def pdReverse : BitVec 256 :=
  0x00000000_00000001_00000002_00000003_00000004_00000005_00000006_00000007#256

/-- The `vpermps` lane function of `AvxOperation.interp`. -/
def vpermpsLanes (idx b : BitVec 256) : BitVec 256 :=
  BitVec.packedBinOp 32 (fun i _ => b.extractLsb' (32 * (i.toNat % 8)) 32) idx idx

/-- With `pd_reverse` as index, `vpermps` reverses the eight floats. -/
example : vpermpsLanes pdReverse oneToEight =
    0x3f800000_40000000_40400000_40800000_40a00000_40c00000_40e00000_41000000#256 := by
  decide +kernel

/-- Index bits above bit 2 are ignored: `0x80000007` picks lane 7, `0xfffffff9` lane 1. -/
example : vpermpsLanes
      0x80000007_00000006_00000005_00000004_00000023_00000002_fffffff9_00000010#256 oneToEight =
    0x41000000_40e00000_40c00000_40a00000_40800000_40400000_40000000_3f800000#256 := by
  decide +kernel

/-- The `vinsertf128` lane function of `AvxOperation.interp`. -/
def vinsertf128Lanes (imm : UInt8) (a : BitVec 256) (b : BitVec 128) : BitVec 256 :=
  if imm.toNat % 2 = 0 then a.extractLsb' 128 128 ++ b else b ++ a.extractLsb' 0 128

/-- `imm = 1` replaces the high lane, `imm = 0` the low lane, `imm = 3` acts as 1. -/
example : vinsertf128Lanes 1 oneToEight 0x41400000_41300000_41200000_41100000#128 =
    0x41400000_41300000_41200000_41100000_40800000_40400000_40000000_3f800000#256 := by
  decide +kernel
example : vinsertf128Lanes 0 oneToEight 0x41400000_41300000_41200000_41100000#128 =
    0x41000000_40e00000_40c00000_40a00000_41400000_41300000_41200000_41100000#256 := by
  decide +kernel
example : vinsertf128Lanes 3 oneToEight 0x41400000_41300000_41200000_41100000#128 =
    vinsertf128Lanes 1 oneToEight 0x41400000_41300000_41200000_41100000#128 := by
  decide +kernel
