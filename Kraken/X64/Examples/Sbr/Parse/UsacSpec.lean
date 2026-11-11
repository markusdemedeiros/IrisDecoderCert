import Kraken.X64.Examples.Sbr.Parse.UsacText
import Kraken.X64.Examples.Sbr.Parse.LibAbort
import Kraken.X64.Examples.Sbr.ApplySpec
import Kraken.X64.Examples.Sbr.Parse.GridSpec
import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.DecExtSpec
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_decode_usac_data`, `ff_aac_sbr_config_usac`: the specification

`ff_aac_sbr_decode_usac_data(ac, che, ue, gb, sbr_ch, indep_flag)`
(`libavcodec/aacsbr_template.c` l.1209-1354, FFmpeg n8.1) parses the SBR payload of one USAC
element; `ff_aac_sbr_config_usac(ac, che, ue)` (l.1201-1207) is `sbr_turnoff`.

* The decoder state is the model's `St = Args × Hid` (`ParseModel.lean`), with the machine
  values the model does not hold: the bit reader's `index`, `sbr->usac`,
  `sbr->bs_amp_res_header`, the six bytes of `spectrum_params` (`Hid` reads two of them).
  These are a `USt`.
* The footprint `UF` is the whole of `*sbr` except the PS context and the apply-only work arrays
  (the scalar head, both `SBRData`, the frequency tables), the fields of `*ac` read, the twelve
  bytes of `ue->sbr` read, `*gb`, the bitstream, `ceil_log2` and `read_sbr_grid`'s jump table,
  `av_log`'s state `Ext` and `Oth`, the state of the other callees (their tables). The fields of
  `Args` are cells with their values (as in `ApplySpec.lean`), the rest raw bytes.
* The postcondition is the row `usac_spec` of the model (`MI → MI ∧ (success → LiveC)`) on the
  final state the footprint holds, on every return path; `Args` fields outside the footprint
  are kept (`UKeep`). A run may also reach `abort` (from `read_sbr_grid`'s `av_assert0`): the
  specification is a `ProcSpecA`.
* The callees are assumed by contracts (`UsacCallees`), each the weakest the model's row
  gives: `read_sbr_grid` by its own specification (`GridPre`/`GridPost`), the others as a
  model relation on the footprint (`read_sbr_header`: `Header`; `sbr_reset`: `ResetS`;
  `sbr_make_f_tablelim`: `Tablelim`; `read_sbr_invf`: `invfRead`; `read_sbr_dtdf`,
  `read_sbr_envelope`, `read_sbr_noise`: no `Args` field written).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

/-- `sbr`. -/
abbrev sA (c : BitVec 64) : BitVec 64 := c + 0x28920#64

/-- `&sbr->data[ch]`. -/
abbrev dAc (c : BitVec 64) (ch : Nat) : BitVec 64 := sA c + BitVec.ofNat 64 (0x80 + 0x15ac0 * ch)

variable [CodeEnv]

/-- `*sbr` up to `data`: the scalar fields (cells for the `Args` fields, `sbr->usac`,
`bs_amp_res_header`, `spectrum_params`, `bs_limiter_bands`; raw: `inter_tes`,
`bs_sbr_preprocessing`, `k[1..4]`, `n_master` and the padding). -/
def SHW (c : BitVec 64) (st : USt) : Mem 64 → Prop :=
  let s := sA c
  cell4 s st.x.sampleRate ⋆ (cell4 (s + 0x4#64) st.x.start ⋆ (cell4 (s + 0x8#64) st.x.ready
    ⋆ (cell4 (s + 0xc#64) st.x.idAac ⋆ (cell4 (s + 0x10#64) st.u ⋆ (4 ?@ (s + 0x14#64)
    ⋆ (cell4 (s + 0x18#64) st.x.reset ⋆ (st.sp.take 4 =@ (s + 0x1c#64)
    ⋆ (st.sp.drop 4 =@ (s + 0x20#64) ⋆ (2 ?@ (s + 0x22#64)
    ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (4 ?@ (s + 0x28#64)
    ⋆ (cell4 (s + 0x2c#64) (BitVec.ofNat 32 st.h.lb) ⋆ (c4 (s + 0x30#64) st.x.limGains
    ⋆ (cell4 (s + 0x34#64) st.x.interpol ⋆ (cell4 (s + 0x38#64) st.x.smooth
    ⋆ (cell4 (s + 0x3c#64) st.x.coupling ⋆ (c4 (s + 0x40#64) st.x.k0 ⋆ (16 ?@ (s + 0x44#64)
    ⋆ (c4 (s + 0x54#64) st.x.kx0 ⋆ (c4 (s + 0x58#64) st.x.kx1 ⋆ (c4 (s + 0x5c#64) st.x.m0
    ⋆ (c4 (s + 0x60#64) st.x.m1 ⋆ (cell4 (s + 0x64#64) st.x.pushed
    ⋆ 24 ?@ (s + 0x68#64))))))))))))))))))))))))

/-- The frequency tables (`ApplySpec`'s `TabW`) with `f_master` and the padding raw. -/
def TWc (c : BitVec 64) (x : Args) : Mem 64 → Prop :=
  let s := sA c
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
    ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (x.ftLow =@ (s + 0x4c252#64)
    ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
    ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (2 ?@ (s + 0x4c32e#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
    ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64))))))))))))

/-- The scalar fields of `sbr->data[ch]` (`ApplySpec`'s `DScW`), `bs_frame_class` and
`e_a[0..1]` raw. -/
def DSc (c : BitVec 64) (ch : Nat) (v : DV) : Mem 64 → Prop :=
  let d := dAc c ch
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (4 ?@ (d + 0x3904#64)
    ⋆ (4 ?@ (d + 0x3908#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
    ⋆ Int.toBytes 8 v.idx.toInt =@ (d + 0x15aac#64))))))))))))))

/-- The other bytes of `sbr->data[ch]` (the arrays of `ApplySpec`'s `DArrW` and the gaps:
`bs_df_env`, `bs_df_noise`, `temp_shape`, padding). -/
def DRaw (c : BitVec 64) (ch : Nat) : Mem 64 → Prop :=
  let d := dAc c ch
  Blocks [(d + 0x15#64, 3), (d + 0x1c#64, 11), (d + 0x61#64, 3), (d + 0x68#64, 24),
    (d + 0x80#64, 9216), (d + 0x2480#64, 5248), (d + 0x390c#64, 20),
    (d + 0x3920#64, 16384), (d + 0x7924#64, 12), (d + 0x7930#64, 38936),
    (d + 0x11148#64, 8040), (d + 0x130b0#64, 8064), (d + 0x15030#64, 432),
    (d + 0x151e0#64, 432), (d + 0x15390#64, 1728), (d + 0x15a50#64, 16),
    (d + 0x15a60#64, 60), (d + 0x15aa9#64, 3), (d + 0x15ab4#64, 12)]

/-- `*ac`: `avctx`, `oc[1].m4ac.ext_sample_rate`. -/
def AcU (a : BitVec 64) (x : Args) : Mem 64 → Prop :=
  Int.toBytes 8 x.avctx.toInt =@ (a + 0x8#64) ⋆ cell4 (a + 0x57f4#64) x.extRate

/-- What is only read, and the callees' state: the bitstream, `ceil_log2`, the jump table,
`ue->sbr`, `Ext`, `Oth`. -/
def RdU (q : UQ) : Mem 64 → Prop :=
  Blocks [(q.buf, q.L), (lab "ceil_log2", 6)] ⋆ (Grid.JtW ⋆ (q.uev =@ (q.ue + 0xc#64)
    ⋆ (q.Ext ⋆ q.Oth)))

/-- The footprint at the values `st`. -/
def UF (q : UQ) (st : USt) : Mem 64 → Prop :=
  SHW q.c st ⋆ (TWc q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DSc q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (AcU q.a st.x ⋆ (GbU q st.i ⋆ RdU q)))))))

/-- The bit reader's precondition (as `read_sbr_grid`'s): `index ≤ size_in_bits_plus8 < 2^31`,
every read loads at most 4 bytes at `buffer + index / 8` inside the buffer. -/
def GbC (q : UQ) : Prop :=
  q.p8.toNat < 2 ^ 31 ∧ q.p8.toNat / 8 + 4 ≤ q.L ∧ q.L < 2 ^ 32

/-- `ue->sbr`: twelve bytes; the default header's `start_freq` (4 bits), `limiter_bands`,
`limiter_gains` (2 bits each), as the configuration parser reads them, and its `freq_scale`
(2 bits). -/
def UeC (q : UQ) : Prop :=
  q.uev.length = 12 ∧ u8 q.uev 1 < 16 ∧ u8 q.uev 6 < 4 ∧ u8 q.uev 7 < 4 ∧ u8 q.uev 3 ≤ 3

/-- The layout of `*sbr`: no address wrap (for `sbr_reset`, `sbr_make_f_tablelim`), 32-aligned
(for `read_sbr_envelope`). -/
def LayU (q : UQ) : Prop := (sA q.c).toNat + 0x60000 < 2 ^ 64 ∧ (sA q.c).toNat % 32 = 0

/-- The side conditions at entry. -/
def UsacC (q : UQ) (st : USt) : Prop :=
  MI (st.x, st.h) ∧ SpOk st ∧ st.i.toNat ≤ q.p8.toNat ∧ GbC q ∧ UeC q ∧ Grid.JtC ∧ LayU q

/-- The stack at entry: the ABI alignment. -/
def StkC (t : MachineData) : Prop :=
  isAligned 16 (t.regs.get64 .rsp + 8#64) = true

/-- The logical variables: the fixed values and the state at entry. -/
abbrev UA := UQ × USt

/-- The callees' states are `Ext` (`av_log`'s) and `Oth`. -/
abbrev QE (Ext Oth : Mem 64 → Prop) (q : UQ) : Prop := q.Ext = Ext ∧ q.Oth = Oth

abbrev UsacPre (k : Nat) (A : UA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (usacNeed k) (UF A.1 A.2 ⋆ A.1.R) ra t ∧ UsacC A.1 A.2
  ∧ arg0 t = A.1.a ∧ arg1 t = A.1.c ∧ arg2 t = A.1.ue ∧ arg3 t = A.1.g ∧ StkC t

/-- What a return leaves: the model's row `usac_spec` on the final state (`MI`; `LiveC` on
`0`), the fields outside the footprint kept, `SpOk` (with `bs_limiter_bands ≤ 3` and the table
lengths), the reader's bound. -/
def UsacOut (A : UA) (st : USt) (ret : BitVec 32) : Prop :=
  MI (st.x, st.h) ∧ (ret = 0#32 → LiveC st.x) ∧ UKeep A.2.x st.x ∧ SpOk st
  ∧ st.i.toNat ≤ A.1.p8.toNat

abbrev UsacPost (k : Nat) (A : UA) (ra : Int64) (t s : MachineData) : Prop :=
  ∃ st, UsacOut A st ((s.regs.get64 .rax).setWidth 32)
    ∧ CallPost (usacNeed k) (UF A.1 st ⋆ A.1.R) ra t s

/-! ## The callees' contracts

Each callee owns `UF` (at the caller's values) and the caller's rest; the logical variable of
a contract is the pair `(q, st)` with `q.R` the rest. The callees' states `q.Ext`, `q.Oth` are
fixed (`Ext`, `Oth`, parameters of the contracts). -/

/-- The convention's part of a callee contract, `UF` at `st`, the callees' states. -/
abbrev CPre (k : Nat) (Ext Oth : Mem 64 → Prop) (A : UA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre (cneed k) (UF A.1 A.2 ⋆ A.1.R) ra t ∧ QE Ext Oth A.1

/-- The return of a callee: some state `st'` related to the entry state by `Rel`. -/
abbrev CPost (k : Nat) (Rel : USt → USt → Prop) (A : UA) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ st', Rel A.2 st' ∧ CallPost (cneed k) (UF A.1 st' ⋆ A.1.R) ra t s

/-- A callee that writes no `Args` field: the reader's `index` stays in bounds. -/
def RdOnly (q : UQ) (st st' : USt) : Prop :=
  st' = { st with i := st'.i } ∧ st'.i.toNat ≤ q.p8.toNat

/-- `read_sbr_dtdf(sbr->usac, gb, &sbr->data[ch], indep_flag)` (the first argument is the
value of `sbr->usac` in this object). -/
abbrev DtdfSpec (k : Nat) (ch : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "read_sbr_dtdf")
    (fun (A : UA) ra t => CPre k Ext Oth A ra t ∧ (arg0 t).setWidth 32 = A.2.u ∧ arg1 t = A.1.g
      ∧ arg2 t = dAc A.1.c ch ∧ DWF False (A.2.x.d ch) ∧ A.2.i.toNat ≤ A.1.p8.toNat ∧ GbC A.1)
    (fun A => CPost k (RdOnly A.1) A)

/-- `read_sbr_invf(sbr, gb, &sbr->data[ch])`: `invfRead` of the channel. -/
abbrev InvfSpec (k : Nat) (ch : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "read_sbr_invf")
    (fun (A : UA) ra t => CPre k Ext Oth A ra t ∧ arg0 t = sA A.1.c ∧ arg1 t = A.1.g
      ∧ arg2 t = dAc A.1.c ch ∧ Scal A.2.x ∧ DWF False (A.2.x.d ch)
      ∧ A.2.i.toNat ≤ A.1.p8.toNat ∧ GbC A.1)
    (fun A => CPost k (fun st st' => ∃ vals : Nat → Nat,
      st' = { st with x := if ch = 0 then { st.x with d0 := invfRead st.x.nq st.x.d0 vals }
                           else { st.x with d1 := invfRead st.x.nq st.x.d1 vals }, i := st'.i }
      ∧ st'.i.toNat ≤ A.1.p8.toNat) A)

/-- The stops of the routine: `abort`'s entry (`read_sbr_grid`'s `av_assert0`) and the bounds
trap `read_sbr_envelope.L60f9` (`temp_shape[i]` for `i ≥ 6`, reached with `usac`, `inter_tes`
set and more than six envelopes; `usac` is set here, `inter_tes` comes from `ue->sbr`). -/
abbrev usacStops (a : Int64) : Prop := a = abortA ∨ a = entry "read_sbr_envelope.L60f9"

/-- `read_sbr_envelope(ac, sbr, gb, &sbr->data[ch], ch)` / `read_sbr_noise(…)` (`sbr`
32-aligned): no `Args` field written (abstraction 6 of the model), any result; a run may stop
at the envelope's bounds trap. Called after a successful grid of the channel, in a USAC frame. -/
abbrev EnvNoiseSpec (l : Label) (k : Nat) (ch : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecS usacStops (entry l)
    (fun (A : UA) ra t => CPre k Ext Oth A ra t ∧ arg0 t = A.1.a ∧ arg1 t = sA A.1.c
      ∧ arg2 t = A.1.g ∧ arg3 t = dAc A.1.c ch ∧ (arg4 t).setWidth 32 = BitVec.ofNat 32 ch
      ∧ MI (A.2.x, A.2.h) ∧ Live (A.2.x.d ch)
      ∧ A.2.i.toNat ≤ A.1.p8.toNat ∧ GbC A.1 ∧ (sA A.1.c).toNat % 32 = 0)
    (fun A => CPost k (RdOnly A.1) A)

/-- `read_sbr_header(sbr, gb, 1)` (with no address wrap of `*sbr`, for `sbr_make_f_tablelim`):
a `Header true` step, `sbr->usac = is_usac = 1`; `bs_amp_res_header` and the other bytes of
`spectrum_params` any value but the field widths of `bs_freq_scale`, `bs_alter_scale`
(`SpOk`: of `bs_limiter_bands`). -/
abbrev HeaderSpec (k : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "read_sbr_header")
    (fun (A : UA) ra t => CPre k Ext Oth A ra t ∧ arg0 t = sA A.1.c ∧ arg1 t = A.1.g
      ∧ (arg2 t).setWidth 32 = 1#32 ∧ MI (A.2.x, A.2.h) ∧ A.2.x.reset = 0 ∧ SpOk A.2
      ∧ A.2.i.toNat ≤ A.1.p8.toNat ∧ GbC A.1 ∧ (sA A.1.c).toNat + 0x60000 < 2 ^ 64)
    (fun A => CPost k (fun st st' => Header true (st.x, st.h) (st'.x, st'.h) ∧ st'.u = 1#32
      ∧ SpOk st' ∧ st'.i.toNat ≤ A.1.p8.toNat ∧ u8 st'.sp 3 < 4 ∧ u8 st'.sp 4 < 2) A)

/-- `sbr_make_f_tablelim(sbr)` with `bs_limiter_bands = h.lb` (a 2-bit value; the table lengths,
no address wrap of `*sbr`): a `Tablelim` step, the table lengths kept. -/
abbrev TablelimSpec (k : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "sbr_make_f_tablelim")
    (fun (A : UA) ra t => CPre k Ext Oth A ra t ∧ arg0 t = sA A.1.c ∧ Scal A.2.x ∧ TabWF A.2.x
      ∧ 1 ≤ A.2.x.n0 ∧ 1 ≤ A.2.x.npatch ∧ A.2.h.lb ≤ 3 ∧ DecExt.Lens A.2.x
      ∧ (sA A.1.c).toNat + 0x60000 < 2 ^ 64)
    (fun A => CPost k (fun st st' => ∃ y, Tablelim st.h.lb st.x y ∧ st' = { st with x := y }
      ∧ DecExt.Lens y) A)

/-- `sbr_reset(ac, sbr)` with a reset pending: `reset_spec`'s conclusion (`Scal`; the fields of
`TFrame` and of `UKeep` kept; either `sbr_turnoff`, with the bytes of `spectrum_params` all
`0xFF` and `usac = 0`, or the tables of `TabWF` with `Inv2`, `usac` kept); `bs_limiter_bands`
kept. From the field widths
of `bs_freq_scale`, `bs_alter_scale` (and `SpOk`), no address wrap of `*sbr`, the ABI stack
alignment. -/
abbrev ResetSpec (k : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "sbr_reset")
    (fun (A : UA) ra t => CPre k Ext Oth A ra t ∧ arg0 t = A.1.a ∧ arg1 t = sA A.1.c
      ∧ A.2.x.reset ≠ 0 ∧ A.2.h.start < 16 ∧ Scal A.2.x ∧ SpOk A.2
      ∧ u8 A.2.sp 3 ≤ 3 ∧ u8 A.2.sp 4 ≤ 1 ∧ (sA A.1.c).toNat + 0x60000 < 2 ^ 64
      ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true)
    (fun A => CPost k (fun st st' => Scal st'.x ∧ ∃ y, TFrame st.x y ∧ UKeep st.x y
      ∧ ((st'.x = y.turnoff ∧ st'.h = st.h.turnoff ∧ st'.u = 0#32)
        ∨ (st'.x = y ∧ st'.h = st.h ∧ st'.u = st.u ∧ TabWF y ∧ 1 ≤ y.n0 ∧ 1 ≤ y.npatch))
      ∧ st' = { st with x := st'.x, h := st'.h, sp := st'.sp, u := st'.u } ∧ SpOk st') A)

/-- `read_sbr_grid(ac, sbr, gb, ch_data)`: its own specification (`GridSpec.lean`). -/
abbrev GridSpecA (k : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "read_sbr_grid") (Grid.GridPre k Ext) (Grid.GridPost k Ext)

/-- The callees at `k` bytes of stack, with the callees' states `Ext` (`av_log`'s) and `Oth`. -/
abbrev UsacCallees (k : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  GridSpecA k Ext ∧ HeaderSpec k Ext Oth ∧ TablelimSpec k Ext Oth ∧ ResetSpec k Ext Oth
  ∧ DtdfSpec k 0 Ext Oth ∧ DtdfSpec k 1 Ext Oth ∧ InvfSpec k 0 Ext Oth ∧ InvfSpec k 1 Ext Oth
  ∧ EnvNoiseSpec "read_sbr_envelope" k 0 Ext Oth ∧ EnvNoiseSpec "read_sbr_envelope" k 1 Ext Oth
  ∧ EnvNoiseSpec "read_sbr_noise" k 0 Ext Oth ∧ EnvNoiseSpec "read_sbr_noise" k 1 Ext Oth

/-- **`ff_aac_sbr_decode_usac_data`** with its callees at `k` bytes of stack. -/
abbrev UsacSpec (k : Nat) (Ext Oth : Mem 64 → Prop) : Prop :=
  ProcSpecS usacStops (entry "ff_aac_sbr_decode_usac_data")
    (fun A ra t => UsacPre k A ra t ∧ QE Ext Oth A.1) (UsacPost k)

/-! ## `ff_aac_sbr_config_usac` -/

abbrev ConfigPre (A : UA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre 0 (UF A.1 A.2 ⋆ A.1.R) ra t ∧ MI (A.2.x, A.2.h) ∧ SpOk A.2 ∧ arg1 t = A.1.c

/-- `sbr_turnoff`: the model's `Config` step (`stOff`), and `MI` again. -/
abbrev ConfigPost (A : UA) (ra : Int64) (t s : MachineData) : Prop :=
  ∃ st, (st.x, st.h) = stOff (A.2.x, A.2.h) ∧ MI (st.x, st.h) ∧ SpOk st ∧ UKeep A.2.x st.x
    ∧ (s.regs.get64 .rax).setWidth 32 = 0#32
    ∧ CallPost 0 (UF A.1 st ⋆ A.1.R) ra t s

abbrev ConfigSpec : Prop :=
  cenv.ProcSpec (entry "ff_aac_sbr_config_usac") ConfigPre ConfigPost

end Kraken.Examples.Sbr.Usac
