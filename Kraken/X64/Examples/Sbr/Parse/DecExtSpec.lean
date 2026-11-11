import Kraken.X64.Examples.Sbr.Parse.DecExtText
import Kraken.X64.Examples.Sbr.Parse.LibAbort
import Kraken.X64.Examples.Sbr.Parse.GridSpec
import Kraken.X64.Examples.Sbr.ParseModel
import Kraken.X64.Examples.Sbr.Parse.LibGb
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# `ff_aac_sbr_decode_extension`: the specification

`ff_aac_sbr_decode_extension(ac, che, gb_host, crc, cnt, id_aac)` (`libavcodec/aacsbr_template.c`,
FFmpeg n8.1) parses one SBR extension payload of `cnt` bytes from the bit reader `*gb_host` into
the decoder state `sbr = &che->sbr` (at `che + 0x28920`). It copies the reader to its frame,
advances `*gb_host` by `cnt * 8 - 4` bits (clamped), reads an optional header
(`read_sbr_header`), runs `sbr_reset` if one was requested, and, if the decoder is started, reads
the channel element and its extensions (`read_sbr_data`, inlined). It returns `cnt`.

* The decoder-state values are `DS`: the model's `Args` and `Hid` (`ParseModel.lean`) and the
  raw scalars of `*sbr` the code and its callees read (`usac`, `bs_amp_res_header`, the six bytes
  of `spectrum_params`, which hold `Hid.start` and `Hid.xover`; `Hid.lb` is the cell
  `bs_limiter_bands`, see `DS.ok`).
* The footprint `DecF` owns the decoder state the parser reads or writes (`SbrF`: the scalars,
  both `SBRData`, `ps->common`, the frequency tables), the reader `*gb_host`, the fields of
  `*ac` and `ac->avctx->profile`, the bitstream buffer with the bytes after it, the read-only
  tables, and `Ext`, the state of the callees outside the footprint (logging, static tables).
* The callees are assumed contracts (hypotheses, `DecCallees`), stated on the same groups.
* The postcondition is the conclusion of `ParseModel.decext_spec`: `MI` and the live clauses
  `LiveC` hold of the values left, on every return. A run may also end at `abort` (reached from
  `read_sbr_grid`'s assertion) or at the compiler's bounds trap in `read_sbr_envelope` (`ud1` at
  `read_sbr_envelope.L60f9`): the spec is a `ProcSpecS` with these two stops (`DStops`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.DecExt

/-! ## Values -/

/-- `&sbr->data[b]`. -/
abbrev chA (s : BitVec 64) (b : Bool) : BitVec 64 := if b then s + 0x15b40#64 else s + 0x80#64

/-- The values of `sbr->data[b]`. -/
abbrev chV (d : DS) (b : Bool) : DV := if b then d.a.d1 else d.a.d0

/-- `DS` with `sbr->data[b]` at the values `v`. -/
def DS.setCh (d : DS) (b : Bool) (v : DV) : DS :=
  if b then { d with a := { d.a with d1 := v } } else { d with a := { d.a with d0 := v } }

/-- The fields of `SBRData` `read_sbr_grid` writes: `bs_num_env`, `bs_freq_res`, `bs_num_noise`,
`t_env` (with `t_env_num_env_old`), `t_q`. -/
abbrev dvGrid (v : DV) (n : Nat) (fr : List UInt8) (nn : Nat) (te tq : List UInt8) : DV :=
  { v with nenv := n, freqRes := fr, nnoise := nn, te := te, tq := tq }

/-- `read_sbr_grid`'s outcome on the values `v` left, result `ret` (`Grid.GridOut`): `DWF False`,
the border bound, `ret ∈ {0, -1}`, a live grid on `0`. -/
def GridV (v : DV) (ret : BitVec 32) : Prop :=
  DWF False v ∧ u8 v.te v.nenv ≤ 19 ∧ (ret = 0#32 ∨ ret = 0xffffffff#32)
  ∧ (ret = 0#32 → 1 ≤ v.nenv ∧ (∀ e, e ≤ v.nenv → u8 v.te e ≤ 19)
      ∧ (∀ e, e < v.nenv → u8 v.te e < u8 v.te (e + 1)))

variable [CodeEnv]

/-! ## The footprint groups -/

/-- A `GetBitContext` at `g` as the callees see it: `buffer`, `index = i`, `size_in_bits`
(raw), `size_in_bits_plus8`. -/
abbrev GbR (g : BitVec 64) (r : Rd) (i : BitVec 32) : Mem 64 → Prop := GbW g r.buf i r.p8

/-- The bitstream bytes and the table `ceil_log2` (read by `read_sbr_grid`). -/
abbrev BufW (r : Rd) : Mem 64 → Prop := Blocks [(r.buf, r.L), (lab "ceil_log2", 6)]

/-- `ac->avctx` at `ac + 8`. -/
abbrev AvW (ac : BitVec 64) (x : Args) : Mem 64 → Prop := Apply.c8 (ac + 8#64) x.avctx

/-! ## The callees' contracts (assumed)

Each callee of the decoder state gets the whole decoder state `SbrF` at `sbr`, its bit reader at
`gb`, the bitstream, `ac->avctx`, the jump table of `read_sbr_grid` and `Ext`, and gives them
back. What it may change is stated on the values. The logical variable `CA` names the addresses
(`sbr`, `ac`, the reader), so a contract also covers a callee whose arguments do not include
them (`read_sbr_dtdf` gets `sbr->usac` and `ch_data`). -/

structure CA where
  R : Mem 64 → Prop
  d : DS
  s : BitVec 64
  ac : BitVec 64
  g : BitVec 64
  r : Rd
  i : BitVec 32

/-- A callee's footprint at the values `d` and index `i`. -/
abbrev CF (Ext : Mem 64 → Prop) (c : CA) (d : DS) (i : BitVec 32) : Mem 64 → Prop :=
  SbrF d c.s ⋆ (GbR c.g c.r i ⋆ (BufW c.r ⋆ (AvW c.ac d.a ⋆ (Grid.JtW ⋆ Ext))))

/-- The convention and the footprint at entry, the reader's precondition. -/
abbrev CPre (need : Nat) (Ext : Mem 64 → Prop) (c : CA) (ra : Int64) (t : MachineData) : Prop :=
  CallPre need (CF Ext c c.d c.i ⋆ c.R) ra t ∧ c.r.ok c.i ∧ c.d.ok

/-- The convention and the footprint at the return, at values `d'` and index `i'`. -/
abbrev CPost (need : Nat) (Ext : Mem 64 → Prop) (c : CA) (ra : Int64) (t s : MachineData)
    (P : DS → Prop) : Prop :=
  ∃ d' i', P d' ∧ d'.ok ∧ XKeep c.d.a d'.a ∧ i'.toNat ≤ c.r.p8.toNat
    ∧ CallPost need (CF Ext c d' i' ⋆ c.R) ra t s

/-- `read_sbr_header(sbr, gb, 0)` (l.188-247), from `MI` with `reset = 0` (and no address wrap of
`*sbr`, for `sbr_make_f_tablelim`; `bs_limiter_bands ≤ 3`): the values left satisfy `HI`
(`ParseModel.hdr_spec`) and keep `id_aac`; the channels, `ps->common`, `kx`, `m`, `bs_coupling` and `sample_rate` are not written
by it; `usac = is_usac = 0`; the field widths of `bs_freq_scale`, `bs_alter_scale` and
`bs_limiter_bands`. -/
abbrev HdrSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_header")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.s ∧ arg1 t = c.g
      ∧ (arg2 t).setWidth 32 = 0#32 ∧ MI (c.d.a, c.d.h) ∧ c.d.a.reset = 0
      ∧ c.s.toNat + 0x60000 < 2 ^ 64 ∧ c.d.h.lb ≤ 3)
    (fun c ra t s => CPost need Ext c ra t s fun d' => HI (d'.a, d'.h)
      ∧ d'.a.idAac = c.d.a.idAac ∧ d'.a.d0 = c.d.a.d0 ∧ d'.a.d1 = c.d.a.d1
      ∧ d'.a.psc = c.d.a.psc ∧ d'.a.coupling = c.d.a.coupling
      ∧ d'.usac = 0#32 ∧ u8 d'.sp 3 < 4 ∧ u8 d'.sp 4 < 2 ∧ d'.h.lb < 4)

/-- `sbr_reset(ac, sbr)` (l.1113-1124) with `reset ≠ 0`, from `HI` and the header's field widths
(`sbr_reset`'s `ResetC`), no address wrap of `*sbr`, the ABI stack alignment: `MI`
(`ParseModel.reset_step`), `id_aac` kept, `DS.si` kept. -/
abbrev ResetSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "sbr_reset")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.ac ∧ arg1 t = c.s
      ∧ HI (c.d.a, c.d.h) ∧ c.d.a.reset ≠ 0
      ∧ u8 c.d.sp 3 ≤ 3 ∧ u8 c.d.sp 4 ≤ 1 ∧ c.d.h.lb ≤ 3 ∧ c.s.toNat + 0x60000 < 2 ^ 64
      ∧ isAligned 16 (t.regs.get64 .rsp + 8#64) = true)
    (fun c ra t s => CPost need Ext c ra t s fun d' => MI (d'.a, d'.h)
      ∧ d'.a.idAac = c.d.a.idAac ∧ d'.a.psc = c.d.a.psc ∧ (c.d.si → d'.si))

/-- `read_sbr_dtdf(sbr->usac, gb, ch_data, 0)` (l.837-856; the compiled routine takes `usac`),
with `bs_num_env ≤ 8`, `bs_num_noise ≤ 2` in both channels: no value of `DS` changes. -/
abbrev DtdfSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_dtdf")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ (arg0 t).setWidth 32 = c.d.usac ∧ arg1 t = c.g
      ∧ (arg2 t = c.s + 0x80#64 ∨ arg2 t = c.s + 0x15b40#64) ∧ (arg3 t).setWidth 32 = 0#32
      ∧ c.d.a.d0.nenv ≤ 8 ∧ c.d.a.d0.nnoise ≤ 2 ∧ c.d.a.d1.nenv ≤ 8 ∧ c.d.a.d1.nnoise ≤ 2)
    (fun c ra t s => CPost need Ext c ra t s fun d' => d' = c.d)

/-- `invfRead` on channel `ch` of the values. -/
def DS.invf (d : DS) (ch : Nat) (vals : Nat → Nat) : DS :=
  if ch = 0 then { d with a := { d.a with d0 := invfRead d.a.nq d.a.d0 vals } }
  else { d with a := { d.a with d1 := invfRead d.a.nq d.a.d1 vals } }

/-- `read_sbr_invf(sbr, gb, ch_data)` (l.827-835), with `n_q ≤ 5` and both `bs_invf_mode` arrays
of 10 bytes: `invfRead` (`ParseModel`). -/
abbrev InvfSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_invf")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.s ∧ arg1 t = c.g
      ∧ (arg2 t = c.s + 0x80#64 ∨ arg2 t = c.s + 0x15b40#64)
      ∧ c.d.a.nq ≤ 5 ∧ c.d.a.d0.invf.length = 10 ∧ c.d.a.d1.invf.length = 10)
    (fun c ra t s => CPost need Ext c ra t s fun d' =>
      ∃ vals, d' = c.d.invf (if arg2 t = c.s + 0x80#64 then 0 else 1) vals)

/-- `read_sbr_envelope(ac, sbr, gb, ch_data, ch)` (l.858-925), with `DWF False` of both channels,
`n[0] ≤ 24`, `n[1] ≤ 48`, `sbr` 32-aligned: no value of `DS` changes (abstraction 6 of the
model: the outcome is free). A run may stop at the bounds trap `read_sbr_envelope.L60f9`. -/
abbrev EnvSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecS (fun a => a = entry "read_sbr_envelope.L60f9") (entry "read_sbr_envelope")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.ac ∧ arg1 t = c.s ∧ arg2 t = c.g
      ∧ (arg3 t = c.s + 0x80#64 ∨ arg3 t = c.s + 0x15b40#64)
      ∧ DWF False c.d.a.d0 ∧ DWF False c.d.a.d1 ∧ c.d.a.n0 ≤ 24 ∧ c.d.a.n1 ≤ 48
      ∧ c.s.toNat % 32 = 0)
    (fun c ra t s => CPost need Ext c ra t s fun d' => d' = c.d)

/-- `read_sbr_noise(ac, sbr, gb, ch_data, ch)` (l.927-964), with `n_q ≤ 5` and `bs_num_noise ≤ 2`
in both channels: no value of `DS` changes. -/
abbrev NoiseSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "read_sbr_noise")
    (fun (c : CA) ra t => CPre need Ext c ra t ∧ arg0 t = c.ac ∧ arg1 t = c.s ∧ arg2 t = c.g
      ∧ (arg3 t = c.s + 0x80#64 ∨ arg3 t = c.s + 0x15b40#64)
      ∧ c.d.a.nq ≤ 5 ∧ c.d.a.d0.nnoise ≤ 2 ∧ c.d.a.d1.nnoise ≤ 2)
    (fun c ra t s => CPost need Ext c ra t s fun d' => d' = c.d)

/-- `read_sbr_grid(ac, sbr, gb, &sbr->data[b])`, with `DWF False` of the channel and
`t_env[bs_num_env] ≤ 19` (the logical variable is the pair `(c, b)`): the channel's values become
`dvGrid` of new fields with `GridV`; a run may end at `abort` (the routine's assertion). -/
abbrev GridSpec (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecA (entry "read_sbr_grid")
    (fun (cb : CA × Bool) ra t => CPre need Ext cb.1 ra t ∧ arg0 t = cb.1.ac ∧ arg1 t = cb.1.s
      ∧ arg2 t = cb.1.g ∧ arg3 t = chA cb.1.s cb.2 ∧ DWF False (chV cb.1.d cb.2)
      ∧ u8 (chV cb.1.d cb.2).te (chV cb.1.d cb.2).nenv ≤ 19)
    (fun cb ra t s => CPost need Ext cb.1 ra t s fun d' => ∃ n fr nn te tq,
      d' = cb.1.d.setCh cb.2 (dvGrid (chV cb.1.d cb.2) n fr nn te tq)
      ∧ GridV (dvGrid (chV cb.1.d cb.2) n fr nn te tq) ((s.regs.get64 .rax).setWidth 32))

/-- The logical variables of `ff_ps_read_data`'s contract. -/
structure PA where
  R : Mem 64 → Prop
  c : List UInt8
  g : BitVec 64
  r : Rd
  i : BitVec 32

/-- `ff_ps_read_data(avctx, gb, &sbr->ps.common, bits_left)` (aacps_common.c:133-289): the 764
bytes of `ps->common` keep `PsWF`'s clauses (the conclusion of `ParseModel.psread_wf`) and the
routine's own invariant `PI` (the bounds its array accesses need); the result is in
`[0, bits_left]`. -/
abbrev PsSpec (PI : List UInt8 → Prop) (need : Nat) (Ext : Mem 64 → Prop) : Prop :=
  cenv.ProcSpec (entry "ff_ps_read_data")
    (fun (p : PA) ra t => CallPre need ((p.c =@ arg2 t ⋆ (GbR p.g p.r p.i ⋆ (BufW p.r ⋆ Ext)))
        ⋆ p.R) ra t ∧ p.r.ok p.i ∧ arg1 t = p.g ∧ p.c.length = 764 ∧ PI p.c
      ∧ 0 ≤ ((arg3 t).setWidth 32).toInt)
    (fun p ra t s => ∃ c' i', (∀ h, PsWF p.c h → PsWF c' h) ∧ c'.length = 764 ∧ PI c'
      ∧ i'.toNat ≤ p.r.p8.toNat
      ∧ 0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt
      ∧ ((s.regs.get64 .rax).setWidth 32).toInt ≤ ((arg3 t).setWidth 32).toInt
      ∧ CallPost need ((c' =@ arg2 t ⋆ (GbR p.g p.r i' ⋆ (BufW p.r ⋆ Ext))) ⋆ p.R) ra t s)

/-- The callees: `kc` bytes of stack for the decoder-state callees, `k` for the logging ones. -/
abbrev DecCallees (PI : List UInt8 → Prop) (kc k : Nat) (Ext : Mem 64 → Prop) : Prop :=
  HdrSpec kc Ext ∧ ResetSpec kc Ext ∧ DtdfSpec kc Ext ∧ InvfSpec kc Ext ∧ EnvSpec kc Ext
  ∧ NoiseSpec kc Ext ∧ PsSpec PI kc Ext ∧ GridSpec kc Ext
  ∧ AvLogSpec Ext k ∧ AvReqSpec Ext k

/-! ## The specification -/

/-- `*gb_host` at `g` with `index = i`. -/
abbrev GhW (g : BitVec 64) (X : XA) (i : BitVec 32) : Mem 64 → Prop :=
  Apply.c8 g X.r.buf ⋆ (cell4 (g + 8#64) i ⋆ (cell4 (g + 0xc#64) X.sib ⋆ (cell4 (g + 0x10#64) X.r.p8
  ⋆ cell4 (g + 0x14#64) X.pad)))

/-- The fields of `*ac` (`avctx`, `oc[1].m4ac.sample_rate`, `ext_sample_rate`, `ps`,
`warned_he_aac_mono`) and `ac->avctx->profile`. -/
def AcF (ac : BitVec 64) (x : Args) (sr : BitVec 32) : Mem 64 → Prop :=
  cell4 (ac + 0x57e0#64) sr ⋆ (cell4 (ac + 0x57f4#64) x.extRate ⋆ (cell4 (ac + 0x5800#64) x.ps
  ⋆ (4 ?@ (ac + 0x8850#64) ⋆ 4 ?@ (x.avctx + 0x2b0#64))))

/-- The footprint at the values `d` and host index `i`. -/
def DecF (Ext : Mem 64 → Prop) (X : XA) (t : MachineData) (d : DS) (i : BitVec 32) :
    Mem 64 → Prop :=
  SbrF d (sbrA t) ⋆ (GhW (arg2 t) X i ⋆ (AvW (arg0 t) d.a ⋆ (AcF (arg0 t) d.a X.sr
  ⋆ (BufW X.r ⋆ (Grid.JtW ⋆ Ext)))))

/-- `DS.si` (`bs_limiter_bands ≤ 3`) and the layout of `*che` (as `ApplySpec.LayoutC`:
`che` and `sbr` 32-aligned, the signed bound past `sbr + 0x5fcc0`), and no address wrap of
`*sbr` (`sbr_reset`, `sbr_make_f_tablelim`). -/
def DecL (X : XA) (t : MachineData) : Prop :=
  X.d.si ∧ isAligned 32 (arg1 t) = true ∧ isAligned 32 (sbrA t) = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63 ∧ (sbrA t).toNat + 0x60000 < 2 ^ 64

/-- The side conditions: the model invariant `MI` of the values, `ff_ps_read_data`'s invariant
`PI` of `ps->common`, the reader, the jump table's
layout, the stack alignment (`vmovaps` to the frame). -/
def DecC (PI : List UInt8 → Prop) (X : XA) (t : MachineData) : Prop :=
  MI (X.d.a, X.d.h) ∧ X.d.ok ∧ PI X.d.a.psc ∧ X.r.ok X.i ∧ Grid.JtC
  ∧ (isAligned 16 (t.regs.get64 .rsp + 8#64) = true ∧ DecL X t)

/-- The proof's invariant form of `DecL`: with the frame's own bytes below `rsp` (`0x70`), which
the entry reads off `CallPre (decNeed kc)` (`CallPre.le`). -/
def DecLI (X : XA) (t : MachineData) : Prop :=
  X.d.si ∧ isAligned 32 (arg1 t) = true ∧ isAligned 32 (sbrA t) = true
  ∧ (sbrA t + 0x5fcc0#64).toInt + 1280 < 2 ^ 63 ∧ (sbrA t).toNat + 0x60000 < 2 ^ 64
  ∧ 0x70 ≤ (t.regs.get64 .rsp).toNat

/-- `DecC` with `DecLI`. -/
def DecCI (PI : List UInt8 → Prop) (X : XA) (t : MachineData) : Prop :=
  MI (X.d.a, X.d.h) ∧ X.d.ok ∧ PI X.d.a.psc ∧ X.r.ok X.i ∧ Grid.JtC
  ∧ (isAligned 16 (t.regs.get64 .rsp + 8#64) = true ∧ DecLI X t)

theorem DecCI.of {PI : List UInt8 → Prop} {X : XA} {t : MachineData} (h : DecC PI X t)
    (hr : 0x70 ≤ (t.regs.get64 .rsp).toNat) : DecCI PI X t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hr⟩

theorem DecCI.rsp {PI : List UInt8 → Prop} {X : XA} {t : MachineData} (h : DecCI PI X t) :
    0x70 ≤ (t.regs.get64 .rsp).toNat :=
  h.2.2.2.2.2.2.2.2.2.2.2

abbrev DecPre (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t : MachineData) : Prop :=
  CallPre (decNeed kc) (DecF Ext X t X.d X.i ⋆ X.R) ra t ∧ DecC PI X t

abbrev DecPost (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t s : MachineData) : Prop :=
  ∃ d' i', DecOut PI X d' ∧ i'.toNat ≤ X.r.p8.toNat
    ∧ (s.regs.get64 .rax).setWidth 32 = (arg4 t).setWidth 32
    ∧ CallPost (decNeed kc) (DecF Ext X t d' i' ⋆ X.R) ra t s

/-- `ff_aac_sbr_decode_extension` with its callees: it returns with `DecPost` or reaches a stop
of `DStops`. -/
abbrev DecExtSpec (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) : Prop :=
  ProcSpecS DStops (entry "ff_aac_sbr_decode_extension") (DecPre PI kc Ext) (DecPost PI kc Ext)

end Kraken.Examples.Sbr.DecExt
