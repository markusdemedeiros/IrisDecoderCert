import Kraken.X64.Examples.Sbr.Parse.DecExtSpec

/-!
# `ff_aac_sbr_decode_extension`: the frame, the block table

The memory at every label (`T`): the callee area below the frame, the frame's locals, the
footprint `DecF` at the current values, the saved registers and the return slot. The locals
(`rbp`-relative: the index after the header at `-0x58`, `cnt` at `-0x50`, `ac` at `-0x48`, the
copy `gbc` of the reader at `-0x40`) are raw before they are written (`Loc0`, `LocW0`), cells
after (`LocW`), and raw again at the exit (`LocE`).

The values at the labels of the prologue are given exactly as updates of the entry values
(`DS.st1`, `DS.pro`), so that `MI` is needed only of the entry values (`ParseModel.mi_extPro`);
those of `sbr_turnoff` likewise (`DS.off1`, `DS.off2`, `DS.off`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.DecExt

/-! ## Values at the labels -/

/-- After `sbr->reset = 0`, with `sample_rate = s` and `ext_sample_rate = e`. -/
def DS.st1 (d : DS) (s e : BitVec 32) : DS :=
  { d with a := { d.a with reset := 0, sampleRate := s, extRate := e } }

/-- The new `sample_rate` (`ext_sample_rate`): `2 * ac->oc[1].m4ac.sample_rate` if it was `0`. -/
abbrev newRate (v sr : BitVec 32) : BitVec 32 := if v = 0 then sr + sr else v

/-- After the prologue (`extPro` with `sr = er = 2 * ac->oc[1].m4ac.sample_rate`). -/
def DS.pro (d : DS) (sr : BitVec 32) : DS :=
  { d with a := extPro d.a (sr + sr) (sr + sr) }

/-- `sbr_turnoff`, stage 1: `start = ready = 0`, `usac = 0`. -/
def DS.off1 (d : DS) : DS :=
  { d with a := { d.a with start := 0, ready := 0 }, usac := 0 }

/-- Stage 2: `kx[1] = 32`, `m[1] = 0` (the `e_a[1]` stores are to raw bytes). -/
def DS.off2 (d : DS) : DS := { d with a := d.a.turnoff, usac := 0 }

/-- `sbr_turnoff`: `spectrum_params` all ones. -/
def DS.off (d : DS) : DS :=
  { d with a := d.a.turnoff, h := d.h.turnoff, usac := 0, sp := List.replicate 6 0xff }

variable [CodeEnv]

/-! ## The frame -/

/-- The locals before the copy of the reader (raw). -/
abbrev Loc0 (r : BitVec 64) : Mem 64 → Prop :=
  8 ?@ (r - 0x68#64) ⋆ (8 ?@ (r - 0x60#64) ⋆ (8 ?@ (r - 0x58#64) ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (16 ?@ (r - 0x48#64) ⋆ 8 ?@ (r - 0x38#64)))))

/-- The locals before `read_sbr_data`: `cnt`, `gbc` with index `gi`. -/
abbrev LocW0 (X : XA) (t₀ : MachineData) (gi : BitVec 32) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x68#64) ⋆ (8 ?@ (r - 0x60#64) ⋆ (Apply.c8 (r - 0x58#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x50#64) ⋆ (GbR (r - 0x48#64) X.r gi ⋆ 4 ?@ (r - 0x34#64)))))

/-- The locals in `read_sbr_data`: the index after the header `i0`, `cnt`, `ac`, `gbc`. -/
abbrev LocW (X : XA) (t₀ : MachineData) (i0 : BitVec 64) (gi : BitVec 32) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x68#64) ⋆ (Apply.c8 (r - 0x60#64) i0 ⋆ (Apply.c8 (r - 0x58#64) (arg4 t₀)
    ⋆ (Apply.c8 (r - 0x50#64) (arg0 t₀) ⋆ (GbR (r - 0x48#64) X.r gi ⋆ 4 ?@ (r - 0x34#64)))))

/-- The locals at the exit: only `cnt`. -/
abbrev LocE (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x68#64) ⋆ (8 ?@ (r - 0x60#64) ⋆ (Apply.c8 (r - 0x58#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (4 ?@ (r - 0x40#64) ⋆ (4 ?@ (r - 0x3c#64)
    ⋆ (4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64))))))))

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The six pushed registers. -/
abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Apply.c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (Apply.c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (Apply.c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (Apply.c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (Apply.c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (Apply.c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K)))))

abbrev BlankS (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K)))))

/-- The memory at every label: the return slot of a call and the callee's `kc` bytes, the
locals `LW`, the footprint at values `d` and host index `ih`, the saved registers `FR`. -/
abbrev T (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (LW : Mem 64 → Prop) (d : DS) (ih : BitVec 32) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ (LW ⋆ (DecF Ext X t₀ d ih
    ⋆ FR (Rest X.R ra t₀))))

/-- The registers of the frame after the prologue. -/
abbrev Fr (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x68#64 ∧ s.regs.get64 .rbp = r - 8#64
  ∧ s.regs.get64 .r14 = arg1 t₀

/-- `id_aac` (the low 32 bits of `r9` at entry) zero-extended, as `r13` holds it. -/
abbrev idZ (t₀ : MachineData) : BitVec 64 := ((arg5 t₀).setWidth 32).setWidth 64

/-- The registers before the header. -/
abbrev R0 (t₀ s : MachineData) : Prop :=
  Fr t₀ s ∧ s.regs.get64 .rdi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀
  ∧ s.regs.get64 .r13 = idZ t₀

/-- Memory before `read_sbr_data`, with `gbc`'s index `gi`. -/
abbrev Mm0 (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ s : MachineData)
    (gi : BitVec 32) (d : DS) (ih : BitVec 32) : Prop :=
  s.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (LocW0 X t₀ gi) d ih

/-- The two readers within bounds. -/
abbrev RdB (X : XA) (gi ih : BitVec 32) : Prop :=
  gi.toNat ≤ X.r.p8.toNat ∧ ih.toNat ≤ X.r.p8.toNat

/-- In the prologue: values `d`, the readers within bounds. -/
abbrev P0 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ s : MachineData) (d : DS) : Prop :=
  DecCI PI X t₀ ∧ R0 t₀ s ∧ ∃ gi ih, RdB X gi ih ∧ Mm0 kc Ext X ra t₀ s gi d ih

/-- The values' invariant after the header: `HI`, `DS.si`, the header's field
widths while a reset is pending (`sbr_reset`'s `ResetC`). -/
def Inv1 (PI : List UInt8 → Prop) (X : XA) (d : DS) : Prop :=
  HI (d.a, d.h) ∧ d.ok ∧ PI d.a.psc ∧ XKeep X.d.a d.a
  ∧ (d.si ∧ (d.a.reset ≠ 0 → u8 d.sp 3 ≤ 3 ∧ u8 d.sp 4 ≤ 1 ∧ d.h.lb ≤ 3))

/-- After the reset: `MI`. -/
def Inv2 (PI : List UInt8 → Prop) (X : XA) (d : DS) : Prop :=
  MI (d.a, d.h) ∧ d.ok ∧ PI d.a.psc ∧ XKeep X.d.a d.a ∧ d.si

/-- At the end: `MI` and the live clauses. -/
def EInv (PI : List UInt8 → Prop) (X : XA) (d : DS) : Prop :=
  MI (d.a, d.h) ∧ LiveC d.a ∧ d.ok ∧ PI d.a.psc ∧ XKeep X.d.a d.a ∧ d.si

/-- Before `sbr_turnoff`: `AI`. -/
def TInv (PI : List UInt8 → Prop) (X : XA) (d : DS) : Prop :=
  AI d.a ∧ d.ok ∧ PI d.a.psc ∧ XKeep X.d.a d.a ∧ d.si

/-- Between the header and `read_sbr_data` (`rbx = sbr`, `r12 = ac`, `r13 = id_aac`). -/
abbrev PH (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ s : MachineData) (I : DS → Prop) : Prop :=
  DecCI PI X t₀ ∧ Fr t₀ s ∧ s.regs.get64 .rbx = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀
  ∧ s.regs.get64 .r13 = idZ t₀
  ∧ ∃ gi d ih, I d ∧ RdB X gi ih ∧ Mm0 kc Ext X ra t₀ s gi d ih

/-- The exit path (`r12 = ac`; `r15` is the bit count, unconstrained): the values `d` with `I`,
the locals `LocE`. -/
abbrev PX (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ s : MachineData) (I : DS → Prop) : Prop :=
  DecCI PI X t₀ ∧ Fr t₀ s ∧ s.regs.get64 .r12 = arg0 t₀
  ∧ ∃ d ih, I d ∧ ih.toNat ≤ X.r.p8.toNat
    ∧ (s.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (LocE t₀) d ih)

/-- `id_aac` (the low 32 bits of `r9` at entry). -/
abbrev idA (t₀ : MachineData) : BitVec 32 := (arg5 t₀).setWidth 32

/-- After `sbr->id_aac = id_aac; sbr->ready_for_dequant = 1` (the head of `read_sbr_data`). -/
def DS.dat (d : DS) (id : BitVec 32) : DS := { d with a := { d.a with idAac := id, ready := 1 } }

/-- Before a channel element: `Inv2`, the decoder started, `id_aac` as stored. -/
def SInv (PI : List UInt8 → Prop) (X : XA) (t₀ : MachineData) (d : DS) : Prop :=
  Inv2 PI X d ∧ d.a.start ≠ 0 ∧ d.a.idAac = idA t₀

/-- In `read_sbr_data` (the locals `LocW`: the index after the header `i0`, `cnt`, `ac`, `gbc`
with index `gi`): the values `d` with `I i0 gi d`, the readers within bounds. -/
abbrev PD (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ s : MachineData) (I : BitVec 64 → BitVec 32 → DS → Prop) : Prop :=
  DecCI PI X t₀ ∧ Fr t₀ s
  ∧ ∃ i0 gi d ih, I i0 gi d ∧ RdB X gi ih
    ∧ (s.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih)

/-- After the inlined `get_bits1` of `bs_add_harmonic_flag` (`L409`): the reader's next index in
`eax` (not stored yet), `size_in_bits_plus8` in `esi`, the buffer in `rdi`. -/
def RegB (X : XA) (s : MachineData) : Prop :=
  ((s.regs.get64 .rax).setWidth 32).toNat ≤ X.r.p8.toNat ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8
  ∧ s.regs.get64 .rdi = X.r.buf

/-- `RegB` with the reader's next index in `r`. -/
def RegI (X : XA) (s : MachineData) (r : Reg64) : Prop :=
  ((s.regs.get64 r).setWidth 32).toNat ≤ X.r.p8.toNat ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8
  ∧ s.regs.get64 .rdi = X.r.buf

/-- In the unrolled `bs_add_harmonic` loop of `data[0]` (`r10` the next element, a multiple of 4
below `r9 = n[1] & ~3`; `r8 = n[1] & 3` the rest). -/
def HL (d : DS) (s : MachineData) : Prop :=
  s.regs.get64 .r9 = BitVec.ofNat 64 (d.a.n1 / 4 * 4) ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (d.a.n1 % 4)
  ∧ (s.regs.get64 .r10).toNat % 4 = 0 ∧ (s.regs.get64 .r10).toNat + 4 ≤ d.a.n1 / 4 * 4

/-- In a channel pair element after `read_sbr_grid` on `data[0]`: `EInv` but the live clause of
`data[1]` (the started decoder, `id_aac = 1`). -/
def CInv0 (PI : List UInt8 → Prop) (X : XA) (d : DS) : Prop :=
  MI (d.a, d.h) ∧ Live d.a.d0 ∧ d.ok ∧ PI d.a.psc ∧ XKeep X.d.a d.a ∧ d.si ∧ d.a.start ≠ 0
  ∧ d.a.idAac = 1#32

/-! ### The inlined `copy_sbr_grid(&sbr->data[1], &sbr->data[0])` (coupled path) -/

/-- `bs_freq_res[0]`, `t_env_num_env_old` from `dst`'s own last envelope. -/
def cpA (d1 : DV) : DV :=
  { d1 with freqRes := d1.freqRes.set 0 (d1.freqRes.getD d1.nenv 0),
            te := d1.te.set 9 (d1.te.getD d1.nenv 0) }
/-- `bs_freq_res[1..8]`, `t_env[0..7]` from `src`. -/
def cpB (d0 d1 : DV) : DV :=
  { cpA d1 with freqRes := (cpA d1).freqRes.take 1 ++ (d0.freqRes.drop 1).take 8,
                te := d0.te.take 8 ++ (cpA d1).te.drop 8 }
/-- `t_env[8]`. -/
def cpB2 (d0 d1 : DV) : DV := { cpB d0 d1 with te := (cpB d0 d1).te.set 8 (d0.te.getD 8 0) }
/-- `t_q[0..1]`, `t_q[2]`. -/
def cpC (d0 d1 : DV) : DV :=
  { cpB2 d0 d1 with tq := (d0.tq.take 2 ++ (cpB d0 d1).tq.drop 2).set 2 (d0.tq.getD 2 0) }
/-- `bs_num_env`. -/
def cpD (d0 d1 : DV) : DV := { cpC d0 d1 with nenv := d0.nenv }
/-- `bs_num_noise` (`bs_amp_res`, `bs_frame_class`, `e_a[1]` are raw). -/
def cpE (d0 d1 : DV) : DV := { cpD d0 d1 with nnoise := d0.nnoise }

/-- `bs_invf_mode[1]` of channel 1 from its `bs_invf_mode[0]` (the first `memcpy`). -/
def invfShift (d1 : DV) : DV :=
  { d1 with invf := mk 10 (fun i => if i < 5 then old d1.invf i else old d1.invf (i - 5)) }

/-- In the copy: `data[1]` at `f data[0] data[1]` of values with `CInv0`. -/
def CpI (PI : List UInt8 → Prop) (X : XA) (f : DV → DV → DV) (d : DS) : Prop :=
  ∃ e, CInv0 PI X e ∧ d = e.setCh true (f e.a.d0 e.a.d1)

/-- The table's labels of the channel pair element (`L16e`–`Laed`, `L466`), in a third match. -/
def tableC (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop
  | "ff_aac_sbr_decode_extension.L466", s => PD PI kc Ext X ra t₀ s (fun _ _ d => TInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = idZ t₀
  | "ff_aac_sbr_decode_extension.L481", s => PD PI kc Ext X ra t₀ s (fun _ _ d => TInv PI X d)
  | "ff_aac_sbr_decode_extension.L16e", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => SInv PI X t₀ d ∧ (s.regs.get64 .r8).setWidth 32 = gi)
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀ ∧ idA t₀ = 1#32
  | "ff_aac_sbr_decode_extension.L1a7", s => PD PI kc Ext X ra t₀ s (fun _ _ d => SInv PI X t₀ d)
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀ ∧ idA t₀ = 1#32
      ∧ ((s.regs.get64 .rcx).setWidth 32).toNat ≤ X.r.p8.toNat ∧ (s.regs.get64 .rdx).setWidth 32 = X.r.p8
      ∧ s.regs.get64 .rax = X.r.buf
  | "ff_aac_sbr_decode_extension.L1d4", s => PD PI kc Ext X ra t₀ s (fun _ _ d => SInv PI X t₀ d)
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀ ∧ idA t₀ = 1#32
  | "ff_aac_sbr_decode_extension.L1ea", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => TInv PI X d ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → CInv0 PI X d))
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
  | "ff_aac_sbr_decode_extension.L483", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => TInv PI X d ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → CInv0 PI X d))
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
  | "ff_aac_sbr_decode_extension.L591", s => PD PI kc Ext X ra t₀ s (fun _ _ d => CInv0 PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
  | "ff_aac_sbr_decode_extension.L215", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => TInv PI X d ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → EInv PI X d))
      ∧ s.regs.get64 .r12 = arg0 t₀
  | "ff_aac_sbr_decode_extension.L239", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
  | "ff_aac_sbr_decode_extension.L251", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
  | "ff_aac_sbr_decode_extension.L26a", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbx = sbrA t₀
  | "ff_aac_sbr_decode_extension.L27c", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbx = sbrA t₀
  | "ff_aac_sbr_decode_extension.L29e", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rbx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .r13 = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L2c2", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rbx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .r13 = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L2e3", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rbx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .r13 = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L76e", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .rdx = t₀.regs.get64 .rsp - 0x48#64 ∧ s.regs.get64 .rdi = arg0 t₀
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .rcx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L779", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.L781", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.L7b5", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d) ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L8e2", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 d.a.n1 ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (d.a.n1 % 4)
      ∧ 4 ≤ d.a.n1) ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L8ec", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L913", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L939", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L960", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L998", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ (s.regs.get64 .r10).toNat + (s.regs.get64 .r8).toNat = d.a.n1
      ∧ 0 < (s.regs.get64 .r8).toNat ∧ (s.regs.get64 .r8).toNat < 4) ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L9a7", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ ∃ b, s.regs.get64 .rax = sbrA t₀ + 0xb1#64 + BitVec.ofNat 64 b
        ∧ b + (s.regs.get64 .r8).toNat = d.a.n1 ∧ (s.regs.get64 .r9).toNat < (s.regs.get64 .r8).toNat
        ∧ (s.regs.get64 .r8).toNat < 4) ∧ RegI X s .rcx
  | "ff_aac_sbr_decode_extension.L9d4", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d) ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.La04", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d) ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.La29", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 d.a.n1 ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (d.a.n1 % 4)
      ∧ 4 ≤ d.a.n1) ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.La33", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.La59", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.La80", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.Laa6", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.Ladf", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ (s.regs.get64 .r10).toNat + (s.regs.get64 .r8).toNat = d.a.n1
      ∧ 0 < (s.regs.get64 .r8).toNat ∧ (s.regs.get64 .r8).toNat < 4) ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.Laed", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ ∃ b, s.regs.get64 .rdx = sbrA t₀ + 0x15b71#64 + BitVec.ofNat 64 b
        ∧ b + (s.regs.get64 .r8).toNat = d.a.n1 ∧ (s.regs.get64 .r9).toNat < (s.regs.get64 .r8).toNat
        ∧ (s.regs.get64 .r8).toNat < 4) ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L5a2", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => CInv0 PI X d ∧ s.regs.get64 .rax = BitVec.ofNat 64 d.a.d1.nenv)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
  | "ff_aac_sbr_decode_extension.L5cc", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => CpI PI X (fun _ v => cpA v) d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L5e1", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => CpI PI X (fun _ v => cpA v) d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L5fd", s => PD PI kc Ext X ra t₀ s (fun _ _ d => CpI PI X cpB d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L614", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => CpI PI X cpB2 d
        ∧ (s.regs.get64 .rax).setWidth 16 = BitVec.ofInt 16 (Int.ofBytes (d.a.d0.tq.take 2)))
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L62b", s => PD PI kc Ext X ra t₀ s (fun _ _ d => CpI PI X cpC d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L647", s => PD PI kc Ext X ra t₀ s (fun _ _ d => CpI PI X cpD d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L663", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rdx = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L686", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbx = sbrA t₀ + 0x15b40#64
  | "ff_aac_sbr_decode_extension.L69a", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
  | "ff_aac_sbr_decode_extension.L6b3", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbx = sbrA t₀
  | "ff_aac_sbr_decode_extension.L6d0", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => ∃ e, EInv PI X e ∧ d = e.setCh true (invfShift e.a.d1))
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbx = sbrA t₀
  | "ff_aac_sbr_decode_extension.L6ed", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbx = sbrA t₀
  | "ff_aac_sbr_decode_extension.L708", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .rbx = sbrA t₀ + 0x80#64
  | "ff_aac_sbr_decode_extension.L729", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀
  | "ff_aac_sbr_decode_extension.L751", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = arg0 t₀
  | _, _ => False

/-- The table's labels of the extension data (`Lb40`–`Lcd3`), in a separate match: the blocks
before them see the main table's match only. -/
def tableE (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop
  | "ff_aac_sbr_decode_extension.Lb40", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => EInv PI X d ∧ (s.regs.get64 .rdx).setWidth 32 = gi)
      ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8 ∧ s.regs.get64 .rdi = X.r.buf
  | "ff_aac_sbr_decode_extension.Lb64", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => EInv PI X d ∧ (s.regs.get64 .rdx).setWidth 32 = gi)
      ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8 ∧ s.regs.get64 .rdi = X.r.buf
  | "ff_aac_sbr_decode_extension.Lb86", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ ((s.regs.get64 .rax).setWidth 32).toNat ≤ 270
  | "ff_aac_sbr_decode_extension.Lb9d", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .rbx = arg1 t₀ + 0x53f20#64 ∧ s.regs.get64 .r13 = arg0 t₀
      ∧ 8 ≤ ((s.regs.get64 .rax).setWidth 32).toNat ∧ ((s.regs.get64 .rax).setWidth 32).toNat ≤ 2160
  | "ff_aac_sbr_decode_extension.Lbd4", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .rbx = arg1 t₀ + 0x53f20#64 ∧ s.regs.get64 .r13 = arg0 t₀
      ∧ 6 ≤ ((s.regs.get64 .r12).setWidth 32).toNat ∧ ((s.regs.get64 .r12).setWidth 32).toNat ≤ 2158
  | "ff_aac_sbr_decode_extension.Lbe6", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .rbx = arg1 t₀ + 0x53f20#64 ∧ s.regs.get64 .r13 = arg0 t₀
      ∧ 6 ≤ ((s.regs.get64 .r12).setWidth 32).toNat ∧ ((s.regs.get64 .r12).setWidth 32).toNat ≤ 2158
  | "ff_aac_sbr_decode_extension.Lbf5", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .rbx = arg1 t₀ + 0x53f20#64 ∧ s.regs.get64 .r13 = arg0 t₀
      ∧ 6 ≤ ((s.regs.get64 .r12).setWidth 32).toNat ∧ ((s.regs.get64 .r12).setWidth 32).toNat ≤ 2158
      ∧ 0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt
      ∧ ((s.regs.get64 .rax).setWidth 32).toInt ≤ ((s.regs.get64 .r12).setWidth 32).toInt
  | "ff_aac_sbr_decode_extension.Lc1c", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lc1f", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lc41", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => EInv PI X d ∧ (s.regs.get64 .rdx).setWidth 32 = gi)
      ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8 ∧ s.regs.get64 .rdi = X.r.buf
  | "ff_aac_sbr_decode_extension.Lc4b", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => EInv PI X d ∧ (s.regs.get64 .rdx).setWidth 32 = gi)
      ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8 ∧ s.regs.get64 .rdi = X.r.buf
  | "ff_aac_sbr_decode_extension.Lc67", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lc7d", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lc83", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => EInv PI X d ∧ (s.regs.get64 .rdx).setWidth 32 = gi)
      ∧ (s.regs.get64 .rsi).setWidth 32 = X.r.p8
  | "ff_aac_sbr_decode_extension.Lca0", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lcbb", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lcc0", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.Lcd3", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | l, s => tableC PI kc Ext X ra t₀ l s

abbrev table (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop
  | "ff_aac_sbr_decode_extension", s => s = t₀ ∧ DecCI PI X t₀
      ∧ (t₀.dmem =⋆ T kc Ext X ra t₀ (BlankS (t₀.regs.get64 .rsp))
          (Loc0 (t₀.regs.get64 .rsp)) X.d X.i)
  | "ff_aac_sbr_decode_extension.L21", s => DecCI PI X t₀ ∧ R0 t₀ s
      ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀
      ∧ (s.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (Loc0 (t₀.regs.get64 .rsp)) X.d X.i)
  | "ff_aac_sbr_decode_extension.L36", s => DecCI PI X t₀ ∧ R0 t₀ s
      ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀
      ∧ Mm0 kc Ext X ra t₀ s X.i X.d X.i
  | "ff_aac_sbr_decode_extension.L63", s => DecCI PI X t₀ ∧ R0 t₀ s
      ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ ∃ ih, RdB X X.i ih ∧ Mm0 kc Ext X ra t₀ s X.i X.d ih
  | "ff_aac_sbr_decode_extension.L301", s => P0 PI kc Ext X ra t₀ s (X.d.st1 0 X.d.a.extRate)
      ∧ s.regs.get64 .rcx = arg3 t₀ ∧ X.d.a.sampleRate = 0
  | "ff_aac_sbr_decode_extension.L31c", s =>
      P0 PI kc Ext X ra t₀ s (X.d.st1 (newRate X.d.a.sampleRate X.sr) 0)
      ∧ s.regs.get64 .rcx = arg3 t₀ ∧ X.d.a.extRate = 0
  | "ff_aac_sbr_decode_extension.L8b", s =>
      P0 PI kc Ext X ra t₀ s (X.d.st1 (newRate X.d.a.sampleRate X.sr) (newRate X.d.a.extRate X.sr))
      ∧ s.regs.get64 .rcx = arg3 t₀
  | "ff_aac_sbr_decode_extension.Lad", s =>
      P0 PI kc Ext X ra t₀ s (X.d.st1 (newRate X.d.a.sampleRate X.sr) (newRate X.d.a.extRate X.sr))
      ∧ (s.regs.get64 .rax).toNat ≤ X.r.p8.toNat ∧ s.regs.get64 .rsi = X.r.p8.setWidth 64
  | "ff_aac_sbr_decode_extension.Ld4", s => P0 PI kc Ext X ra t₀ s (X.d.pro X.sr)
      ∧ (s.regs.get64 .rax).toNat ≤ X.r.p8.toNat ∧ s.regs.get64 .rsi = X.r.p8.setWidth 64
  | "ff_aac_sbr_decode_extension.Lff", s => P0 PI kc Ext X ra t₀ s (X.d.pro X.sr)
  | "ff_aac_sbr_decode_extension.L333", s => P0 PI kc Ext X ra t₀ s (X.d.pro X.sr)
  | "ff_aac_sbr_decode_extension.L10d", s => PH PI kc Ext X ra t₀ s (Inv1 PI X)
  | "ff_aac_sbr_decode_extension.L11d", s => PH PI kc Ext X ra t₀ s
      (fun d => Inv1 PI X d ∧ d.a.reset ≠ 0)
  | "ff_aac_sbr_decode_extension.L128", s => PH PI kc Ext X ra t₀ s (Inv2 PI X)
  | "ff_aac_sbr_decode_extension.L349", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => SInv PI X t₀ d ∧ (s.regs.get64 .r8).setWidth 32 = gi)
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀
      ∧ idA t₀ &&& 0xfffffffd#32 = 0#32
  | "ff_aac_sbr_decode_extension.L164", s => PD PI kc Ext X ra t₀ s
      (fun _ gi d => SInv PI X t₀ d ∧ (s.regs.get64 .r8).setWidth 32 = gi)
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀ ∧ s.regs.get64 .r13 = idZ t₀
      ∧ idA t₀ &&& 0xfffffffd#32 ≠ 0#32
  | "ff_aac_sbr_decode_extension.L384", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => SInv PI X t₀ d)
      ∧ s.regs.get64 .rsi = sbrA t₀ ∧ s.regs.get64 .r12 = arg0 t₀ ∧ idA t₀ ≠ 1#32
  | "ff_aac_sbr_decode_extension.L39d", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => TInv PI X d ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → EInv PI X d))
      ∧ s.regs.get64 .r12 = sbrA t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
  | "ff_aac_sbr_decode_extension.L3bd", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = sbrA t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = t₀.regs.get64 .rsp - 0x48#64
  | "ff_aac_sbr_decode_extension.L3cb", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = sbrA t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = t₀.regs.get64 .rsp - 0x48#64
  | "ff_aac_sbr_decode_extension.L3e4", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ s.regs.get64 .r12 = sbrA t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x80#64
      ∧ s.regs.get64 .rbx = arg0 t₀
  | "ff_aac_sbr_decode_extension.L401", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.L409", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.L43d", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ RegB X s
  | "ff_aac_sbr_decode_extension.Lb1a", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
      ∧ RegB X s
  | "ff_aac_sbr_decode_extension.L48b", s => PD PI kc Ext X ra t₀ s (fun _ _ d => TInv PI X d)
  | "ff_aac_sbr_decode_extension.L4a1", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => ∃ d₀, TInv PI X d₀ ∧ d = d₀.off1)
  | "ff_aac_sbr_decode_extension.L4b7", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => ∃ d₀, TInv PI X d₀ ∧ d = d₀.off2)
  | "ff_aac_sbr_decode_extension.L4cd", s => PD PI kc Ext X ra t₀ s
      (fun _ _ d => ∃ d₀, TInv PI X d₀ ∧ d = d₀.off2)
  | "ff_aac_sbr_decode_extension.L4e2", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d)
  | "ff_aac_sbr_decode_extension.L4ee", s => PX PI kc Ext X ra t₀ s (EInv PI X)
  | "ff_aac_sbr_decode_extension.L50b", s => PX PI kc Ext X ra t₀ s (EInv PI X)
  | "ff_aac_sbr_decode_extension.L527", s => PX PI kc Ext X ra t₀ s (TInv PI X)
  | "ff_aac_sbr_decode_extension.L53d", s => PX PI kc Ext X ra t₀ s
      (fun d => ∃ d₀, TInv PI X d₀ ∧ d = d₀.off1)
  | "ff_aac_sbr_decode_extension.L553", s => PX PI kc Ext X ra t₀ s
      (fun d => ∃ d₀, TInv PI X d₀ ∧ d = d₀.off2)
  | "ff_aac_sbr_decode_extension.L569", s => PX PI kc Ext X ra t₀ s
      (fun d => ∃ d₀, TInv PI X d₀ ∧ d = d₀.off2)
  | "ff_aac_sbr_decode_extension.L57e", s => PX PI kc Ext X ra t₀ s (EInv PI X)
  | "ff_aac_sbr_decode_extension.done", s => DecCI PI X t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s ∧ (s.regs.get64 .rax).setWidth 32 = (arg4 t₀).setWidth 32
      ∧ ∃ d ih, EInv PI X d ∧ ih.toNat ≤ X.r.p8.toNat
        ∧ (s.dmem =⋆ T kc Ext X ra t₀ (Saved t₀) (LocE t₀) d ih)
  | "ff_aac_sbr_decode_extension.L7de", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ s.regs.get64 .r9 = BitVec.ofNat 64 d.a.n1 ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (d.a.n1 % 4)
      ∧ 4 ≤ d.a.n1) ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L7e8", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L80e", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L835", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L85b", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d ∧ HL d s)
      ∧ RegI X s .rdx
  | "ff_aac_sbr_decode_extension.L898", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ (s.regs.get64 .r10).toNat + (s.regs.get64 .r8).toNat = d.a.n1
      ∧ 0 < (s.regs.get64 .r8).toNat ∧ (s.regs.get64 .r8).toNat < 4) ∧ RegI X s .rax
  | "ff_aac_sbr_decode_extension.L8b0", s => PD PI kc Ext X ra t₀ s (fun _ _ d => EInv PI X d
      ∧ ∃ b, s.regs.get64 .rdx = sbrA t₀ + 0xb1#64 + BitVec.ofNat 64 b
        ∧ b + (s.regs.get64 .r8).toNat = d.a.n1 ∧ (s.regs.get64 .r9).toNat < (s.regs.get64 .r8).toNat
        ∧ (s.regs.get64 .r8).toNat < 4) ∧ RegI X s .rax
  | l, s => tableE PI kc Ext X ra t₀ l s

/-- The ranking: a level per region, decreasing along the code (the prologue, the header loop,
`read_sbr_data` up to the `bs_add_harmonic` loops, the loops, the extension data, the exit), and
within a loop the trips left. Not reducible: the blocks rewrite it with the `var_*` equations. -/
def var : Label → MachineData → Nat
  | "ff_aac_sbr_decode_extension", _ => 9002
  | "ff_aac_sbr_decode_extension.L21", _ => 9002
  | "ff_aac_sbr_decode_extension.L36", _ => 9002
  | "ff_aac_sbr_decode_extension.L63", _ => 9002
  | "ff_aac_sbr_decode_extension.L301", _ => 9002
  | "ff_aac_sbr_decode_extension.L31c", _ => 9002
  | "ff_aac_sbr_decode_extension.L8b", _ => 9001
  | "ff_aac_sbr_decode_extension.Lad", _ => 9001
  | "ff_aac_sbr_decode_extension.Ld4", _ => 9001
  | "ff_aac_sbr_decode_extension.L333", _ => 9001
  | "ff_aac_sbr_decode_extension.Lff", _ => 9000
  | "ff_aac_sbr_decode_extension.L10d", _ => 9000
  | "ff_aac_sbr_decode_extension.L11d", _ => 9000
  | "ff_aac_sbr_decode_extension.L128", _ => 9000
  | "ff_aac_sbr_decode_extension.L164", _ => 9000
  | "ff_aac_sbr_decode_extension.L16e", _ => 9000
  | "ff_aac_sbr_decode_extension.L1a7", _ => 9000
  | "ff_aac_sbr_decode_extension.L1d4", _ => 9000
  | "ff_aac_sbr_decode_extension.L1ea", _ => 9000
  | "ff_aac_sbr_decode_extension.L215", _ => 9000
  | "ff_aac_sbr_decode_extension.L239", _ => 9000
  | "ff_aac_sbr_decode_extension.L251", _ => 9000
  | "ff_aac_sbr_decode_extension.L26a", _ => 9000
  | "ff_aac_sbr_decode_extension.L27c", _ => 9000
  | "ff_aac_sbr_decode_extension.L29e", _ => 9000
  | "ff_aac_sbr_decode_extension.L2c2", _ => 9000
  | "ff_aac_sbr_decode_extension.L2e3", _ => 9000
  | "ff_aac_sbr_decode_extension.L349", _ => 9000
  | "ff_aac_sbr_decode_extension.L384", _ => 9000
  | "ff_aac_sbr_decode_extension.L39d", _ => 9000
  | "ff_aac_sbr_decode_extension.L3bd", _ => 9000
  | "ff_aac_sbr_decode_extension.L3cb", _ => 9000
  | "ff_aac_sbr_decode_extension.L3e4", _ => 9000
  | "ff_aac_sbr_decode_extension.L401", _ => 9000
  | "ff_aac_sbr_decode_extension.L409", _ => 9000
  | "ff_aac_sbr_decode_extension.L43d", _ => 9000
  | "ff_aac_sbr_decode_extension.L466", _ => 8990
  | "ff_aac_sbr_decode_extension.L481", _ => 8990
  | "ff_aac_sbr_decode_extension.L483", _ => 8980
  | "ff_aac_sbr_decode_extension.L591", _ => 8970
  | "ff_aac_sbr_decode_extension.L5a2", _ => 8970
  | "ff_aac_sbr_decode_extension.L5cc", _ => 8970
  | "ff_aac_sbr_decode_extension.L5e1", _ => 8970
  | "ff_aac_sbr_decode_extension.L5fd", _ => 8970
  | "ff_aac_sbr_decode_extension.L614", _ => 8970
  | "ff_aac_sbr_decode_extension.L62b", _ => 8970
  | "ff_aac_sbr_decode_extension.L647", _ => 8970
  | "ff_aac_sbr_decode_extension.L663", _ => 8970
  | "ff_aac_sbr_decode_extension.L686", _ => 8970
  | "ff_aac_sbr_decode_extension.L69a", _ => 8970
  | "ff_aac_sbr_decode_extension.L6b3", _ => 8970
  | "ff_aac_sbr_decode_extension.L6d0", _ => 8970
  | "ff_aac_sbr_decode_extension.L6ed", _ => 8970
  | "ff_aac_sbr_decode_extension.L708", _ => 8970
  | "ff_aac_sbr_decode_extension.L729", _ => 8970
  | "ff_aac_sbr_decode_extension.L751", _ => 8970
  | "ff_aac_sbr_decode_extension.L76e", _ => 8960
  | "ff_aac_sbr_decode_extension.L779", _ => 8960
  | "ff_aac_sbr_decode_extension.L781", _ => 8960
  | "ff_aac_sbr_decode_extension.L7b5", _ => 8960
  | "ff_aac_sbr_decode_extension.L7de", _ => 6100
  | "ff_aac_sbr_decode_extension.L7e8", s => 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L80e", s => 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L835", s => 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L85b", s => 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L898", _ => 6004
  | "ff_aac_sbr_decode_extension.L8b0", s => 6000 + ((s.regs.get64 .r8).toNat - (s.regs.get64 .r9).toNat)
  | "ff_aac_sbr_decode_extension.Lb1a", _ => 5000
  | "ff_aac_sbr_decode_extension.Lb40", _ => 4900
  | "ff_aac_sbr_decode_extension.Lb64", _ => 4800
  | "ff_aac_sbr_decode_extension.Lb86", _ => 4700
  | "ff_aac_sbr_decode_extension.Lc41", _ => 900
  | "ff_aac_sbr_decode_extension.Lc4b", _ => 890
  | "ff_aac_sbr_decode_extension.Lc67", _ => 880
  | "ff_aac_sbr_decode_extension.Lc7d", _ => 870
  | "ff_aac_sbr_decode_extension.Lc83", _ => 860
  | "ff_aac_sbr_decode_extension.Lcc0", _ => 850
  | "ff_aac_sbr_decode_extension.Lcd3", _ => 840
  | "ff_aac_sbr_decode_extension.Lc1c", _ => 510
  | "ff_aac_sbr_decode_extension.Lc1f", _ => 500
  | "ff_aac_sbr_decode_extension.Lca0", _ => 400
  | "ff_aac_sbr_decode_extension.Lcbb", _ => 390
  | "ff_aac_sbr_decode_extension.Lb9d", s => 1000 + ((s.regs.get64 .rax).setWidth 32).toNat
  | "ff_aac_sbr_decode_extension.Lbd4", s => 1001 + ((s.regs.get64 .r12).setWidth 32).toNat
  | "ff_aac_sbr_decode_extension.Lbe6", s => 1001 + ((s.regs.get64 .r12).setWidth 32).toNat
  | "ff_aac_sbr_decode_extension.Lbf5", s => 1001 + ((s.regs.get64 .r12).setWidth 32).toNat
  | "ff_aac_sbr_decode_extension.L8e2", _ => 8100
  | "ff_aac_sbr_decode_extension.L998", _ => 8004
  | "ff_aac_sbr_decode_extension.L9d4", _ => 7900
  | "ff_aac_sbr_decode_extension.La04", _ => 7900
  | "ff_aac_sbr_decode_extension.La29", _ => 7100
  | "ff_aac_sbr_decode_extension.Ladf", _ => 7004
  | "ff_aac_sbr_decode_extension.L8ec", s => 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L913", s => 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L939", s => 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L960", s => 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.L9a7", s => 8000 + ((s.regs.get64 .r8).toNat - (s.regs.get64 .r9).toNat)
  | "ff_aac_sbr_decode_extension.La33", s => 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.La59", s => 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.La80", s => 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.Laa6", s => 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat)
  | "ff_aac_sbr_decode_extension.Laed", s => 7000 + ((s.regs.get64 .r8).toNat - (s.regs.get64 .r9).toNat)
  | _, _ => 0

theorem var_entry (s : MachineData) : var "ff_aac_sbr_decode_extension" s = 9002 := rfl

theorem var_L21 (s : MachineData) : var "ff_aac_sbr_decode_extension.L21" s = 9002 := rfl

theorem var_L36 (s : MachineData) : var "ff_aac_sbr_decode_extension.L36" s = 9002 := rfl

theorem var_L63 (s : MachineData) : var "ff_aac_sbr_decode_extension.L63" s = 9002 := rfl

theorem var_L301 (s : MachineData) : var "ff_aac_sbr_decode_extension.L301" s = 9002 := rfl

theorem var_L31c (s : MachineData) : var "ff_aac_sbr_decode_extension.L31c" s = 9002 := rfl

theorem var_L8b (s : MachineData) : var "ff_aac_sbr_decode_extension.L8b" s = 9001 := rfl

theorem var_Lad (s : MachineData) : var "ff_aac_sbr_decode_extension.Lad" s = 9001 := rfl

theorem var_Ld4 (s : MachineData) : var "ff_aac_sbr_decode_extension.Ld4" s = 9001 := rfl

theorem var_L333 (s : MachineData) : var "ff_aac_sbr_decode_extension.L333" s = 9001 := rfl

theorem var_Lff (s : MachineData) : var "ff_aac_sbr_decode_extension.Lff" s = 9000 := rfl

theorem var_L10d (s : MachineData) : var "ff_aac_sbr_decode_extension.L10d" s = 9000 := rfl

theorem var_L11d (s : MachineData) : var "ff_aac_sbr_decode_extension.L11d" s = 9000 := rfl

theorem var_L128 (s : MachineData) : var "ff_aac_sbr_decode_extension.L128" s = 9000 := rfl

theorem var_L4ee (s : MachineData) : var "ff_aac_sbr_decode_extension.L4ee" s = 0 := rfl

theorem var_L349 (s : MachineData) : var "ff_aac_sbr_decode_extension.L349" s = 9000 := rfl

theorem var_L164 (s : MachineData) : var "ff_aac_sbr_decode_extension.L164" s = 9000 := rfl

theorem var_L384 (s : MachineData) : var "ff_aac_sbr_decode_extension.L384" s = 9000 := rfl

theorem var_L39d (s : MachineData) : var "ff_aac_sbr_decode_extension.L39d" s = 9000 := rfl

theorem var_L3bd (s : MachineData) : var "ff_aac_sbr_decode_extension.L3bd" s = 9000 := rfl

theorem var_L3cb (s : MachineData) : var "ff_aac_sbr_decode_extension.L3cb" s = 9000 := rfl

theorem var_L3e4 (s : MachineData) : var "ff_aac_sbr_decode_extension.L3e4" s = 9000 := rfl

theorem var_L401 (s : MachineData) : var "ff_aac_sbr_decode_extension.L401" s = 9000 := rfl

theorem var_L409 (s : MachineData) : var "ff_aac_sbr_decode_extension.L409" s = 9000 := rfl

theorem var_L43d (s : MachineData) : var "ff_aac_sbr_decode_extension.L43d" s = 9000 := rfl

theorem var_Lb1a (s : MachineData) : var "ff_aac_sbr_decode_extension.Lb1a" s = 5000 := rfl

theorem var_L48b (s : MachineData) : var "ff_aac_sbr_decode_extension.L48b" s = 0 := rfl

theorem var_L4a1 (s : MachineData) : var "ff_aac_sbr_decode_extension.L4a1" s = 0 := rfl

theorem var_L4b7 (s : MachineData) : var "ff_aac_sbr_decode_extension.L4b7" s = 0 := rfl

theorem var_L4cd (s : MachineData) : var "ff_aac_sbr_decode_extension.L4cd" s = 0 := rfl

theorem var_L4e2 (s : MachineData) : var "ff_aac_sbr_decode_extension.L4e2" s = 0 := rfl

theorem var_L50b (s : MachineData) : var "ff_aac_sbr_decode_extension.L50b" s = 0 := rfl

theorem var_L527 (s : MachineData) : var "ff_aac_sbr_decode_extension.L527" s = 0 := rfl

theorem var_L53d (s : MachineData) : var "ff_aac_sbr_decode_extension.L53d" s = 0 := rfl

theorem var_L553 (s : MachineData) : var "ff_aac_sbr_decode_extension.L553" s = 0 := rfl

theorem var_L569 (s : MachineData) : var "ff_aac_sbr_decode_extension.L569" s = 0 := rfl

theorem var_L57e (s : MachineData) : var "ff_aac_sbr_decode_extension.L57e" s = 0 := rfl

theorem var_done (s : MachineData) : var "ff_aac_sbr_decode_extension.done" s = 0 := rfl

theorem var_L7de (s : MachineData) : var "ff_aac_sbr_decode_extension.L7de" s = 6100 := rfl

theorem var_L898 (s : MachineData) : var "ff_aac_sbr_decode_extension.L898" s = 6004 := rfl

theorem var_L7e8 (s : MachineData) : var "ff_aac_sbr_decode_extension.L7e8" s
    = 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L80e (s : MachineData) : var "ff_aac_sbr_decode_extension.L80e" s
    = 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L835 (s : MachineData) : var "ff_aac_sbr_decode_extension.L835" s
    = 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L85b (s : MachineData) : var "ff_aac_sbr_decode_extension.L85b" s
    = 6004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L8b0 (s : MachineData) : var "ff_aac_sbr_decode_extension.L8b0" s
    = 6000 + ((s.regs.get64 .r8).toNat - (s.regs.get64 .r9).toNat) := rfl

theorem var_Lb40 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lb40" s = 4900 := rfl

theorem var_Lb64 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lb64" s = 4800 := rfl

theorem var_Lb86 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lb86" s = 4700 := rfl

theorem var_Lc41 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc41" s = 900 := rfl

theorem var_Lc4b (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc4b" s = 890 := rfl

theorem var_Lc67 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc67" s = 880 := rfl

theorem var_Lc7d (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc7d" s = 870 := rfl

theorem var_Lc83 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc83" s = 860 := rfl

theorem var_Lcc0 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lcc0" s = 850 := rfl

theorem var_Lcd3 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lcd3" s = 840 := rfl

theorem var_Lc1c (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc1c" s = 510 := rfl

theorem var_Lc1f (s : MachineData) : var "ff_aac_sbr_decode_extension.Lc1f" s = 500 := rfl

theorem var_Lca0 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lca0" s = 400 := rfl

theorem var_Lcbb (s : MachineData) : var "ff_aac_sbr_decode_extension.Lcbb" s = 390 := rfl

theorem var_Lb9d (s : MachineData) : var "ff_aac_sbr_decode_extension.Lb9d" s
    = 1000 + ((s.regs.get64 .rax).setWidth 32).toNat := rfl

theorem var_Lbd4 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lbd4" s
    = 1001 + ((s.regs.get64 .r12).setWidth 32).toNat := rfl

theorem var_Lbe6 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lbe6" s
    = 1001 + ((s.regs.get64 .r12).setWidth 32).toNat := rfl

theorem var_Lbf5 (s : MachineData) : var "ff_aac_sbr_decode_extension.Lbf5" s
    = 1001 + ((s.regs.get64 .r12).setWidth 32).toNat := rfl

theorem var_L16e (s : MachineData) : var "ff_aac_sbr_decode_extension.L16e" s = 9000 := rfl

theorem var_L1a7 (s : MachineData) : var "ff_aac_sbr_decode_extension.L1a7" s = 9000 := rfl

theorem var_L1d4 (s : MachineData) : var "ff_aac_sbr_decode_extension.L1d4" s = 9000 := rfl

theorem var_L1ea (s : MachineData) : var "ff_aac_sbr_decode_extension.L1ea" s = 9000 := rfl

theorem var_L215 (s : MachineData) : var "ff_aac_sbr_decode_extension.L215" s = 9000 := rfl

theorem var_L239 (s : MachineData) : var "ff_aac_sbr_decode_extension.L239" s = 9000 := rfl

theorem var_L251 (s : MachineData) : var "ff_aac_sbr_decode_extension.L251" s = 9000 := rfl

theorem var_L26a (s : MachineData) : var "ff_aac_sbr_decode_extension.L26a" s = 9000 := rfl

theorem var_L27c (s : MachineData) : var "ff_aac_sbr_decode_extension.L27c" s = 9000 := rfl

theorem var_L29e (s : MachineData) : var "ff_aac_sbr_decode_extension.L29e" s = 9000 := rfl

theorem var_L2c2 (s : MachineData) : var "ff_aac_sbr_decode_extension.L2c2" s = 9000 := rfl

theorem var_L2e3 (s : MachineData) : var "ff_aac_sbr_decode_extension.L2e3" s = 9000 := rfl

theorem var_L466 (s : MachineData) : var "ff_aac_sbr_decode_extension.L466" s = 8990 := rfl

theorem var_L481 (s : MachineData) : var "ff_aac_sbr_decode_extension.L481" s = 8990 := rfl

theorem var_L483 (s : MachineData) : var "ff_aac_sbr_decode_extension.L483" s = 8980 := rfl

theorem var_L76e (s : MachineData) : var "ff_aac_sbr_decode_extension.L76e" s = 8960 := rfl

theorem var_L779 (s : MachineData) : var "ff_aac_sbr_decode_extension.L779" s = 8960 := rfl

theorem var_L781 (s : MachineData) : var "ff_aac_sbr_decode_extension.L781" s = 8960 := rfl

theorem var_L7b5 (s : MachineData) : var "ff_aac_sbr_decode_extension.L7b5" s = 8960 := rfl

theorem var_L8e2 (s : MachineData) : var "ff_aac_sbr_decode_extension.L8e2" s = 8100 := rfl

theorem var_L998 (s : MachineData) : var "ff_aac_sbr_decode_extension.L998" s = 8004 := rfl

theorem var_L9d4 (s : MachineData) : var "ff_aac_sbr_decode_extension.L9d4" s = 7900 := rfl

theorem var_La04 (s : MachineData) : var "ff_aac_sbr_decode_extension.La04" s = 7900 := rfl

theorem var_La29 (s : MachineData) : var "ff_aac_sbr_decode_extension.La29" s = 7100 := rfl

theorem var_Ladf (s : MachineData) : var "ff_aac_sbr_decode_extension.Ladf" s = 7004 := rfl

theorem var_L591 (s : MachineData) : var "ff_aac_sbr_decode_extension.L591" s = 8970 := rfl

theorem var_L5a2 (s : MachineData) : var "ff_aac_sbr_decode_extension.L5a2" s = 8970 := rfl

theorem var_L5cc (s : MachineData) : var "ff_aac_sbr_decode_extension.L5cc" s = 8970 := rfl

theorem var_L5e1 (s : MachineData) : var "ff_aac_sbr_decode_extension.L5e1" s = 8970 := rfl

theorem var_L5fd (s : MachineData) : var "ff_aac_sbr_decode_extension.L5fd" s = 8970 := rfl

theorem var_L614 (s : MachineData) : var "ff_aac_sbr_decode_extension.L614" s = 8970 := rfl

theorem var_L62b (s : MachineData) : var "ff_aac_sbr_decode_extension.L62b" s = 8970 := rfl

theorem var_L647 (s : MachineData) : var "ff_aac_sbr_decode_extension.L647" s = 8970 := rfl

theorem var_L663 (s : MachineData) : var "ff_aac_sbr_decode_extension.L663" s = 8970 := rfl

theorem var_L686 (s : MachineData) : var "ff_aac_sbr_decode_extension.L686" s = 8970 := rfl

theorem var_L69a (s : MachineData) : var "ff_aac_sbr_decode_extension.L69a" s = 8970 := rfl

theorem var_L6b3 (s : MachineData) : var "ff_aac_sbr_decode_extension.L6b3" s = 8970 := rfl

theorem var_L6d0 (s : MachineData) : var "ff_aac_sbr_decode_extension.L6d0" s = 8970 := rfl

theorem var_L6ed (s : MachineData) : var "ff_aac_sbr_decode_extension.L6ed" s = 8970 := rfl

theorem var_L708 (s : MachineData) : var "ff_aac_sbr_decode_extension.L708" s = 8970 := rfl

theorem var_L729 (s : MachineData) : var "ff_aac_sbr_decode_extension.L729" s = 8970 := rfl

theorem var_L751 (s : MachineData) : var "ff_aac_sbr_decode_extension.L751" s = 8970 := rfl

theorem var_L8ec (s : MachineData) : var "ff_aac_sbr_decode_extension.L8ec" s
    = 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L913 (s : MachineData) : var "ff_aac_sbr_decode_extension.L913" s
    = 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L939 (s : MachineData) : var "ff_aac_sbr_decode_extension.L939" s
    = 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L960 (s : MachineData) : var "ff_aac_sbr_decode_extension.L960" s
    = 8004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_L9a7 (s : MachineData) : var "ff_aac_sbr_decode_extension.L9a7" s
    = 8000 + ((s.regs.get64 .r8).toNat - (s.regs.get64 .r9).toNat) := rfl

theorem var_La33 (s : MachineData) : var "ff_aac_sbr_decode_extension.La33" s
    = 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_La59 (s : MachineData) : var "ff_aac_sbr_decode_extension.La59" s
    = 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_La80 (s : MachineData) : var "ff_aac_sbr_decode_extension.La80" s
    = 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_Laa6 (s : MachineData) : var "ff_aac_sbr_decode_extension.Laa6" s
    = 7004 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .r10).toNat) := rfl

theorem var_Laed (s : MachineData) : var "ff_aac_sbr_decode_extension.Laed" s
    = 7000 + ((s.regs.get64 .r8).toNat - (s.regs.get64 .r9).toNat) := rfl

macro "grind_cells'" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

/-- What a return leaves: the frame's cells still in place below the popped return slot. -/
abbrev Post' (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  0x70 ≤ r.toNat ∧ ∃ d i, EInv PI X d ∧ i.toNat ≤ X.r.p8.toNat
    ∧ (s.regs.get64 .rax).setWidth 32 = (arg4 t₀).setWidth 32
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 8 ?@ r ⋆ (8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ (LocE t₀
        ⋆ (DecF Ext X t₀ d i ⋆ Saved t₀ X.R)))))

/-- The exits: the return, or a stop (`DStops`). -/
abbrev Exit (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ : MachineData) (a : Int64) (s : MachineData) : Prop :=
  (a = ra ∧ Post' PI kc Ext X ra t₀ s) ∨ DStops a

abbrev BlockOb (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64)
    (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table PI kc Ext X ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table PI kc Ext X ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table PI kc Ext X ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ Exit PI kc Ext X ra t₀ a s ⦄

end Kraken.Examples.Sbr.DecExt
