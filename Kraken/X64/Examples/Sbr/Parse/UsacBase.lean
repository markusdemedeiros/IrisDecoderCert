import Kraken.X64.Examples.Sbr.Parse.UsacCfg
import Kraken.X64.Examples.Sbr.Parse.Lib

/-!
# `ff_aac_sbr_decode_usac_data`: the assertions between blocks

The frame (`push rbp`, five saved registers, `sub $0x18`): the saved registers at
`r - 0x30 .. r - 0x8` (`r` the entry `rsp`), the locals at `r - 0x48 .. r - 0x30` (`indep_flag`
at `-0x2c(%rbp) = r - 0x34`; the old `spectrum_params` bytes at `-0x34(%rbp)`, `-0x30(%rbp)`
during the default header), a call's return slot at `r - 0x50`, the callee's reservation below.

The values between blocks are a `USt` with `Inv` (the fields outside the footprint kept, the
bytes of `spectrum_params` in step with `Hid`, the reader's bound) and a stage of the model's
row `usac_spec` (`ParseModel.lean`): `MI` with `reset = 0` before the header, `HI` after it, `MI`
after the reset, `MI` with live grids after the channel element, and `MI ∧ LiveC` (`Fin`) on the
way to the return of `0`. The default header and the inlined `copy_sbr_grid` have their own
intermediate values (`dhA`..`dhR`, `cpA`..`cpE`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

/-! ## Values -/

/-- `sbr_ch`, `indep_flag` (the low halves of `r8`, `r9` at entry); `id_aac`. -/
abbrev chv (t₀ : MachineData) : BitVec 32 := (arg4 t₀).setWidth 32
abbrev ivv (t₀ : MachineData) : BitVec 32 := (arg5 t₀).setWidth 32
abbrev idv (t₀ : MachineData) : BitVec 32 := if chv t₀ = 2#32 then 1#32 else 0#32

/-- The values kept between blocks. -/
def Inv (A : UA) (st : USt) : Prop :=
  UKeep A.2.x st.x ∧ SpOk st ∧ st.i.toNat ≤ A.1.p8.toNat

/-- Before the header: `MI`, `reset = 0`, `usac = 1`. -/
def S0 (st : USt) : Prop := MI (st.x, st.h) ∧ st.x.reset = 0 ∧ st.u = 1#32

/-- `S0` with `id_aac` set. -/
def S1 (t₀ : MachineData) (st : USt) : Prop := S0 st ∧ st.x.idAac = idv t₀

/-- A reset pending: the field widths of `bs_freq_scale`, `bs_alter_scale` (bytes 3 and 4 of
`spectrum_params`; from the header or the default header). -/
def SpW (st : USt) : Prop := st.x.reset ≠ 0#32 → u8 st.sp 3 ≤ 3 ∧ u8 st.sp 4 ≤ 1

/-- After the header (before the reset): `HI`, `SpW`. -/
def SH (t₀ : MachineData) (st : USt) : Prop :=
  HI (st.x, st.h) ∧ st.x.idAac = idv t₀ ∧ st.u = 1#32 ∧ SpW st

/-- After the reset: `MI`. -/
def SM (t₀ : MachineData) (st : USt) : Prop :=
  MI (st.x, st.h) ∧ st.x.idAac = idv t₀ ∧ (st.u = 1#32 ∨ st.u = 0#32)

/-- After a successful grid of channel 0 / of both channels. -/
def SE0 (t₀ : MachineData) (st : USt) : Prop := SM t₀ st ∧ Live st.x.d0
def SE01 (t₀ : MachineData) (st : USt) : Prop := SM t₀ st ∧ Live st.x.d0 ∧ Live st.x.d1

/-- On the way to the return of `0`. -/
def Fin (st : USt) : Prop := MI (st.x, st.h) ∧ LiveC st.x

/-! ### The default header (`copy_usac_default_header` and the change test) -/

/-- The byte `j` of `ue->sbr` (`ue + 0xc + j`). -/
abbrev ub (q : UQ) (j : Nat) : UInt8 := q.uev.getD j 0

/-- After `bs_start_freq` (byte 0 of `spectrum_params`). -/
def dhA (q : UQ) (st : USt) : USt := { st with sp := st.sp.set 0 (ub q 1) }
/-- After `bs_stop_freq`, `bs_freq_scale`. -/
def dhB (q : UQ) (st : USt) : USt :=
  { st with sp := ((st.sp.set 0 (ub q 1)).set 1 (ub q 2)).set 3 (ub q 3) }
/-- After `bs_alter_scale`, `bs_noise_bands`: the six bytes. -/
def dsp (q : UQ) (st : USt) : List UInt8 :=
  ((((st.sp.set 0 (ub q 1)).set 1 (ub q 2)).set 3 (ub q 3)).set 4 (ub q 4 &&& 1)).set 5 (ub q 5)
def dhC (q : UQ) (st : USt) : USt := { st with sp := dsp q st }
/-- After `bs_limiter_bands`, `bs_limiter_gains`. -/
def dhD (q : UQ) (st : USt) : USt :=
  { st with sp := dsp q st, h := { st.h with lb := u8 q.uev 6 },
            x := { st.x with limGains := u8 q.uev 7 } }
/-- After `bs_interpol_freq`, `bs_smoothing_mode`: `Hid` with the new `bs_start_freq`. -/
def dh (q : UQ) (st : USt) : USt :=
  { st with sp := dsp q st, h := { start := u8 q.uev 1, xover := st.h.xover, lb := u8 q.uev 6 },
            x := { st.x with limGains := u8 q.uev 7,
                             interpol := BitVec.ofNat 32 (u8 q.uev 8 % 2),
                             smooth := BitVec.ofNat 32 (u8 q.uev 8 / 2 % 2) } }
/-- After the change test: `reset = 1` if the bytes changed. -/
def dhR (q : UQ) (st : USt) : USt :=
  { dh q st with x := { (dh q st).x with reset := if dsp q st = st.sp then 0#32 else 1#32 } }

/-! ### `copy_sbr_grid(&sbr->data[1], &sbr->data[0])` (inlined) -/

/-- `bs_freq_res[0]`, `t_env_num_env_old` from `dst`'s own last envelope. -/
def cpA (d1 : DV) : DV :=
  { d1 with freqRes := d1.freqRes.set 0 (d1.freqRes.getD d1.nenv 0),
            te := d1.te.set 9 (d1.te.getD d1.nenv 0) }
/-- `bs_freq_res[1..8]`, `t_env[0..7]` from `src`. -/
def cpB (d0 d1 : DV) : DV :=
  { cpA d1 with freqRes := (cpA d1).freqRes.take 1 ++ (d0.freqRes.drop 1).take 8,
                te := d0.te.take 8 ++ (cpA d1).te.drop 8 }
/-- `t_env[8]`, `t_q[0..1]`. -/
def cpC (d0 d1 : DV) : DV :=
  { cpB d0 d1 with te := (cpB d0 d1).te.set 8 (d0.te.getD 8 0),
                   tq := d0.tq.take 2 ++ (cpB d0 d1).tq.drop 2 }
/-- `t_q[2]`, `bs_num_env`. -/
def cpD (d0 d1 : DV) : DV :=
  { cpC d0 d1 with tq := (cpC d0 d1).tq.set 2 (d0.tq.getD 2 0), nenv := d0.nenv }
/-- `bs_num_noise` (`bs_amp_res`, `bs_frame_class`, `e_a[1]` are raw). -/
def cpE (d0 d1 : DV) : DV := { cpD d0 d1 with nnoise := d0.nnoise }

/-- `bs_invf_mode[1]` of channel 1 from its `bs_invf_mode[0]` (the first `memcpy`). -/
def invfShift (d1 : DV) : DV :=
  { d1 with invf := mk 10 (fun i => if i < 5 then old d1.invf i else old d1.invf (i - 5)) }

/-- A state with new channels. -/
abbrev USt.wd1 (st : USt) (d : DV) : USt := { st with x := { st.x with d1 := d } }

variable [CodeEnv]

/-! ## The frame -/

/-- The saved registers. -/
abbrev Sv (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15) ⋆ c8 (r - 0x8#64) (t₀.regs.get64 .rbp)))))

/-- Their slots before the pushes / after the pops. -/
abbrev Bs (r : BitVec 64) : Mem 64 → Prop :=
  8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64) ⋆ 8 ?@ (r - 0x8#64)))))

/-- The locals, raw. -/
abbrev LocR (r : BitVec 64) : Mem 64 → Prop :=
  12 ?@ (r - 0x48#64) ⋆ (4 ?@ (r - 0x3c#64) ⋆ (2 ?@ (r - 0x38#64) ⋆ (2 ?@ (r - 0x36#64)
    ⋆ 4 ?@ (r - 0x34#64))))

/-- The locals with `indep_flag`. -/
abbrev LocI (r : BitVec 64) (iv : BitVec 32) : Mem 64 → Prop :=
  12 ?@ (r - 0x48#64) ⋆ (4 ?@ (r - 0x3c#64) ⋆ (2 ?@ (r - 0x38#64) ⋆ (2 ?@ (r - 0x36#64)
    ⋆ cell4 (r - 0x34#64) iv)))

/-- The locals with `indep_flag` and the old `spectrum_params` bytes. -/
abbrev LocT (r : BitVec 64) (iv : BitVec 32) (l4 l2 : List UInt8) : Mem 64 → Prop :=
  12 ?@ (r - 0x48#64) ⋆ (l4 =@ (r - 0x3c#64) ⋆ (l2 =@ (r - 0x38#64) ⋆ (2 ?@ (r - 0x36#64)
    ⋆ cell4 (r - 0x34#64) iv)))

/-- The memory at a label: the call slot, the callee's reservation, the footprint, the locals,
the saved registers, the return address, the caller's rest. -/
abbrev UM (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (Lc Sg : Mem 64 → Prop)
    (st : USt) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x50#64) ⋆ (Reserve (cneed k) (r - 0x50#64) ⋆ (UF A.1 st ⋆ (Lc ⋆ (Sg
    ⋆ (RetCell ra r ⋆ A.1.R)))))

/-- The fixed facts: the side conditions at entry, the arguments. -/
abbrev Fix (A : UA) (t₀ : MachineData) : Prop :=
  UsacC A.1 A.2 ∧ arg0 t₀ = A.1.a ∧ arg1 t₀ = A.1.c ∧ arg2 t₀ = A.1.ue ∧ arg3 t₀ = A.1.g
  ∧ StkC t₀

/-- The registers of the body. -/
abbrev Fr (A : UA) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x48#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
  ∧ s.regs.get64 .r12 = A.1.a ∧ s.regs.get64 .rbx = A.1.c ∧ s.regs.get64 .r14 = A.1.g

/-- A label of the body: the frame, `r13 = sbr`, a stage `P` of the values, the memory with
locals `Lc`. -/
abbrev At (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (Lc : Mem 64 → Prop)
    (P : USt → Prop) : Prop :=
  Fix A t₀ ∧ Fr A t₀ s ∧ s.regs.get64 .r13 = sA A.1.c
  ∧ ∃ st, Inv A st ∧ P st ∧ (s.dmem =⋆ UM k A ra t₀ Lc (Sv t₀) st)

/-- `At` with `indep_flag` in its local. -/
abbrev AtI (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (P : USt → Prop) : Prop :=
  At k A ra t₀ s (LocI (t₀.regs.get64 .rsp) (ivv t₀)) P

/-- `At` with `r15 = &sbr->data[0]`. -/
abbrev AtD (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (P : USt → Prop) : Prop :=
  AtI k A ra t₀ s P ∧ s.regs.get64 .r15 = dAc A.1.c 0

/-- The return paths: `UsacOut` on the value in `eax`. -/
abbrev AtX (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Fix A t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x48#64
  ∧ ∃ st, UsacOut A st ((s.regs.get64 .rax).setWidth 32)
    ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st)

/-- The harmonic loops: `n[1]` (`movslq`), `MI ∧ LiveC`, the registers of the loop. -/
abbrev AtH (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (R : USt → Prop) : Prop :=
  AtI k A ra t₀ s (fun st => Fin st ∧ R st)

/-- The default header: the values `st₀` at its start (`S1`), the old bytes in the locals,
the old `bs_limiter_bands` in `eax`, the current values `f st₀`. -/
abbrev AtDH (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (f : USt → USt)
    (P : USt → Prop) : Prop :=
  Fix A t₀ ∧ Fr A t₀ s ∧ s.regs.get64 .r13 = sA A.1.c ∧ s.regs.get64 .rdx = A.1.ue
  ∧ ∃ st₀, Inv A st₀ ∧ S1 t₀ st₀ ∧ P st₀
    ∧ s.regs.get64 .rax = (BitVec.ofNat 32 st₀.h.lb).setWidth 64
    ∧ (s.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st₀.sp.take 4)
        (st₀.sp.drop 4)) (Sv t₀) (f st₀))

/-- The coupled path's copy: the values `st` before it (`SE0`), the current channel 1. -/
abbrev AtCp (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (f : DV → DV → DV) : Prop :=
  AtD k A ra t₀ s (fun _ => True) ∧ ∃ st, Inv A st ∧ SE0 t₀ st ∧ st.x.coupling = 1#32
    ∧ st.x.d1.nenv < 9 ∧ s.regs.get64 .rax = BitVec.ofNat 64 st.x.d1.nenv
    ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
        (st.wd1 (f st.x.d0 st.x.d1)))

/-- `AtCp` after `rax` is overwritten (from `L3763` on). -/
abbrev AtCq (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) (f : DV → DV → DV) : Prop :=
  AtD k A ra t₀ s (fun _ => True) ∧ ∃ st, Inv A st ∧ SE0 t₀ st ∧ st.x.coupling = 1#32
    ∧ st.x.d1.nenv < 9
    ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
        (st.wd1 (f st.x.d0 st.x.d1)))

/-- `n[1]` as the loops read it. -/
abbrev n1v (st : USt) : BitVec 64 := BitVec.ofNat 64 st.x.n1

/-- A harmonic loop head/body: counter `i` even below the bound `b = n[1] & ~1`, `n = n[1]`. -/
abbrev Lp (st : USt) (i b n : BitVec 64) : Prop :=
  n = n1v st ∧ b = BitVec.ofNat 64 (st.x.n1 / 2 * 2) ∧ i.toNat % 2 = 0 ∧ i.toNat < b.toNat

/-- The last odd bit: counter `i = n[1] - 1`. -/
abbrev Lo (st : USt) (i : BitVec 64) : Prop := i.toNat + 1 = st.x.n1

/-! ## The table -/

/-! ### The assertions, one per label -/

/-- The assertion at `ff_aac_sbr_decode_usac_data`. -/
def T_entry (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  s = t₀ ∧ Fix A t₀
      ∧ (s.dmem =⋆ UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) (Bs (t₀.regs.get64 .rsp)) A.2)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3361`. -/
def T_L3361 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Fix A t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x48#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = arg5 t₀
      ∧ (s.dmem =⋆ UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) (Sv t₀) A.2)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3388`. -/
def T_L3388 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (At k A ra t₀ s (LocR (t₀.regs.get64 .rsp)) S0
      ∧ s.regs.get64 .rdi = A.1.a ∧ s.regs.get64 .rsi = A.1.c ∧ s.regs.get64 .rdx = A.1.ue
      ∧ s.regs.get64 .rcx = A.1.g ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = arg5 t₀)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L33a3`. -/
def T_L33a3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (At k A ra t₀ s (LocR (t₀.regs.get64 .rsp)) (S1 t₀)
      ∧ s.regs.get64 .rdx = A.1.ue ∧ s.regs.get64 .rcx = A.1.g ∧ s.regs.get64 .r9 = arg5 t₀)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L33ba`. -/
def T_L33ba (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (fun st => S1 t₀ st
        ∧ s.regs.get64 .rcx = st.i.setWidth 64)
      ∧ s.regs.get64 .rdx = A.1.ue ∧ s.regs.get64 .rsi = A.1.buf)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L33e6`. -/
def T_L33e6 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (fun st => S1 t₀ st
        ∧ s.regs.get64 .rax = st.i.setWidth 64)
      ∧ s.regs.get64 .rdx = A.1.ue ∧ s.regs.get64 .rsi = A.1.buf
      ∧ s.regs.get64 .rdi = A.1.p8.setWidth 64)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3410`. -/
def T_L3410 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (fun st => S1 t₀ st
        ∧ s.regs.get64 .rcx = st.i.setWidth 64)
      ∧ s.regs.get64 .rdx = A.1.ue ∧ s.regs.get64 .rsi = A.1.buf
      ∧ s.regs.get64 .rdi = A.1.p8.setWidth 64)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L343d`. -/
def T_L343d (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (S1 t₀) ∧ s.regs.get64 .rdx = A.1.ue)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3475`. -/
def T_L3475 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (S1 t₀) ∧ s.regs.get64 .rdx = A.1.ue)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L34b0`. -/
def T_L34b0 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (S1 t₀) ∧ s.regs.get64 .rdx = A.1.ue)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L34dd`. -/
def T_L34dd (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (S1 t₀) ∧ s.regs.get64 .rdx = A.1.ue)
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L34f7`. -/
def T_L34f7 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtDH k A ra t₀ s id (fun _ => True))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L350f`. -/
def T_L350f (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtDH k A ra t₀ s (dhA A.1) (fun _ => True))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3523`. -/
def T_L3523 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtDH k A ra t₀ s (dhB A.1) (fun _ => True))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L353a`. -/
def T_L353a (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtDH k A ra t₀ s (dhC A.1) (fun _ => True))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L354e`. -/
def T_L354e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtDH k A ra t₀ s (dhD A.1) (fun _ => True)
      ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u8 A.1.uev 6))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3569` (`AtDH` without `rdx`: L354e
overwrites it with `bs_smoothing_mode`). -/
def T_L3569 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (Fix A t₀ ∧ Fr A t₀ s ∧ s.regs.get64 .r13 = sA A.1.c
      ∧ (∃ st₀, Inv A st₀ ∧ S1 t₀ st₀
        ∧ s.regs.get64 .rax = (BitVec.ofNat 32 st₀.h.lb).setWidth 64
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocT (t₀.regs.get64 .rsp) (ivv t₀) (st₀.sp.take 4)
            (st₀.sp.drop 4)) (Sv t₀) (dh A.1 st₀)))
      ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u8 A.1.uev 6))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L358e`. -/
def T_L358e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (Fix A t₀ ∧ Fr A t₀ s
      ∧ s.regs.get64 .r13 = sA A.1.c ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (u8 A.1.uev 6)
      ∧ ∃ st₀, Inv A st₀ ∧ S1 t₀ st₀
        ∧ s.regs.get64 .rax = (BitVec.ofNat 32 st₀.h.lb).setWidth 64
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (dhR A.1 st₀)))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L359b`. -/
def T_L359b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (Fix A t₀ ∧ Fr A t₀ s
      ∧ s.regs.get64 .r13 = sA A.1.c
      ∧ ∃ st₀, Inv A st₀ ∧ S1 t₀ st₀ ∧ (dhR A.1 st₀).x.reset = 0#32 ∧ u8 A.1.uev 6 ≠ st₀.h.lb
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) (dhR A.1 st₀)))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35a3`. -/
def T_L35a3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (Fix A t₀ ∧ Fr A t₀ s
      ∧ s.regs.get64 .r13 = sA A.1.c
      ∧ ∃ st₀ y, Inv A st₀ ∧ S1 t₀ st₀ ∧ (dhR A.1 st₀).x.reset = 0#32 ∧ u8 A.1.uev 6 ≠ st₀.h.lb
        ∧ Tablelim (u8 A.1.uev 6) (dhR A.1 st₀).x y ∧ DecExt.Lens y
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
            { dhR A.1 st₀ with x := y }))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35a5`. -/
def T_L35a5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (S1 t₀))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35b5`. -/
def T_L35b5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (fun st =>
      HI ({ st.x with start := 1#32 }, st.h) ∧ st.x.idAac = idv t₀ ∧ st.u = 1#32 ∧ SpW st))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35bf`. -/
def T_L35bf (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (SH t₀))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35d7`. -/
def T_L35d7 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (SH t₀))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35ea`. -/
def T_L35ea (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (fun st => SH t₀ st
      ∧ st.x.reset ≠ 0#32))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L35f5`. -/
def T_L35f5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  (AtI k A ra t₀ s (SM t₀))
  ∧ (s.regs.get64 .r15).setWidth 32 = chv t₀

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3609`. -/
def T_L3609 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s (SM t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3621`. -/
def T_L3621 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (fun st => SM t₀ st
      ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → Live st.x.d0)) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3630`. -/
def T_L3630 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3644`. -/
def T_L3644 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3652`. -/
def T_L3652 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3666`. -/
def T_L3666 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L366e`. -/
def T_L366e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3682`. -/
def T_L3682 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀) ∧ chv t₀ = 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L368a`. -/
def T_L368a (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s Fin

/-- The assertion at `ff_aac_sbr_decode_usac_data.L36c0`. -/
def T_L36c0 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s Fin

/-- The assertion at `ff_aac_sbr_decode_usac_data.L36c7`. -/
def T_L36c7 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s (SM t₀) ∧ chv t₀ ≠ 1#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L36fa`. -/
def T_L36fa (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SM t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3715`. -/
def T_L3715 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (fun st => SM t₀ st
      ∧ st.x.coupling = 1#32 ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → Live st.x.d0))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3724`. -/
def T_L3724 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (fun st => SE0 t₀ st
      ∧ st.x.coupling = 1#32)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3734`. -/
def T_L3734 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCp k A ra t₀ s (fun _ d1 => d1)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3750`. -/
def T_L3750 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCp k A ra t₀ s (fun _ d1 => cpA d1)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3763`. -/
def T_L3763 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCp k A ra t₀ s (fun _ d1 => cpA d1)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L377f`. -/
def T_L377f (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCq k A ra t₀ s cpB

/-- The assertion at `ff_aac_sbr_decode_usac_data.L379a`. -/
def T_L379a (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCq k A ra t₀ s cpC

/-- The assertion at `ff_aac_sbr_decode_usac_data.L37b3`. -/
def T_L37b3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCq k A ra t₀ s cpD

/-- The assertion at `ff_aac_sbr_decode_usac_data.L37cb`. -/
def T_L37cb (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtCq k A ra t₀ s cpE

/-- The assertion at `ff_aac_sbr_decode_usac_data.L37e3`. -/
def T_L37e3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L37fe` (`r13` holds `&data[0]`, not `sbr`). -/
def T_L37fe (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Fix A t₀ ∧ Fr A t₀ s
      ∧ s.regs.get64 .r13 = dAc A.1.c 0
      ∧ ∃ st, Inv A st ∧ SE01 t₀ st
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3819`. -/
def T_L3819 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Fix A t₀ ∧ Fr A t₀ s
      ∧ s.regs.get64 .r15 = dAc A.1.c 0
      ∧ ∃ st, Inv A st ∧ SE01 t₀ st
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀) st)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L382e`. -/
def T_L382e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀) ∧ True

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3847`. -/
def T_L3847 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (fun _ => True)
      ∧ ∃ st, Inv A st ∧ SE01 t₀ st
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocI (t₀.regs.get64 .rsp) (ivv t₀)) (Sv t₀)
            (st.wd1 (invfShift st.x.d1)))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3860`. -/
def T_L3860 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3874`. -/
def T_L3874 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L387c`. -/
def T_L387c (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3890`. -/
def T_L3890 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3898`. -/
def T_L3898 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L38b6`. -/
def T_L38b6 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s (SE01 t₀)
      ∧ s.regs.get64 .r15 = dAc A.1.c 1

/-- The assertion at `ff_aac_sbr_decode_usac_data.L38be`. -/
def T_L38be (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s (SE01 t₀)
      ∧ s.regs.get64 .r15 = dAc A.1.c 1

/-- The assertion at `ff_aac_sbr_decode_usac_data.L38d5`. -/
def T_L38d5 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L38dd`. -/
def T_L38dd (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s Fin

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3913`. -/
def T_L3913 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3933`. -/
def T_L3933 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SM t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L394e`. -/
def T_L394e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (fun st => SM t₀ st
      ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → Live st.x.d0))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L395d`. -/
def T_L395d (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE0 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3972`. -/
def T_L3972 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (fun st => SE0 t₀ st
      ∧ ((s.regs.get64 .rax).setWidth 32 = 0#32 → Live st.x.d1))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3981`. -/
def T_L3981 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3999`. -/
def T_L3999 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L39b8`. -/
def T_L39b8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L39c6`. -/
def T_L39c6 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L39d8`. -/
def T_L39d8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L39ec`. -/
def T_L39ec (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L39f4`. -/
def T_L39f4 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a0f`. -/
def T_L3a0f (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a17`. -/
def T_L3a17 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a2b`. -/
def T_L3a2b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a33`. -/
def T_L3a33 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a4e`. -/
def T_L3a4e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtD k A ra t₀ s (SE01 t₀)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a56`. -/
def T_L3a56 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtI k A ra t₀ s Fin

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3a8c`. -/
def T_L3a8c (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3aac`. -/
def T_L3aac (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtX k A ra t₀ s

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ab1`. -/
def T_L3ab1 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ad4`. -/
def T_L3ad4 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      s.regs.get64 .rsi = n1v st ∧ 2 ≤ st.x.n1) ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ae0`. -/
def T_L3ae0 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rdx) (s.regs.get64 .rdi) (s.regs.get64 .rsi))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3b17`. -/
def T_L3b17 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rdx) (s.regs.get64 .rdi) (s.regs.get64 .rsi))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3b61`. -/
def T_L3b61 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st => Lo st (s.regs.get64 .rdx))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3b98`. -/
def T_L3b98 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      s.regs.get64 .rdx = n1v st ∧ 2 ≤ st.x.n1)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ba2`. -/
def T_L3ba2 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rax) (s.regs.get64 .rsi) (s.regs.get64 .rdx))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3bd8`. -/
def T_L3bd8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rax) (s.regs.get64 .rsi) (s.regs.get64 .rdx))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3c1c`. -/
def T_L3c1c (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st => Lo st (s.regs.get64 .rax))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3c4b`. -/
def T_L3c4b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3c84`. -/
def T_L3c84 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3c9b`. -/
def T_L3c9b (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st => st.x.n1 = 1)
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ca2`. -/
def T_L3ca2 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      s.regs.get64 .rsi = n1v st ∧ 2 ≤ st.x.n1) ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3cac`. -/
def T_L3cac (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rdx) (s.regs.get64 .rdi) (s.regs.get64 .rsi))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ce3`. -/
def T_L3ce3 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rdx) (s.regs.get64 .rdi) (s.regs.get64 .rsi))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3d23`. -/
def T_L3d23 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      s.regs.get64 .rsi = n1v st ∧ s.regs.get64 .rdx = BitVec.ofNat 64 (st.x.n1 / 2 * 2))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3d2d`. -/
def T_L3d2d (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st => Lo st (s.regs.get64 .rdx))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3d64`. -/
def T_L3d64 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      s.regs.get64 .rdx = n1v st ∧ 2 ≤ st.x.n1)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3d6e`. -/
def T_L3d6e (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rax) (s.regs.get64 .rsi) (s.regs.get64 .rdx))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3da4`. -/
def T_L3da4 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rax) (s.regs.get64 .rsi) (s.regs.get64 .rdx))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3de8`. -/
def T_L3de8 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st => Lo st (s.regs.get64 .rax))

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3e17`. -/
def T_L3e17 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3e50`. -/
def T_L3e50 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun _ => True)
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3e75`. -/
def T_L3e75 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rdx) (s.regs.get64 .rdi) (s.regs.get64 .rsi))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3eac`. -/
def T_L3eac (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtH k A ra t₀ s (fun st =>
      Lp st (s.regs.get64 .rdx) (s.regs.get64 .rdi) (s.regs.get64 .rsi))
      ∧ (s.regs.get64 .rax).setWidth 32 = 0#32

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3ef1`. -/
def T_L3ef1 (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  AtX k A ra t₀ s

/-- The assertion at `ff_aac_sbr_decode_usac_data.done`. -/
def T_done (k : Nat) (A : UA) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Fix A t₀
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ ∃ st, UsacOut A st ((s.regs.get64 .rax).setWidth 32)
        ∧ (s.dmem =⋆ UM k A ra t₀ (LocR (t₀.regs.get64 .rsp)) (Bs (t₀.regs.get64 .rsp)) st)

/-- The assertion at `ff_aac_sbr_decode_usac_data.L3f00`. -/
def T_L3f00 (_k : Nat) (_A : UA) (_ra : Int64) (_t₀ _s : MachineData) : Prop :=
  False

def table (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "ff_aac_sbr_decode_usac_data", s => T_entry k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3361", s => T_L3361 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3388", s => T_L3388 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L33a3", s => T_L33a3 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L33ba", s => T_L33ba k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L33e6", s => T_L33e6 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3410", s => T_L3410 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L343d", s => T_L343d k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3475", s => T_L3475 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L34b0", s => T_L34b0 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L34dd", s => T_L34dd k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L34f7", s => T_L34f7 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L350f", s => T_L350f k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3523", s => T_L3523 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L353a", s => T_L353a k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L354e", s => T_L354e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3569", s => T_L3569 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L358e", s => T_L358e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L359b", s => T_L359b k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35a3", s => T_L35a3 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35a5", s => T_L35a5 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35b5", s => T_L35b5 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35bf", s => T_L35bf k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35d7", s => T_L35d7 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35ea", s => T_L35ea k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L35f5", s => T_L35f5 k A ra t₀ s
  -- the single channel element
  | "ff_aac_sbr_decode_usac_data.L3609", s => T_L3609 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3621", s => T_L3621 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3630", s => T_L3630 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3644", s => T_L3644 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3652", s => T_L3652 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3666", s => T_L3666 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L366e", s => T_L366e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3682", s => T_L3682 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L368a", s => T_L368a k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L36c0", s => T_L36c0 k A ra t₀ s
  -- the pair element
  | "ff_aac_sbr_decode_usac_data.L36c7", s => T_L36c7 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L36fa", s => T_L36fa k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3715", s => T_L3715 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3724", s => T_L3724 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3734", s => T_L3734 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3750", s => T_L3750 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3763", s => T_L3763 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L377f", s => T_L377f k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L379a", s => T_L379a k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L37b3", s => T_L37b3 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L37cb", s => T_L37cb k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L37e3", s => T_L37e3 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L37fe", s => T_L37fe k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3819", s => T_L3819 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L382e", s => T_L382e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3847", s => T_L3847 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3860", s => T_L3860 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3874", s => T_L3874 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L387c", s => T_L387c k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3890", s => T_L3890 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3898", s => T_L3898 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L38b6", s => T_L38b6 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L38be", s => T_L38be k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L38d5", s => T_L38d5 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L38dd", s => T_L38dd k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3913", s => T_L3913 k A ra t₀ s
  -- the independent pair
  | "ff_aac_sbr_decode_usac_data.L3933", s => T_L3933 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L394e", s => T_L394e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L395d", s => T_L395d k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3972", s => T_L3972 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3981", s => T_L3981 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3999", s => T_L3999 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L39b8", s => T_L39b8 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L39c6", s => T_L39c6 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L39d8", s => T_L39d8 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L39ec", s => T_L39ec k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L39f4", s => T_L39f4 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a0f", s => T_L3a0f k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a17", s => T_L3a17 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a2b", s => T_L3a2b k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a33", s => T_L3a33 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a4e", s => T_L3a4e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a56", s => T_L3a56 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3a8c", s => T_L3a8c k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3aac", s => T_L3aac k A ra t₀ s
  -- the harmonic flags and bits
  | "ff_aac_sbr_decode_usac_data.L3ab1", s => T_L3ab1 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3ad4", s => T_L3ad4 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3ae0", s => T_L3ae0 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3b17", s => T_L3b17 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3b61", s => T_L3b61 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3b98", s => T_L3b98 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3ba2", s => T_L3ba2 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3bd8", s => T_L3bd8 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3c1c", s => T_L3c1c k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3c4b", s => T_L3c4b k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3c84", s => T_L3c84 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3c9b", s => T_L3c9b k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3ca2", s => T_L3ca2 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3cac", s => T_L3cac k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3ce3", s => T_L3ce3 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3d23", s => T_L3d23 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3d2d", s => T_L3d2d k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3d64", s => T_L3d64 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3d6e", s => T_L3d6e k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3da4", s => T_L3da4 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3de8", s => T_L3de8 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3e17", s => T_L3e17 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3e50", s => T_L3e50 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3e75", s => T_L3e75 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3eac", s => T_L3eac k A ra t₀ s
  -- the return
  | "ff_aac_sbr_decode_usac_data.L3ef1", s => T_L3ef1 k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.done", s => T_done k A ra t₀ s
  | "ff_aac_sbr_decode_usac_data.L3f00", s => T_L3f00 k A ra t₀ s
  | _, _ => False

/-- The variant: a rank per label (non-increasing along every edge, equal only on forward
edges), plus the distance to the bound in the five harmonic loops; the labels before the
harmonic bits (all their edges forward) share the top rank. The ranks are `r * 2 ^ 65`
(`r ≤ 10`, the top `2 ^ 70`) written as literals: with `2 * 2 ^ 65` the `rfl` unfolding of a
label's rank ran out of memory. -/
def var : Label → MachineData → Nat
  | "ff_aac_sbr_decode_usac_data.L36c0", _ => 73786976294838206464
  | "ff_aac_sbr_decode_usac_data.L3ab1", _ => 184467440737095516160
  | "ff_aac_sbr_decode_usac_data.L3ad4", _ => 147573952589676412928
  | "ff_aac_sbr_decode_usac_data.L3ae0", s =>
      110680464442257309696 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat
  | "ff_aac_sbr_decode_usac_data.L3b17", s =>
      110680464442257309696 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat
  | "ff_aac_sbr_decode_usac_data.L3b61", _ => 73786976294838206464
  | "ff_aac_sbr_decode_usac_data.L3b98", _ => 368934881474191032320
  | "ff_aac_sbr_decode_usac_data.L3ba2", s =>
      332041393326771929088 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat
  | "ff_aac_sbr_decode_usac_data.L3bd8", s =>
      332041393326771929088 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat
  | "ff_aac_sbr_decode_usac_data.L3c1c", _ => 295147905179352825856
  | "ff_aac_sbr_decode_usac_data.L3c4b", _ => 258254417031933722624
  | "ff_aac_sbr_decode_usac_data.L3c84", _ => 221360928884514619392
  | "ff_aac_sbr_decode_usac_data.L3c9b", _ => 110680464442257309696
  | "ff_aac_sbr_decode_usac_data.L3ca2", _ => 184467440737095516160
  | "ff_aac_sbr_decode_usac_data.L3cac", s =>
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat
  | "ff_aac_sbr_decode_usac_data.L3ce3", s =>
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat
  | "ff_aac_sbr_decode_usac_data.L3d23", _ => 110680464442257309696
  | "ff_aac_sbr_decode_usac_data.L3d2d", _ => 73786976294838206464
  | "ff_aac_sbr_decode_usac_data.L3d64", _ => 332041393326771929088
  | "ff_aac_sbr_decode_usac_data.L3d6e", s =>
      295147905179352825856 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat
  | "ff_aac_sbr_decode_usac_data.L3da4", s =>
      295147905179352825856 + (s.regs.get64 .rsi - s.regs.get64 .rax).toNat
  | "ff_aac_sbr_decode_usac_data.L3de8", _ => 258254417031933722624
  | "ff_aac_sbr_decode_usac_data.L3e17", _ => 221360928884514619392
  | "ff_aac_sbr_decode_usac_data.L3e50", _ => 184467440737095516160
  | "ff_aac_sbr_decode_usac_data.L3e75", s =>
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat
  | "ff_aac_sbr_decode_usac_data.L3eac", s =>
      147573952589676412928 + (s.regs.get64 .rdi - s.regs.get64 .rdx).toNat
  | "ff_aac_sbr_decode_usac_data.L3ef1", _ => 36893488147419103232
  | "ff_aac_sbr_decode_usac_data.done", _ => 0
  | "ff_aac_sbr_decode_usac_data.L3f00", _ => 0
  | _, _ => 1180591620717411303424

/-- What a return leaves, the frame given back as raw slots. -/
abbrev Post' (k : Nat) (A : UA) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  ∃ st, UsacOut A st ((s.regs.get64 .rax).setWidth 32)
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 8 ?@ (r - 0x50#64) ⋆ (Reserve (cneed k) (r - 0x50#64) ⋆ (UF A.1 st
        ⋆ (LocR r ⋆ (Bs r ⋆ (8 ?@ r ⋆ A.1.R))))))

abbrev BlockOb (k : Nat) (A : UA) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k A ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k A ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k A ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ ((a = ra ∧ Post' k A ra t₀ s) ∨ (a = abortA ∨ a = entry "read_sbr_envelope.L60f9")) ⦄

end Kraken.Examples.Sbr.Usac
