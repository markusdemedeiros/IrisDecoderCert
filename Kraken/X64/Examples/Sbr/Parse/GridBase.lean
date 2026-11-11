import Kraken.X64.Examples.Sbr.Parse.GridFoot

/-!
# `read_sbr_grid`: the block table

The assertions at the labels of `body`, over the footprint `T` of `GridFoot.lean`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

macro "grind_cells0" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

/-- The invariant of the values between the parse steps: the `DWF` clauses, the border
invariant, the reader's bound. -/
def SInv (x : GArgs) (st : GSt) : Prop :=
  DWF False (st.dv x) ∧ u8 st.te st.n.toNat ≤ 19 ∧ st.i.toNat ≤ x.p8.toNat

/-- `SInv` without the reader's index (kept in a register at some labels). -/
def SInvD (x : GArgs) (st : GSt) : Prop :=
  DWF False (st.dv x) ∧ u8 st.te st.n.toNat ≤ 19

/-- Inside a class body, after `bs_num_env` is written and before `bs_freq_res` is: the `DWF`
clauses that do not mention `bs_freq_res[1..bs_num_env]`, the reader's bound, and
`bs_freq_res[0] ≤ 1` (written before the dispatch, never in a body). -/
def SInvF (x : GArgs) (st : GSt) : Prop :=
  st.fr.length = 9 ∧ st.te.length = 10 ∧ st.tq.length = 3 ∧ st.n.toNat ≤ 8
  ∧ st.nn.toNat ≤ 2 ∧ u8 st.te 9 ≤ 19 ∧ (∀ q, q ≤ st.nn.toNat → u8 st.tq q ≤ 19)
  ∧ st.i.toNat ≤ x.p8.toNat ∧ u8 st.fr 0 ≤ 1

/-- After `bs_freq_res[0] = bs_freq_res[bs_num_env]`. -/
def st1a (x : GArgs) : GSt :=
  { x.st with fr := x.v.freqRes.set 0 (x.v.freqRes.getD x.v.nenv 0) }

/-- After `t_env_num_env_old = t_env[bs_num_env]` too. -/
def st1 (x : GArgs) : GSt :=
  { st1a x with te := x.v.te.set 9 (x.v.te.getD x.v.nenv 0) }

/-- The registers kept after the prologue. -/
abbrev Regs0 (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x28#64 ∧ s.regs.get64 .rbp = r - 8#64
    ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13
    ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀

abbrev Regs (t₀ s : MachineData) : Prop :=
  Regs0 t₀ s ∧ s.regs.get64 .rbx = arg3 t₀

/-- At the four frame classes (after the dispatch), `c` the class. -/
abbrev Cls (c : Nat) (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64)
    (t₀ s : MachineData) : Prop :=
  GridC x ∧ Regs t₀ s ∧ s.regs.get64 .rax = x.buf
  ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r15 = BitVec.ofNat 64 c
  ∧ (s.regs.get64 .r9).toNat ≤ x.p8.toNat
  ∧ ∃ st, SInvD x st
    ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) (st.withI ((s.regs.get64 .r9).setWidth 32)))

/-- On the error paths (to the return of `-1`): the stack pointer and an invariant state. -/
abbrev ErrS (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  GridC x ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
  ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13
  ∧ ∃ st, SInv x st ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)

/-- The registers every body keeps: the frame, `r13` (callee-saved, never written), `ch_data`. -/
abbrev RB (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x28#64 ∧ s.regs.get64 .rbp = r - 8#64
    ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13 ∧ s.regs.get64 .rbx = arg3 t₀

/-- The memory at a label: the footprint at the values `st`. -/
abbrev At (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ s : MachineData)
    (st : GSt) : Prop :=
  s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st

/-- Inside a class body: `RB`, `ac` and `gb` in their argument registers, a state with `P`. -/
abbrev Bd (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ s : MachineData)
    (P : GSt → Prop) : Prop :=
  GridC x ∧ RB t₀ s ∧ s.regs.get64 .rdx = arg2 t₀ ∧ s.regs.get64 .rdi = arg0 t₀
  ∧ ∃ st, P st ∧ At k Ext x ra t₀ s st

/-- After the bodies (`gb` no longer used). -/
abbrev Tl (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ s : MachineData)
    (P : GSt → Prop) : Prop :=
  GridC x ∧ RB t₀ s ∧ ∃ st, P st ∧ At k Ext x ra t₀ s st

/-- `bs_freq_res[0..j]` are flags. -/
def FrOk (st : GSt) (j : Nat) : Prop := ∀ e, e ≤ j → u8 st.fr e ≤ 1

/-- `bs_freq_res[n-j+1..n]` are flags (the FIXVAR fill runs from the top). -/
def FrTop (st : GSt) (j : Nat) : Prop :=
  ∀ e, st.n.toNat - j < e → e ≤ st.n.toNat → u8 st.fr e ≤ 1

/-- `t_env[0..j]` strictly increasing. -/
def Mono (st : GSt) (j : Nat) : Prop := ∀ e, e < j → u8 st.te e < u8 st.te (e + 1)

/-- A live grid: what the border check establishes. -/
def Live (st : GSt) : Prop :=
  1 ≤ st.n.toNat ∧ (∀ e, e ≤ st.n.toNat → u8 st.te e ≤ 19) ∧ Mono st st.n.toNat

/-- In a body after `bs_num_env` and `t_env[bs_num_env]` are written, before the
`bs_freq_res` fill. -/
def FrPre (x : GArgs) (st : GSt) : Prop :=
  SInvF x st ∧ 1 ≤ st.n.toNat ∧ u8 st.te st.n.toNat ≤ 19

/-- A complete `bs_freq_res` fill: the body invariant. -/
theorem frPre_sinv {x : GArgs} {st : GSt} (hC : GridC x) (hP : FrPre x st)
    (hF : FrOk st st.n.toNat) : SInv x st := by
  obtain ⟨⟨-, hil, -, -, -, -, -, hinv, hy, -, -, hidx1, hidx2, hv1, hv2, -⟩, -⟩ := hC
  obtain ⟨⟨hfl, htl, hql, hn, hnn, hte9, htq, hi, -⟩, -, hten⟩ := hP
  exact ⟨⟨hfl, hil, htl, hql, hn, hF, hnn, hinv, hy, hte9, htq, hidx1, hidx2, hv1, hv2,
    fun h => h.elim⟩, hten, hi⟩

/-- The paired `get_bits1` loop of the `bs_freq_res` fill (VARFIX, VARVAR): `rax` the even
counter, `r9 = n & ~1`, `rsi = n`, and `bs_freq_res[0..rax+j]` done. -/
def FrLoop (x : GArgs) (st : GSt) (rax r9 rsi : BitVec 64) (j : Nat) : Prop :=
  FrPre x st ∧ 2 ≤ st.n.toNat ∧ rsi = st.n.setWidth 64 ∧ r9.toNat = st.n.toNat / 2 * 2
  ∧ rax.toNat % 2 = 0 ∧ rax.toNat < r9.toNat ∧ FrOk st (rax.toNat + j)

/-- The `t_env` fill from the top (FIXVAR, VARVAR): `v = bs_num_rel` steps, step `j`,
`eax = -v`, `esi = -j`; `Q v j` the registers of the label. -/
def RelL (x : GArgs) (st : GSt) (eax esi : BitVec 32) (Q : Nat → Nat → Prop) : Prop :=
  FrPre x st ∧ ∃ v j, 1 ≤ v ∧ v < 4 ∧ j < v ∧ v + 1 ≤ st.n.toNat
    ∧ eax = 0#32 - BitVec.ofNat 32 v ∧ esi = 0#32 - BitVec.ofNat 32 j ∧ Q v j

/-- The FIXVAR `bs_freq_res` fill from the top: step `j`, `esi = j`, `eax = -j`. -/
def FrD (x : GArgs) (st : GSt) (esi eax : BitVec 32) (Q : Nat → Prop) : Prop :=
  FrPre x st ∧ ∃ j, j < st.n.toNat ∧ esi = BitVec.ofNat 32 j ∧ eax = 0#32 - BitVec.ofNat 32 j
    ∧ FrTop st j ∧ Q j

/-- The FIXFIX `t_env` chain at step `j` (`t_env[e] = e * 16 / n` for `e < j`): `n ∈ {2,4,8}`
in `r8`, `r9 = n - 1`, `rsi = 16 / n`. -/
def FX (x : GArgs) (st : GSt) (r8 r9 rsi : BitVec 64) (j : Nat) : Prop :=
  SInvF x st ∧ (st.n.toNat = 2 ∨ st.n.toNat = 4 ∨ st.n.toNat = 8) ∧ j ≤ st.n.toNat
  ∧ r8 = st.n.setWidth 64 ∧ r9 = (st.n - 1#32).setWidth 64 ∧ rsi.toNat = 16 / st.n.toNat
  ∧ u8 st.te 0 = 0 ∧ u8 st.te st.n.toNat = 16
  ∧ ∀ e, 1 ≤ e → e < j → u8 st.te e = e * (16 / st.n.toNat)

/-- The border check of the tail: `ecx = n`, `eax = n + 1`, `r8d = bs_pointer ≤ n + 1` (only the
low 32 bits of `r8` are read). -/
abbrev TR (s : MachineData) (st : GSt) : Prop :=
  s.regs.get64 .rcx = st.n.setWidth 64 ∧ s.regs.get64 .rax = (st.n + 1#32).setWidth 64
  ∧ ((s.regs.get64 .r8).setWidth 32).toNat ≤ st.n.toNat + 1

/-- The chain of `t_env[j-1] < t_env[j]` checks at step `j`: `t_env[j]` in `r`, `t_env[0]` in
`rdx`. -/
abbrev Chk (x : GArgs) (s : MachineData) (st : GSt) (j : Nat) (r : Reg64) : Prop :=
  SInv x st ∧ j + 1 ≤ st.n.toNat ∧ Mono st j ∧ TR s st
  ∧ s.regs.get64 .rdx = (bv st.te 0).setWidth 64 ∧ s.regs.get64 r = (bv st.te j).setWidth 64

/-- The tail after the border check: `DWF` with `bs_num_noise`/`t_q` not yet written (only
`t_q[0]` read by it), the live grid, the reader's bound. -/
def TInv (x : GArgs) (st : GSt) : Prop :=
  DWF False { st.dv x with nnoise := 0 } ∧ Live st ∧ st.i.toNat ≤ x.p8.toNat

/-- `bs_num_noise = 2` with `t_q[0]`, `t_q[2]` written. -/
abbrev TQ2 (x : GArgs) (st : GSt) : Prop :=
  TInv x st ∧ st.nn = 2#32 ∧ u8 st.tq 2 ≤ 19 ∧ 2 ≤ st.n.toNat

/-- The table by label key (`labKey`, `lkey`): a lookup reduces the label once. -/
abbrev tableK (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    Nat → MachineData → Prop
  | lkey "read_sbr_grid", s => s = t₀ ∧ GridC x
      ∧ (t₀.dmem =⋆ T k Ext x ra t₀ (BlankS (t₀.regs.get64 .rsp)) x.st)
  | lkey "read_sbr_grid.L440b", s => GridC x ∧ Regs0 t₀ s ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) x.st)
  | lkey "read_sbr_grid.L4419", s => GridC x ∧ Regs0 t₀ s ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ s.regs.get64 .r14 = BitVec.ofNat 64 x.v.nenv
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) x.st)
  | lkey "read_sbr_grid.L4422", s => GridC x ∧ Regs t₀ s ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ s.regs.get64 .r14 = BitVec.ofNat 64 x.v.nenv
      ∧ s.regs.get64 .rax = (bv x.v.freqRes x.v.nenv).setWidth 64
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) x.st)
  | lkey "read_sbr_grid.L442b", s => GridC x ∧ Regs t₀ s ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ s.regs.get64 .r14 = BitVec.ofNat 64 x.v.nenv
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) (st1a x))
  | lkey "read_sbr_grid.L4434", s => GridC x ∧ Regs t₀ s ∧ s.regs.get64 .rcx = arg3 t₀
      ∧ s.regs.get64 .rax = (bv x.v.te x.v.nenv).setWidth 64
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) (st1a x))
  | lkey "read_sbr_grid.L443a", s => GridC x ∧ Regs t₀ s
      ∧ ∃ st, SInv x st ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)
  | lkey "read_sbr_grid.L4478", s => GridC x ∧ Regs t₀ s ∧ s.regs.get64 .rax = x.buf
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ (s.regs.get64 .r15).toNat < 4
      ∧ (s.regs.get64 .r9).toNat ≤ x.p8.toNat
      ∧ ∃ st, SInvD x st
        ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) (st.withI ((s.regs.get64 .r9).setWidth 32)))
  | lkey "read_sbr_grid.L448b", s => Cls 0 k Ext x ra t₀ s
  | lkey "read_sbr_grid.L4773", s => Cls 1 k Ext x ra t₀ s
  | lkey "read_sbr_grid.L44e3", s => Cls 2 k Ext x ra t₀ s
  | lkey "read_sbr_grid.L46a2", s => Cls 3 k Ext x ra t₀ s
  -- VARFIX (class 2)
  | lkey "read_sbr_grid.L450e", s => Bd k Ext x ra t₀ s (SInv x)
  | lkey "read_sbr_grid.L4539", s => Bd k Ext x ra t₀ s fun st => SInv x st
      ∧ (s.regs.get64 .rax).toNat < 4
  | lkey "read_sbr_grid.L4548", s => Bd k Ext x ra t₀ s fun st => SInvF x st
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 1
      ∧ s.regs.get64 .rcx = s.regs.get64 .rax + 1#64
  | lkey "read_sbr_grid.L4556", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 1 ≤ (s.regs.get64 .rax).toNat ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 1
  | lkey "read_sbr_grid.L4570", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 1 ≤ (s.regs.get64 .rax).toNat ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 1
      ∧ (s.regs.get64 .r8).toNat < (s.regs.get64 .rax).toNat
  | lkey "read_sbr_grid.L45a5", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 1 ≤ (s.regs.get64 .rax).toNat ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 1
      ∧ (s.regs.get64 .r8).toNat < (s.regs.get64 .rax).toNat
  | lkey "read_sbr_grid.L45bf", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 2 ≤ st.n.toNat ∧ st.n.toNat ≤ 4
  | lkey "read_sbr_grid.L45cb", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ st.n.toNat ≤ 4 ∧ s.regs.get64 .rcx = st.n.setWidth 64
  | lkey "read_sbr_grid.L45d8", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 4
  | lkey "read_sbr_grid.L460b", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 4
  | lkey "read_sbr_grid.L4621", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 2 ≤ st.n.toNat ∧ s.regs.get64 .rsi = st.n.setWidth 64
  | lkey "read_sbr_grid.L4630", s => Bd k Ext x ra t₀ s fun st =>
      FrLoop x st (s.regs.get64 .rax) (s.regs.get64 .r9) (s.regs.get64 .rsi) 0
  | lkey "read_sbr_grid.L4662", s => Bd k Ext x ra t₀ s fun st =>
      FrLoop x st (s.regs.get64 .rax) (s.regs.get64 .r9) (s.regs.get64 .rsi) 1
  | lkey "read_sbr_grid.L4694", s => Bd k Ext x ra t₀ s fun st =>
      FrLoop x st (s.regs.get64 .rax) (s.regs.get64 .r9) (s.regs.get64 .rsi) 2
  -- VARVAR (class 3)
  | lkey "read_sbr_grid.L46cd", s => Bd k Ext x ra t₀ s (SInv x)
  | lkey "read_sbr_grid.L4701", s => GridC x ∧ RB t₀ s ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rax = x.buf
      ∧ s.regs.get64 .r10 = x.p8.setWidth 64 ∧ (s.regs.get64 .r9).toNat ≤ x.p8.toNat
      ∧ (s.regs.get64 .r8).toNat < 4
      ∧ ∃ st, SInvD x st ∧ At k Ext x ra t₀ s (st.withI ((s.regs.get64 .r9).setWidth 32))
  | lkey "read_sbr_grid.L4726", s => GridC x ∧ RB t₀ s ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rax = x.buf
      ∧ s.regs.get64 .r10 = x.p8.setWidth 64 ∧ (s.regs.get64 .r9).toNat ≤ x.p8.toNat
      ∧ (s.regs.get64 .r8).toNat < 4 ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ ∃ st, SInvD x st ∧ At k Ext x ra t₀ s (st.withI ((s.regs.get64 .r9).setWidth 32))
  | lkey "read_sbr_grid.L474b", s => Bd k Ext x ra t₀ s fun st => SInv x st
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ (s.regs.get64 .r8).toNat < 4
  | lkey "read_sbr_grid.L4925", s => Bd k Ext x ra t₀ s fun st => SInv x st
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ (s.regs.get64 .r8).toNat < 4
      ∧ (s.regs.get64 .rax).toNat + (s.regs.get64 .rsi).toNat ≤ 4
      ∧ s.regs.get64 .rcx = s.regs.get64 .rax + s.regs.get64 .rsi + 1#64
  | lkey "read_sbr_grid.L4948", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ 1 ≤ (s.regs.get64 .rsi).toNat ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rsi).toNat + 1
  | lkey "read_sbr_grid.L4979", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ 1 ≤ (s.regs.get64 .rsi).toNat ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rsi).toNat + 1
      ∧ (s.regs.get64 .r9).toNat ≤ x.p8.toNat
  | lkey "read_sbr_grid.L499b", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ 2 ≤ (s.regs.get64 .rsi).toNat ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rsi).toNat + 1
  | lkey "read_sbr_grid.L49cf", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ 2 ≤ (s.regs.get64 .rsi).toNat ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + (s.regs.get64 .rsi).toNat + 1
  | lkey "read_sbr_grid.L49e9", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ (s.regs.get64 .rsi).toNat = 3 ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 4
  | lkey "read_sbr_grid.L4a1d", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ (s.regs.get64 .rsi).toNat = 3 ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 4
  | lkey "read_sbr_grid.L4bb9", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ (s.regs.get64 .rax).toNat + 1 ≤ st.n.toNat
  | lkey "read_sbr_grid.L4bbc", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ (s.regs.get64 .rax).toNat + 1 ≤ st.n.toNat
      ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4bd0", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ _ => st.n.toNat ≤ 5 ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4bdb", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ j => st.n.toNat ≤ 5
          ∧ (s.regs.get64 .rcx).setWidth 32 = BitVec.ofNat 32 (st.n.toNat - j)
  | lkey "read_sbr_grid.L4be6", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ _ => st.n.toNat ≤ 5
  | lkey "read_sbr_grid.L4c1b", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ _ => st.n.toNat ≤ 5
  | lkey "read_sbr_grid.L4c2f", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ j => st.n.toNat ≤ 5
          ∧ (s.regs.get64 .r10).setWidth 32 = BitVec.ofNat 32 (st.n.toNat - 1 - j)
          ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4c4a", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ st.n.toNat ≤ 5 ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4c53", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ st.n.toNat ≤ 5 ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4c5c", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ st.n.toNat ≤ 5 ∧ s.regs.get64 .rax = st.n.setWidth 64
      ∧ s.regs.get64 .rcx = lab "ceil_log2"
  | lkey "read_sbr_grid.L4c93", s => Bd k Ext x ra t₀ s (FrPre x)
  | lkey "read_sbr_grid.L4ca9", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n = 1#32
  | lkey "read_sbr_grid.L4df1", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 2 ≤ st.n.toNat ∧ s.regs.get64 .rsi = st.n.setWidth 64
  | lkey "read_sbr_grid.L4e00", s => Bd k Ext x ra t₀ s fun st =>
      FrLoop x st (s.regs.get64 .rax) (s.regs.get64 .r9) (s.regs.get64 .rsi) 0
  | lkey "read_sbr_grid.L4e32", s => Bd k Ext x ra t₀ s fun st =>
      FrLoop x st (s.regs.get64 .rax) (s.regs.get64 .r9) (s.regs.get64 .rsi) 1
  | lkey "read_sbr_grid.L4e64", s => Bd k Ext x ra t₀ s fun st =>
      FrLoop x st (s.regs.get64 .rax) (s.regs.get64 .r9) (s.regs.get64 .rsi) 2
  | lkey "read_sbr_grid.L4e6d", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ s.regs.get64 .rsi = st.n.setWidth 64
      ∧ (s.regs.get64 .rax).toNat = st.n.toNat / 2 * 2 ∧ FrOk st (s.regs.get64 .rax).toNat
  | lkey "read_sbr_grid.L4e73", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ (s.regs.get64 .rax).toNat + 1 = st.n.toNat ∧ FrOk st (s.regs.get64 .rax).toNat
  -- FIXVAR (class 1)
  | lkey "read_sbr_grid.L4798", s => GridC x ∧ RB t₀ s ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rax = x.buf
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ (s.regs.get64 .r9).toNat ≤ x.p8.toNat
      ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ ∃ st, SInvD x st ∧ At k Ext x ra t₀ s (st.withI ((s.regs.get64 .r9).setWidth 32))
  | lkey "read_sbr_grid.L47bd", s => Bd k Ext x ra t₀ s fun st => SInv x st
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ (s.regs.get64 .rsi).toNat < 4
  | lkey "read_sbr_grid.L47d3", s => Bd k Ext x ra t₀ s fun st => SInvF x st
      ∧ (s.regs.get64 .rax).toNat < 4 ∧ (s.regs.get64 .rsi).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 1
      ∧ s.regs.get64 .rcx = s.regs.get64 .rax + 1#64
  | lkey "read_sbr_grid.L47ea", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ 1 ≤ (s.regs.get64 .rax).toNat ∧ (s.regs.get64 .rax).toNat < 4
      ∧ st.n.toNat = (s.regs.get64 .rax).toNat + 1 ∧ s.regs.get64 .rcx = st.n.setWidth 64
  | lkey "read_sbr_grid.L47f0", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ _ => st.n.toNat ≤ 5 ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L47fb", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ j => st.n.toNat ≤ 5
          ∧ (s.regs.get64 .rcx).setWidth 32 = BitVec.ofNat 32 (st.n.toNat - j)
  | lkey "read_sbr_grid.L4806", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ _ => st.n.toNat ≤ 5
  | lkey "read_sbr_grid.L483b", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ _ => st.n.toNat ≤ 5
  | lkey "read_sbr_grid.L484f", s => Bd k Ext x ra t₀ s fun st =>
      RelL x st ((s.regs.get64 .rax).setWidth 32) ((s.regs.get64 .rsi).setWidth 32)
        fun _ j => st.n.toNat ≤ 5
          ∧ (s.regs.get64 .r10).setWidth 32 = BitVec.ofNat 32 (st.n.toNat - 1 - j)
          ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L486a", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ st.n.toNat ≤ 5 ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4873", s => Bd k Ext x ra t₀ s fun st => FrPre x st
      ∧ st.n.toNat ≤ 5 ∧ (s.regs.get64 .rcx).setWidth 32 = st.n
  | lkey "read_sbr_grid.L4880", s => Bd k Ext x ra t₀ s fun st => FrPre x st ∧ st.n.toNat ≤ 5
  | lkey "read_sbr_grid.L48b3", s => Bd k Ext x ra t₀ s (FrPre x)
  | lkey "read_sbr_grid.L48d0", s => Bd k Ext x ra t₀ s fun st =>
      FrD x st ((s.regs.get64 .rsi).setWidth 32) ((s.regs.get64 .rax).setWidth 32) fun _ => True
  | lkey "read_sbr_grid.L48f3", s => Bd k Ext x ra t₀ s fun st =>
      FrD x st ((s.regs.get64 .rsi).setWidth 32) ((s.regs.get64 .rax).setWidth 32) fun _ => True
  | lkey "read_sbr_grid.L4905", s => Bd k Ext x ra t₀ s fun st =>
      FrD x st ((s.regs.get64 .rsi).setWidth 32) ((s.regs.get64 .rax).setWidth 32) fun j =>
        (s.regs.get64 .r11).setWidth 32 = BitVec.ofNat 32 (st.n.toNat - j)
        ∧ (s.regs.get64 .r10).setWidth 32 = st.n
  -- FIXFIX (class 0)
  | lkey "read_sbr_grid.L4cb0", s => GridC x ∧ Regs t₀ s
      ∧ (s.regs.get64 .rax).toNat < 4
      ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (2 ^ (s.regs.get64 .rax).toNat)
      ∧ 2 ^ (s.regs.get64 .rax).toNat ≤ (if x.usac = 0#32 then 5 else 8)
      ∧ ∃ st, SInv x st ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)
  | lkey "read_sbr_grid.L4cc9", s => GridC x ∧ Regs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ s.regs.get64 .r8 = 1#64
      ∧ ∃ st, SInvF x st ∧ st.n = 1#32 ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)
  | lkey "read_sbr_grid.L4cd7", s => GridC x ∧ Regs t₀ s
      ∧ (s.regs.get64 .rax).toNat < 4
      ∧ s.regs.get64 .r8 = BitVec.ofNat 64 (2 ^ (s.regs.get64 .rax).toNat)
      ∧ 2 ^ (s.regs.get64 .rax).toNat ≤ (if x.usac = 0#32 then 5 else 8)
      ∧ ∃ st, SInvF x st ∧ st.n = BitVec.ofNat 32 (2 ^ (s.regs.get64 .rax).toNat)
        ∧ u8 st.te 0 = 0 ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)
  | lkey "read_sbr_grid.L4cfb", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 1
  | lkey "read_sbr_grid.L4d08", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 1
  | lkey "read_sbr_grid.L4d15", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 2 ∧ 4 ≤ st.n.toNat
  | lkey "read_sbr_grid.L4d24", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 3 ∧ 4 ≤ st.n.toNat
  | lkey "read_sbr_grid.L4d37", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 4 ∧ st.n.toNat = 8
      ∧ (s.regs.get64 .rax).toNat = 2
  | lkey "read_sbr_grid.L4d4a", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 5 ∧ st.n.toNat = 8
      ∧ (s.regs.get64 .rax).toNat = 2
  | lkey "read_sbr_grid.L4d59", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 6 ∧ st.n.toNat = 8
      ∧ (s.regs.get64 .rax).toNat = 2
  | lkey "read_sbr_grid.L4d6b", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 7 ∧ st.n.toNat = 8
      ∧ (s.regs.get64 .rax).toNat = 2
  | lkey "read_sbr_grid.L4d80", s => Bd k Ext x ra t₀ s fun st =>
      FX x st (s.regs.get64 .r8) (s.regs.get64 .r9) (s.regs.get64 .rsi) 8 ∧ st.n.toNat = 8
      ∧ (s.regs.get64 .rax).toNat = 2
  | lkey "read_sbr_grid.L4d8b", s => Bd k Ext x ra t₀ s fun st => SInvF x st ∧ 1 ≤ st.n.toNat
      ∧ (∀ e, e ≤ st.n.toNat → u8 st.te e ≤ 19)
      ∧ (∀ e, e < st.n.toNat → u8 st.te e < u8 st.te (e + 1))
  | lkey "read_sbr_grid.L4db6", s => Tl k Ext x ra t₀ s (fun st => SInvF x st ∧ Live st
        ∧ u8 st.fr 1 ≤ 1)
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ ((s.regs.get64 .rax).setWidth 8).toNat ≤ 1
  | lkey "read_sbr_grid.L4dbf", s => Tl k Ext x ra t₀ s (fun st => SInvF x st ∧ Live st
        ∧ u8 st.fr 1 ≤ 1 ∧ 2 ≤ st.n.toNat ∧ s.regs.get64 .rdx = st.n.setWidth 64)
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ ((s.regs.get64 .rax).setWidth 8).toNat ≤ 1
  | lkey "read_sbr_grid.L4dcb", s => Tl k Ext x ra t₀ s (fun st => SInvF x st ∧ Live st
        ∧ u8 st.fr 1 ≤ 1 ∧ 2 ≤ st.n.toNat ∧ s.regs.get64 .rdx = st.n.setWidth 64)
      ∧ s.regs.get64 .rdi = arg0 t₀ ∧ ((s.regs.get64 .rax).setWidth 8).toNat ≤ 1
  | lkey "read_sbr_grid.L4ddd", s => Tl k Ext x ra t₀ s (fun st => SInv x st ∧ Live st)
      ∧ s.regs.get64 .r12 = arg0 t₀
  | lkey "read_sbr_grid.L4de0", s => Tl k Ext x ra t₀ s (fun st => SInv x st ∧ Live st)
      ∧ s.regs.get64 .rdi = arg0 t₀
  -- the tail: the border check, `bs_num_noise`, `t_q`, `e_a`
  | lkey "read_sbr_grid.L4ea2", s => Tl k Ext x ra t₀ s (fun st => SInv x st ∧ 1 ≤ st.n.toNat)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L50e8", s => ErrS k Ext x ra t₀ s
  | lkey "read_sbr_grid.L510e", s => GridC x ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ ∃ st, At k Ext x ra t₀ s st
  | lkey "read_sbr_grid.L4ed8", s => Tl k Ext x ra t₀ s (fun st => SInv x st ∧ 1 ≤ st.n.toNat
        ∧ TR s st)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L4fd3", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 1 .rsi)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L4fed", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 2 .r9)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L5002", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 3 .rsi)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L5018", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 4 .r9)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L502d", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 5 .rsi)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L5043", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 6 .r9)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L5058", s => Tl k Ext x ra t₀ s (fun st => Chk x s st 7 .rsi)
      ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L4efc", s => Tl k Ext x ra t₀ s fun st => SInv x st ∧ Live st ∧ TR s st
      ∧ s.regs.get64 .rdx = (bv st.te 0).setWidth 64
  | lkey "read_sbr_grid.L4f11", s => Tl k Ext x ra t₀ s fun st => TInv x st ∧ TR s st
      ∧ st.nn = (if st.n = 1#32 then 1#32 else 2#32)
      ∧ s.regs.get64 .rsi = (if st.n = 1#32 then 0#64 else 1#64)
  | lkey "read_sbr_grid.L4f22", s => Tl k Ext x ra t₀ s fun st => TInv x st ∧ TR s st
      ∧ st.nn = (if st.n = 1#32 then 1#32 else 2#32) ∧ u8 st.tq st.nn.toNat ≤ 19
  | lkey "read_sbr_grid.L4f27", s => Tl k Ext x ra t₀ s fun st => TQ2 x st ∧ TR s st
  | lkey "read_sbr_grid.L5094", s => Tl k Ext x ra t₀ s fun st => TQ2 x st ∧ TR s st
  | lkey "read_sbr_grid.L509b", s => Tl k Ext x ra t₀ s fun st => TQ2 x st ∧ TR s st
  | lkey "read_sbr_grid.L50ae", s => Tl k Ext x ra t₀ s fun st => TQ2 x st
  | lkey "read_sbr_grid.L50b8", s => Tl k Ext x ra t₀ s fun st => TQ2 x st
      ∧ ((s.regs.get64 .r8).setWidth 32).toNat ≤ st.n.toNat + 1
      ∧ 2 ≤ ((s.regs.get64 .r8).setWidth 32).toNat
  | lkey "read_sbr_grid.L50bc", s => Tl k Ext x ra t₀ s fun st => TQ2 x st
      ∧ ((s.regs.get64 .rcx).setWidth 32).toNat ≤ st.n.toNat
  | lkey "read_sbr_grid.L4f65", s => Tl k Ext x ra t₀ s fun st => TQ2 x st
      ∧ ((s.regs.get64 .rcx).setWidth 32).toNat ≤ st.n.toNat
  | lkey "read_sbr_grid.L4f75", s => Tl k Ext x ra t₀ s fun st =>
      DWF False (st.dv x) ∧ Live st ∧ st.i.toNat ≤ x.p8.toNat
  | lkey "read_sbr_grid.L4f93", s => Tl k Ext x ra t₀ s fun st =>
      DWF False (st.dv x) ∧ Live st ∧ st.i.toNat ≤ x.p8.toNat
  | lkey "read_sbr_grid.L4fae", s => Tl k Ext x ra t₀ s fun st =>
      DWF False (st.dv x) ∧ Live st ∧ st.i.toNat ≤ x.p8.toNat
  -- the error paths and the return
  | lkey "read_sbr_grid.L4ec4", s => ErrS k Ext x ra t₀ s ∧ s.regs.get64 .rdi = x.avctx
  | lkey "read_sbr_grid.L4ecc", s => ErrS k Ext x ra t₀ s ∧ s.regs.get64 .rdi = x.avctx
  | lkey "read_sbr_grid.L4ed3", s => ErrS k Ext x ra t₀ s
  | lkey "read_sbr_grid.L506f", s => ErrS k Ext x ra t₀ s ∧ s.regs.get64 .rdi = arg0 t₀
  | lkey "read_sbr_grid.L5086", s => ErrS k Ext x ra t₀ s
  | lkey "read_sbr_grid.L508b", s => GridC x ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13
      ∧ ∃ st, GridOut x st ((s.regs.get64 .rax).setWidth 32)
        ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)
  | lkey "read_sbr_grid.done", s => GridC x ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ ∃ st, GridOut x st ((s.regs.get64 .rax).setWidth 32)
        ∧ (s.dmem =⋆ T k Ext x ra t₀ (Saved t₀) st)
  -- the traps (`ud1`), the VARVAR steps past `bs_num_rel_0 ≤ 3`, `bs_num_env = 0` in the
  -- tail, and the end of the border chain: not reached
  | _, _ => False

/-- The assertion at each label (a plain definition: `reduceTable` evaluates it at a literal
label). -/
def table (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData)
    (l : Label) (s : MachineData) : Prop :=
  tableK k Ext x ra t₀ (labKey l) s

/-- The variant: each loop's remaining iterations, ranked by the loop's position (the first loop
of a body above the `bs_freq_res` fill, the border chain above its back jump to `L4efc`, the
`t_q` index cases above their back jumps to `L4f65`). Constant (`32`) up to the first loop. -/
abbrev varK : Nat → MachineData → Nat
  -- first loops (`t_env`): 22 + remaining steps (at most 3)
  | lkey "read_sbr_grid.L4570", s => 22 + ((s.regs.get64 .rax).toNat - (s.regs.get64 .r8).toNat)
  | lkey "read_sbr_grid.L45a5", s => 22 + ((s.regs.get64 .rax).toNat - (s.regs.get64 .r8).toNat)
  | lkey "read_sbr_grid.L47f0", s | lkey "read_sbr_grid.L47fb", s | lkey "read_sbr_grid.L4806", s
  | lkey "read_sbr_grid.L483b", s | lkey "read_sbr_grid.L484f", s
  | lkey "read_sbr_grid.L4bd0", s | lkey "read_sbr_grid.L4bdb", s | lkey "read_sbr_grid.L4be6", s
  | lkey "read_sbr_grid.L4c1b", s | lkey "read_sbr_grid.L4c2f", s =>
      22 + ((s.regs.get64 .rsi).setWidth 32 - (s.regs.get64 .rax).setWidth 32).toNat
  -- between the loops
  | lkey "read_sbr_grid.L45bf", _ | lkey "read_sbr_grid.L45cb", _ | lkey "read_sbr_grid.L45d8", _
  | lkey "read_sbr_grid.L460b", _ | lkey "read_sbr_grid.L4621", _
  | lkey "read_sbr_grid.L486a", _ | lkey "read_sbr_grid.L4873", _ | lkey "read_sbr_grid.L4880", _
  | lkey "read_sbr_grid.L48b3", _
  | lkey "read_sbr_grid.L4c4a", _ | lkey "read_sbr_grid.L4c53", _ | lkey "read_sbr_grid.L4c5c", _
  | lkey "read_sbr_grid.L4c93", _ | lkey "read_sbr_grid.L4df1", _ => 12
  -- the `bs_freq_res` loops: 2 + remaining steps (at most 9)
  | lkey "read_sbr_grid.L4630", s | lkey "read_sbr_grid.L4662", s | lkey "read_sbr_grid.L4694", s
  | lkey "read_sbr_grid.L4e00", s | lkey "read_sbr_grid.L4e32", s | lkey "read_sbr_grid.L4e64", s =>
      2 + ((s.regs.get64 .r9).toNat - (s.regs.get64 .rax).toNat)
  | lkey "read_sbr_grid.L48d0", s | lkey "read_sbr_grid.L48f3", s | lkey "read_sbr_grid.L4905", s =>
      2 + (9 - ((s.regs.get64 .rsi).setWidth 32).toNat)
  -- after the fill, the border chain
  | lkey "read_sbr_grid.L4ca9", _ | lkey "read_sbr_grid.L4e6d", _ | lkey "read_sbr_grid.L4e73", _
  | lkey "read_sbr_grid.L4ea2", _ | lkey "read_sbr_grid.L4ed8", _
  | lkey "read_sbr_grid.L4fd3", _ | lkey "read_sbr_grid.L4fed", _ | lkey "read_sbr_grid.L5002", _
  | lkey "read_sbr_grid.L5018", _ | lkey "read_sbr_grid.L502d", _ | lkey "read_sbr_grid.L5043", _
  | lkey "read_sbr_grid.L5058", _ => 2
  -- `bs_num_noise`, `t_q[0]`, `t_q[nn]`, the index cases of `t_q[1]`
  | lkey "read_sbr_grid.L4efc", _ | lkey "read_sbr_grid.L4f11", _ | lkey "read_sbr_grid.L4f22", _
  | lkey "read_sbr_grid.L4f27", _ | lkey "read_sbr_grid.L5094", _ | lkey "read_sbr_grid.L509b", _
  | lkey "read_sbr_grid.L50ae", _ | lkey "read_sbr_grid.L50b8", _ | lkey "read_sbr_grid.L50bc", _ => 1
  -- `t_q[1]`, `e_a`, the error paths, the return
  | lkey "read_sbr_grid.L4f65", _ | lkey "read_sbr_grid.L4f75", _ | lkey "read_sbr_grid.L4f93", _
  | lkey "read_sbr_grid.L4fae", _ | lkey "read_sbr_grid.L4ec4", _ | lkey "read_sbr_grid.L4ecc", _
  | lkey "read_sbr_grid.L4ed3", _ | lkey "read_sbr_grid.L506f", _ | lkey "read_sbr_grid.L5086", _
  | lkey "read_sbr_grid.L508b", _ | lkey "read_sbr_grid.done", _ | lkey "read_sbr_grid.L50e8", _
  | lkey "read_sbr_grid.L510e", _ => 0
  -- the prologue, the dispatch, the class heads, FIXFIX, the code before the first loops
  | _, _ => 32

def var (l : Label) (s : MachineData) : Nat := varK (labKey l) s

open Lean Meta in
/-- `table … "label" s` and `var "label" s` to the label's entry, for `simp`/`dsimp`: the label
is turned into its key (`labKey`) by computation, and the lookup by key reduced. -/
def reduceAtLabel (f fK : Name) (e : Expr) : Simp.SimpM Simp.DStep := do
  unless e.isAppOf f do return .continue
  let args := e.getAppArgs
  if args.size < 2 then return .continue
  let .lit (.strVal str) := args[args.size - 2]! | return .continue
  let n := mkNatLit (str.toUTF8.foldl (fun n c => n * 256 + c.toNat) 0)
  let e' := mkAppN (mkConst fK) (args.set! (args.size - 2) n)
  return .visit (← whnfD e')

dsimproc [simp] reduceTable (@table ?c _ _ _ _ _ _ _) := reduceAtLabel ``table ``tableK

dsimproc [simp] reduceVar (var _ _) := reduceAtLabel ``var ``varK

/-- The edge order (`Program.EdgeLt`) once `var` is reduced: the variant decreased, or it is
unchanged and the target is later in the text (decided by the kernel: the elaborator's `decide`
on the label list exceeds the recursion depth). -/
macro "edge_lt" : tactic =>
  `(tactic| first
      | exact True.intro
      | (left; decide)
      | (right; exact True.intro)
      | (right; exact ⟨rfl, by decide +kernel⟩)
      | (right; exact ⟨True.intro, by decide +kernel⟩))

macro "grind_cells'" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

/-- What a return leaves, with the footprint byte by byte. -/
abbrev Post' (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  let r := t₀.regs.get64 .rsp
  ∃ st, GridOut x st ((s.regs.get64 .rax).setWidth 32)
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ (GFB Ext x t₀ st
      ⋆ Saved t₀ (8 ?@ r ⋆ x.R))))

/-- The exits: the return, and the call of `abort` (`av_assert0`), the shape of
`ProcSpecA.of_cfg_post`. -/
abbrev Exit (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData)
    (a : Int64) (s : MachineData) : Prop :=
  (a = ra ∧ Post' k Ext x ra t₀ s) ∨ a = abortA

abbrev BlockOb (k : Nat) (Ext : Mem 64 → Prop) (x : GArgs) (ra : Int64) (t₀ : MachineData)
    (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k Ext x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k Ext x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k Ext x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ Exit k Ext x ra t₀ a s ⦄

end Kraken.Examples.Sbr.Grid
