import Kraken.X64.Examples.Sbr.Parse.HdrSpec
import Kraken.X64.Examples.Sbr.Parse.HdrLib

/-!
# `read_sbr_header`: the block table

The frame below the return address (`r` = `rsp` at entry): `rbp`, `r14`, `rbx` pushed at
`r - 8`, `r - 0x10`, `r - 0x18`; 16 bytes of locals at `r - 0x28` of which the old
`spectrum_params` is saved at `r - 0x20` (4 bytes) and `r - 0x1c` (2 bytes); the return slot of
the call at `r - 0x30`, the callee's reservation below.

The values at a label are an `HSt` built by `St` from the fields read so far; the facts on them
grow along the path (`SpA` after the frequency fields, `SpB` after the extra fields, then the
reset flag, then the limiter fields).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Hdr

variable [CodeEnv]

/-- The values after the entry block (`start = 1`, `ready_for_dequant = 0`). -/
abbrev St (i : BitVec 32) (sp : List UInt8) (amp rs lb lg ip sm : BitVec 32) : HSt :=
  ⟨i, 1#32, 0#32, rs, sp, amp, lb, lg, ip, sm⟩

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

/-- The frame with the saved registers and the locals `Lc`. -/
abbrev Fr (t₀ : MachineData) (Lc : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .rbx) ⋆ (8 ?@ (r - 0x28#64) ⋆ (2 ?@ (r - 0x1a#64) ⋆ Lc))))

/-- The locals before the copy of `spectrum_params`. -/
abbrev L0 (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  4 ?@ (r - 0x20#64) ⋆ 2 ?@ (r - 0x1c#64)

/-- The locals holding the old `spectrum_params`. -/
abbrev Lsp (t₀ : MachineData) (sp : List UInt8) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  sp.take 4 =@ (r - 0x20#64) ⋆ sp.drop 4 =@ (r - 0x1c#64)

/-- The frame at entry. -/
abbrev FrB (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x8#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x28#64)
    ⋆ (2 ?@ (r - 0x1a#64) ⋆ L0 t₀))))

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- `sbr->usac` after the entry block: `is_usac`. -/
abbrev usacOf (t₀ : MachineData) : BitVec 32 := (arg2 t₀).setWidth 32

/-- The memory with `sbr->usac = u` and the caller's part `E`. -/
abbrev MtU (u : BitVec 32) (k : Nat) (x : HArgs) (t₀ : MachineData) (Fm : Mem 64 → Prop)
    (st : HSt) (Tl E : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  SbWu (arg0 t₀) u st ⋆ (GbW (arg1 t₀) x st.i ⋆ (Blocks [(x.buf, x.L)] ⋆ (Tl ⋆ (Fm
    ⋆ (8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ E))))))

/-- The memory with the caller's part `E` (`sbr->usac = is_usac`). -/
abbrev Mt (k : Nat) (x : HArgs) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl E : Mem 64 → Prop) : Mem 64 → Prop :=
  MtU (usacOf t₀) k x t₀ Fm st Tl E

/-- The memory with `sbr->usac = u`. -/
abbrev MU (u : BitVec 32) (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData)
    (Fm : Mem 64 → Prop) (st : HSt) (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  MtU u k x t₀ Fm st Tl (Rest x.R ra t₀)

/-- The memory at every label but the entry (`sbr->usac = is_usac`). -/
abbrev M (k : Nat) (x : HArgs) (ra : Int64) (t₀ : MachineData) (Fm : Mem 64 → Prop) (st : HSt)
    (Tl : Mem 64 → Prop) : Mem 64 → Prop :=
  MU (usacOf t₀) k x ra t₀ Fm st Tl

/-- The registers between the prologue and the call. -/
abbrev Rs (x : HArgs) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀
  ∧ s.regs.get64 .rsp = r - 0x28#64 ∧ s.regs.get64 .rbp = r - 0x8#64
  ∧ s.regs.get64 .rbx = x.idx.setWidth 64 ∧ s.regs.get64 .r8 = x.lb.setWidth 64
  ∧ s.regs.get64 .r12 = t₀.regs.get64 .r12 ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13
  ∧ s.regs.get64 .r15 = t₀.regs.get64 .r15

/-- The registers after the call. -/
abbrev Rs2 (x : HArgs) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x28#64 ∧ s.regs.get64 .rbp = r - 0x8#64
  ∧ s.regs.get64 .rbx = x.idx.setWidth 64
  ∧ s.regs.get64 .r12 = t₀.regs.get64 .r12 ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13
  ∧ s.regs.get64 .r15 = t₀.regs.get64 .r15

/-- The reader's index within its bounds. -/
abbrev Bnd (x : HArgs) (i : BitVec 32) : Prop := x.idx.toNat ≤ i.toNat ∧ i.toNat ≤ x.p8.toNat

/-- The frequency fields read (`bs_start_freq`, `bs_stop_freq`, and without USAC
`bs_amp_res_header`, `bs_xover_band`). -/
abbrev SpA (x : HArgs) (usac : BitVec 32) (sp : List UInt8) (amp : BitVec 32) : Prop :=
  sp.length = 6 ∧ u8 sp 0 < 16 ∧ u8 sp 1 < 16
  ∧ (usac = 0#32 → u8 sp 2 < 8 ∧ amp.toNat < 2)
  ∧ (usac ≠ 0#32 → sp.getD 2 0 = x.sp.getD 2 0 ∧ amp = x.amp)

/-- The extra fields read (`bs_freq_scale`, `bs_alter_scale`, `bs_noise_bands`). -/
abbrev SpB (sp : List UInt8) : Prop := u8 sp 3 < 4 ∧ u8 sp 4 < 2 ∧ u8 sp 5 < 4

/-- `bs_reset` after the compare. -/
abbrev rsOf (x : HArgs) (sp : List UInt8) : BitVec 32 := if sp = x.sp then x.reset else 1#32

/-- After the frequency and extra fields and the compare. -/
abbrev PB (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop) (x : HArgs) (ra : Int64)
    (t₀ s : MachineData) (P : HSt → Prop) : Prop :=
  ∃ (i : BitVec 32) (sp : List UInt8) (amp lb lg ip sm : BitVec 32), Bnd x i
    ∧ SpA x (usacOf t₀) sp amp ∧ SpB sp ∧ P (St i sp amp (rsOf x sp) lb lg ip sm)
    ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp)) (St i sp amp (rsOf x sp) lb lg ip sm)
      (TlT (arg0 t₀)))

/-- The limiter fields read. -/
abbrev Lim (st : HSt) : Prop :=
  st.lb.toNat < 4 ∧ st.lg.toNat < 4 ∧ st.ip.toNat < 2 ∧ st.sm.toNat < 2

/-- `HdrOut` without the return value. -/
abbrev Out (x : HArgs) (usac : BitVec 32) (st : HSt) : Prop :=
  st.start = 1#32 ∧ st.ready = 0#32 ∧ SpA x usac st.sp st.amp ∧ SpB st.sp
  ∧ st.reset = rsOf x st.sp ∧ Lim st ∧ Bnd x st.i

abbrev table (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "read_sbr_header", s => s = t₀ ∧ HdrC TlC x t₀
      ∧ ∃ u, (t₀.dmem =⋆ MU u k x ra t₀ (FrB t₀) x.st (TlT (arg0 t₀)))
  | "read_sbr_header.Ld1d", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (L0 t₀))
        (St x.idx x.sp x.amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Ld32", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ usacOf t₀ ≠ 0#32
      ∧ s.regs.get64 .rax = x.idx.setWidth 64
      ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
        (St x.idx x.sp x.amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Ld61", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ usacOf t₀ ≠ 0#32
      ∧ ∃ (i : BitVec 32) (sp : List UInt8), Bnd x i ∧ sp.length = 6 ∧ u8 sp 0 < 16
        ∧ sp.getD 2 0 = x.sp.getD 2 0
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp x.amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Ld91", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ usacOf t₀ = 0#32
      ∧ s.regs.get64 .rax = x.idx.setWidth 64
      ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
        (St x.idx x.sp x.amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Ldbd", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ usacOf t₀ = 0#32
      ∧ ∃ (i amp : BitVec 32), Bnd x i ∧ amp.toNat < 2
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i x.sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Lde8", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ usacOf t₀ = 0#32
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i ∧ amp.toNat < 2
        ∧ sp.length = 6 ∧ u8 sp 0 < 16
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Le1a", s => HdrC TlC x t₀ ∧ Rs x t₀ s ∧ usacOf t₀ = 0#32
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i ∧ amp.toNat < 2
        ∧ sp.length = 6 ∧ u8 sp 0 < 16 ∧ u8 sp 1 < 16
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Le45", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i
        ∧ SpA x (usacOf t₀) sp amp
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Le9d", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ s.regs.get64 .r10 = x.buf ∧ s.regs.get64 .r9 = x.p8.setWidth 64
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i
        ∧ s.regs.get64 .r11 = i.setWidth 64 ∧ SpA x (usacOf t₀) sp amp
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Leca", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i
        ∧ SpA x (usacOf t₀) sp amp ∧ u8 sp 3 < 4
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Lefb", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i
        ∧ SpA x (usacOf t₀) sp amp ∧ u8 sp 3 < 4 ∧ u8 sp 4 < 2
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Lf31", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i
        ∧ SpA x (usacOf t₀) sp amp
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Lf3a", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ ((s.regs.get64 .r9).setWidth 8).toNat < 4
      ∧ ∃ (i : BitVec 32) (sp : List UInt8) (amp : BitVec 32), Bnd x i
        ∧ SpA x (usacOf t₀) sp amp ∧ u8 sp 3 < 4 ∧ u8 sp 4 < 2
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp))
          (St i sp amp x.reset x.lb x.lg x.ip x.sm) (TlT (arg0 t₀)))
  | "read_sbr_header.Lf61", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => st.lb = x.lb ∧ st.lg = x.lg ∧ st.ip = x.ip ∧ st.sm = x.sm)
  | "read_sbr_header.Lf6d", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => st.lb = x.lb ∧ st.lg = x.lg ∧ st.ip = x.ip ∧ st.sm = x.sm)
  | "read_sbr_header.Lf98", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => st.lb.toNat < 4 ∧ st.lg = x.lg ∧ st.ip = x.ip ∧ st.sm = x.sm)
  | "read_sbr_header.Lfca", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => st.lb.toNat < 4 ∧ st.lg.toNat < 4 ∧ st.ip = x.ip
        ∧ st.sm = x.sm)
  | "read_sbr_header.Lff8", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => st.lb.toNat < 4 ∧ st.lg.toNat < 4 ∧ st.ip.toNat < 2
        ∧ st.sm = x.sm)
  | "read_sbr_header.L102d", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => st.lb = x.lb ∧ st.lg = x.lg ∧ st.ip = x.ip ∧ st.sm = x.sm)
  | "read_sbr_header.L1054", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => Lim st ∧ st.lb ≠ x.lb)
  | "read_sbr_header.L105a", s => HdrC TlC x t₀ ∧ Rs x t₀ s
      ∧ PB k TlT x ra t₀ s (fun st => Lim st ∧ st.called x)
  | "read_sbr_header.L1062", s => HdrC TlC x t₀ ∧ Rs2 x t₀ s ∧ s.regs.get64 .r14 = arg1 t₀
      ∧ ∃ st, Out x (usacOf t₀) st ∧ st.called x
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp)) st (TlT' st.lb (arg0 t₀)))
  | "read_sbr_header.L1065", s => HdrC TlC x t₀ ∧ Rs2 x t₀ s ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ ∃ st, Out x (usacOf t₀) st
        ∧ (s.dmem =⋆ M k x ra t₀ (Fr t₀ (Lsp t₀ x.sp)) st (TlOut TlT TlT' x t₀ st))
  | "read_sbr_header.done", s =>
      let r := t₀.regs.get64 .rsp
      s.regs.get64 .rsp = r ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ ∃ st, HdrOut x (usacOf t₀) st ((s.regs.get64 .rax).setWidth 32)
        ∧ (s.dmem =⋆ M k x ra t₀ (FrB t₀) st (TlOut TlT TlT' x t₀ st))
  | _, _ => False

abbrev var : Label → MachineData → Nat
  | _, _ => 0

/-- What a return leaves. -/
abbrev Post' (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (x : HArgs) (ra : Int64)
    (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ ∃ st, HdrOut x (usacOf t₀) st ((s.regs.get64 .rax).setWidth 32)
    ∧ (s.dmem =⋆ 8 ?@ r ⋆ Mt k x t₀ (FrB t₀) st (TlOut TlT TlT' x t₀ st) x.R)

abbrev BlockOb (k : Nat) (TlT : BitVec 64 → Mem 64 → Prop)
    (TlT' : BitVec 32 → BitVec 64 → Mem 64 → Prop) (TlC : BitVec 32 → BitVec 64 → Prop)
    (x : HArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k TlT TlT' TlC x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k TlT TlT' TlC x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k TlT TlT' TlC x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k TlT TlT' x ra t₀ s) ⦄

end Kraken.Examples.Sbr.Hdr
