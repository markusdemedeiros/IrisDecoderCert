import Kraken.X64.Examples.Sbr.Parse.InitSpec

/-!
# `ff_aac_sbr_ctx_alloc_init`: the block table

The frame below the return address (`r` = `rsp` at entry): `rbp`, `r15`, `r14`, `rbx` pushed at
`r - 8` … `r - 0x20`; 24 bytes of locals at `r - 0x38` (the stack argument `flags` of `av_tx_init`
at `r - 0x38`, the float `scale` at `r - 0x24`, 12 unused bytes); the return slot of a call at
`r - 0x40`, the callee's reservation below.

The body of the memory (`B`) is `*che` (raw), then `*che` with the zeroed element, then `*che = p`
with the element `ElemS p v`, where the cells `v` grow along the path (`evA` … `evW`), and the
`av_tx` contexts once they exist.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr
open Kraken.Examples.Sbr.Apply (c8)
open Kraken.Examples.Sbr.Session (zs)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

/-! ## The cells along the path -/

def evA (p : BitVec 64) : EV := { ev0 with pr0 := Int.toBytes 8 (p + 0x1e120#64).toInt }

def evB (p : BitVec 64) : EV :=
  { evA p with pr1 := Int.toBytes 8 (p + 0x23520#64).toInt, kx0 := Int.toBytes 4 0 }

def evC (p : BitVec 64) (id : BitVec 32) : EV :=
  { evB p with id := Int.toBytes 4 id.toInt, usac := Int.toBytes 4 0 }

def evD (p : BitVec 64) (id : BitVec 32) : EV :=
  { evC p id with sr := Int.toBytes 8 0, kx1 := Int.toBytes 4 32 }

def evE (p : BitVec 64) (id : BitVec 32) : EV :=
  { evD p id with m1 := Int.toBytes 4 0, e1 := Int.toBytes 4 (-1) }

def evF (p : BitVec 64) (id : BitVec 32) : EV :=
  { evE p id with e0 := Int.toBytes 4 (-1), spLo := Int.toBytes 4 (-1) }

def evG (p : BitVec 64) (id : BitVec 32) : EV :=
  { evF p id with spHi := Int.toBytes 2 (-1), v0 := Int.toBytes 4 0x480 }

def evH (p : BitVec 64) (id : BitVec 32) : EV :=
  { evG p id with v1 := Int.toBytes 4 0x480 }

/-- After `av_tx_init(&sbr->mdct, …)`. -/
def evS (p : BitVec 64) (id : BitVec 32) (c : BitVec 64) (f : Int64) : EV :=
  { evH p id with synC := Int.toBytes 8 c.toInt, synF := fb f }

/-- After `av_tx_init(&sbr->mdct_ana, …)`. -/
def evT (p : BitVec 64) (id : BitVec 32) (c : BitVec 64) (f : Int64) (c' : BitVec 64)
    (f' : Int64) : EV :=
  { evS p id c f with anaC := Int.toBytes 8 c'.toInt, anaF := fb f' }

def evU (p : BitVec 64) (id : BitVec 32) (c : BitVec 64) (f : Int64) (c' : BitVec 64)
    (f' : Int64) (psd : List UInt8) : EV :=
  { evT p id c f c' f' with ps := psd }

def evV (p : BitVec 64) (id : BitVec 32) (c : BitVec 64) (f : Int64) (c' : BitVec 64)
    (f' : Int64) (psd d : List UInt8) : EV :=
  { evU p id c f c' f' psd with dsp := d }

def evW (p : BitVec 64) (id : BitVec 32) (c : BitVec 64) (f : Int64) (c' : BitVec 64)
    (f' : Int64) (psd d : List UInt8) : EV :=
  { evV p id c f c' f' psd d with
    c0 := fb (entry "sbr_lf_gen"), c1 := fb (entry "sbr_hf_assemble") }

/-! ## The memory -/

/-- The saved registers and the locals. -/
abbrev Fr (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14) ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .rbx)
    ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64) ⋆ 8 ?@ (r - 0x38#64))))))

/-- The frame's slots, contents forgotten. -/
abbrev FrB (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x8#64) ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x18#64) ⋆ (8 ?@ (r - 0x20#64)
    ⋆ (4 ?@ (r - 0x24#64) ⋆ (12 ?@ (r - 0x30#64) ⋆ 8 ?@ (r - 0x38#64))))))

def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- The memory: the frame `Fm`, the return slot of a call and the callee's reservation, the body
`B`, the callees' state, the caller's part `E`. -/
abbrev MF (k : Nat) (TxTab X : Mem 64 → Prop) (t₀ : MachineData) (Fm B E : Mem 64 → Prop) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  Fm ⋆ (8 ?@ (r - 0x40#64) ⋆ (Reserve k (r - 0x40#64) ⋆ (B ⋆ (TxTab ⋆ (X ⋆ E)))))

/-- The memory at every label after the prologue. -/
abbrev M (k : Nat) (TxTab X R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData)
    (B : Mem 64 → Prop) : Mem 64 → Prop :=
  MF k TxTab X t₀ (Fr t₀) B (Rest R ra t₀)

/-- `*che = p`, the element with the cells `v`. -/
abbrev BE0 (t₀ : MachineData) (p : BitVec 64) (v : EV) : Mem 64 → Prop :=
  c8 (arg1 t₀) p ⋆ ElemS p v

/-- … and the context `c` of `sbr->mdct`. -/
abbrev BE1 (Ctx : BitVec 64 → Mem 64 → Prop) (t₀ : MachineData) (p : BitVec 64) (v : EV)
    (c : BitVec 64) : Mem 64 → Prop :=
  c8 (arg1 t₀) p ⋆ (ElemS p v ⋆ Ctx c)

/-- … and the contexts `c'` of `sbr->mdct_ana` and `c` of `sbr->mdct`. -/
abbrev BE2 (Ctx : BitVec 64 → Mem 64 → Prop) (t₀ : MachineData) (p : BitVec 64) (v : EV)
    (c c' : BitVec 64) : Mem 64 → Prop :=
  c8 (arg1 t₀) p ⋆ (ElemS p v ⋆ (Ctx c' ⋆ Ctx c))

/-- The registers after the prologue. -/
abbrev Rs (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x38#64 ∧ s.regs.get64 .rbp = r - 0x8#64
  ∧ s.regs.get64 .r14 = (idOf t₀).setWidth 64 ∧ s.regs.get64 .r15 = arg1 t₀
  ∧ s.regs.get64 .r12 = t₀.regs.get64 .r12 ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13

/-- After the first `av_tx_init` failed: `*che = p`, the element with the cells `evPre`, `*ctx`
and `*tx` of `sbr->mdct` the bytes `bc`, `bf`. -/
abbrev BF1 (t₀ : MachineData) (p : BitVec 64) (bc bf : List UInt8) : Mem 64 → Prop :=
  c8 (arg1 t₀) p ⋆ ElemS p { evPre (idOf t₀) p with synC := bc, synF := bf }

/-- After the second failed: also the first context `c` and function `f`. -/
abbrev BF2 (Ctx : BitVec 64 → Mem 64 → Prop) (t₀ : MachineData) (p c : BitVec 64) (f : Int64)
    (bc bf : List UInt8) : Mem 64 → Prop :=
  c8 (arg1 t₀) p ⋆ (ElemS p
    { evPre (idOf t₀) p with synC := Int.toBytes 8 c.toInt, synF := fb f, anaC := bc, anaF := bf }
    ⋆ Ctx c)

/-- The contracts of the two `av_tx` functions (`sbr->mdct_fn` `f`, `sbr->mdct_ana_fn` `f'`). -/
abbrev TF (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) (f f' : Int64) :
    Prop :=
  TxSpec Ctx TxTab k f ∧ TxSpec Ctx TxTab k f'

/-- The four outcomes with the result `ret`, the memory `Mk B` around the body `B`. -/
def Out (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) (t₀ : MachineData)
    (Mk : (Mem 64 → Prop) → Mem 64 → Prop) (ret : BitVec 32) (m : Mem 64) : Prop :=
  (ret = 0#32 ∧ ∃ r : IR, r.psd.length = 64 ∧ DspSlotsOK r.sl
    ∧ TxSpec Ctx TxTab k r.anaFn ∧ TxSpec Ctx TxTab k r.synFn
    ∧ (m =⋆ Mk (InitOK Ctx (arg1 t₀) (idOf t₀) r)))
  ∨ (ret = 0xfffffff4#32 ∧ (m =⋆ Mk (8 ?@ arg1 t₀)))
  ∨ (ret.toInt < 0 ∧ ∃ (p : BitVec 64) (bc bf : List UInt8), bc.length = 8 ∧ bf.length = 8
    ∧ (m =⋆ Mk (BF1 t₀ p bc bf)))
  ∨ (ret.toInt < 0 ∧ ∃ (p c : BitVec 64) (f : Int64) (bc bf : List UInt8), bc.length = 8
    ∧ bf.length = 8 ∧ (m =⋆ Mk (BF2 Ctx t₀ p c f bc bf)))

abbrev eax (s : MachineData) : BitVec 32 := (s.regs.get64 .rax).setWidth 32

abbrev rbx (s : MachineData) : BitVec 64 := s.regs.get64 .rbx

abbrev table (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop
  | "ff_aac_sbr_ctx_alloc_init", s => s = t₀
      ∧ (t₀.dmem =⋆ MF k TxTab X t₀ (FrB t₀) (8 ?@ arg1 t₀) (Rest R ra t₀))
  | "ff_aac_sbr_ctx_alloc_init.L22", s => Rs t₀ s ∧ rbx s = rbx t₀
      ∧ ((s.regs.get64 .rax = 0#64 ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (8 ?@ arg1 t₀)))
        ∨ (s.regs.get64 .rax ≠ 0#64
          ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (8 ?@ arg1 t₀ ⋆ zs 0x88ba0 =@ s.regs.get64 .rax))))
  | "ff_aac_sbr_ctx_alloc_init.L2b", s => Rs t₀ s ∧ rbx s = rbx t₀ ∧ s.regs.get64 .rax ≠ 0#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (8 ?@ arg1 t₀ ⋆ zs 0x88ba0 =@ s.regs.get64 .rax))
  | "ff_aac_sbr_ctx_alloc_init.L3e", s => Rs t₀ s
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evA (rbx s))))
  | "ff_aac_sbr_ctx_alloc_init.L58", s => Rs t₀ s
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evB (rbx s))))
  | "ff_aac_sbr_ctx_alloc_init.L67", s => Rs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evC (rbx s) (idOf t₀))))
  | "ff_aac_sbr_ctx_alloc_init.L78", s => Rs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evD (rbx s) (idOf t₀))))
  | "ff_aac_sbr_ctx_alloc_init.L89", s => Rs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ s.regs.get64 .rcx = 0xffffffff#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evE (rbx s) (idOf t₀))))
  | "ff_aac_sbr_ctx_alloc_init.L95", s => Rs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evF (rbx s) (idOf t₀))))
  | "ff_aac_sbr_ctx_alloc_init.La9", s => Rs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ s.regs.get64 .rcx = 0x480#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evG (rbx s) (idOf t₀))))
  | "ff_aac_sbr_ctx_alloc_init.Lba", s => Rs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ s.regs.get64 .r9 = t₀.regs.get64 .rsp - 0x24#64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE0 t₀ (rbx s) (evH (rbx s) (idOf t₀))))
  | "ff_aac_sbr_ctx_alloc_init.Le1", s => Rs t₀ s
      ∧ ((0 ≤ (eax s).toInt ∧ ∃ c f, TxSpec Ctx TxTab k f
          ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE1 Ctx t₀ (rbx s) (evS (rbx s) (idOf t₀) c f) c)))
        ∨ ((eax s).toInt < 0 ∧ ∃ bc bf : List UInt8, bc.length = 8 ∧ bf.length = 8
          ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BF1 t₀ (rbx s) bc bf))))
  | "ff_aac_sbr_ctx_alloc_init.Le9", s => Rs t₀ s ∧ ∃ c f, TxSpec Ctx TxTab k f
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BE1 Ctx t₀ (rbx s) (evS (rbx s) (idOf t₀) c f) c))
  | "ff_aac_sbr_ctx_alloc_init.L11f", s => Rs t₀ s
      ∧ ((0 ≤ (eax s).toInt ∧ ∃ c f c' f', TF k Ctx TxTab f f'
          ∧ (s.dmem =⋆ M k TxTab X R ra t₀
            (BE2 Ctx t₀ (rbx s) (evT (rbx s) (idOf t₀) c f c' f') c c')))
        ∨ ((eax s).toInt < 0 ∧ ∃ (c : BitVec 64) (f : Int64) (bc bf : List UInt8), bc.length = 8
          ∧ bf.length = 8 ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (BF2 Ctx t₀ (rbx s) c f bc bf))))
  | "ff_aac_sbr_ctx_alloc_init.L123", s => Rs t₀ s ∧ ∃ c f c' f', TF k Ctx TxTab f f'
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀
        (BE2 Ctx t₀ (rbx s) (evT (rbx s) (idOf t₀) c f c' f') c c'))
  | "ff_aac_sbr_ctx_alloc_init.L12f", s => Rs t₀ s ∧ ∃ c f c' f' psd, TF k Ctx TxTab f f'
      ∧ psd.length = 64
      ∧ (s.dmem =⋆ M k TxTab X R ra t₀
        (BE2 Ctx t₀ (rbx s) (evU (rbx s) (idOf t₀) c f c' f' psd) c c'))
  | "ff_aac_sbr_ctx_alloc_init.L13e", s => Rs t₀ s ∧ ∃ c f c' f' psd sl, TF k Ctx TxTab f f'
      ∧ psd.length = 64
      ∧ DspSlotsOK sl ∧ (s.dmem =⋆ M k TxTab X R ra t₀
        (BE2 Ctx t₀ (rbx s) (evV (rbx s) (idOf t₀) c f c' f' psd sl.bytes) c c'))
  | "ff_aac_sbr_ctx_alloc_init.L15a", s => Rs t₀ s ∧ ∃ c f c' f' psd sl, TF k Ctx TxTab f f'
      ∧ psd.length = 64
      ∧ DspSlotsOK sl ∧ (s.dmem =⋆ M k TxTab X R ra t₀
        (BE2 Ctx t₀ (rbx s) (evW (rbx s) (idOf t₀) c f c' f' psd sl.bytes) c c'))
  | "ff_aac_sbr_ctx_alloc_init.L17a", s => Rs t₀ s ∧ (s.dmem =⋆ M k TxTab X R ra t₀ (8 ?@ arg1 t₀))
  | "ff_aac_sbr_ctx_alloc_init.L17f", s => Rs t₀ s
      ∧ Out k Ctx TxTab t₀ (M k TxTab X R ra t₀) (eax s) s.dmem
  | "ff_aac_sbr_ctx_alloc_init.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ Out k Ctx TxTab t₀ (fun B => MF k TxTab X t₀ (FrB t₀) B (Rest R ra t₀)) (eax s) s.dmem
  | _, _ => False

abbrev var : Label → MachineData → Nat
  | _, _ => 0

/-- What a return leaves. -/
abbrev Post' (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X R : Mem 64 → Prop)
    (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ Out k Ctx TxTab t₀ (fun B => 8 ?@ r ⋆ MF k TxTab X t₀ (FrB t₀) B R) (eax s) s.dmem

abbrev BlockOb (k : Nat) (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab X R : Mem 64 → Prop)
    (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k Ctx TxTab X R ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k Ctx TxTab X R ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k Ctx TxTab X R ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k Ctx TxTab X R t₀ s) ⦄

end Kraken.Examples.Sbr.Init
