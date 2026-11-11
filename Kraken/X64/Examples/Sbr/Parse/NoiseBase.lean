import Kraken.X64.Examples.Sbr.Parse.NoiseSpec

/-!
# `read_sbr_noise`: the block table

The frame (`r` the entry `rsp`, `rbp = r - 8`): the six pushes (`Saved`), the locals
(`Loc`: `ch_data` at `rbp-0x50`, `&noise_facs_q` at `rbp-0x48`, `ac` at `rbp-0x40`, `t_huff`
at `rbp-0x38`, the two shift copies in the raw word at `rbp-0x30`), the return slot of the
`av_log` call, `av_log`'s `k`. On the way out (and on the early exit before the locals are
written) the locals are raw (`Blank`).

The VLC tables: `t_huff = ff_aac_sbr_vlc[8 + b]`, `f_huff = ff_aac_sbr_vlc[5 + 2 b]` with
`b = (bs_coupling && ch)` (`kb`). Between the levels of a walk the table records the entry
`e` read so far with `VWalk` (`EnvVlc.lean`): its `sym` and `len` in registers, `len < 0`.

The variant: `100 (3 - i) + c` inside the outer loop (`i = r12`), with `c = 60` up to the
`f_huff` loop, `20 + (5 - j)` in it (`j = rdi`), `10` at its end; `1000` in the prologue,
`1` at `L66c9` (whose `jmp` goes backwards), `0` after the loop.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Vlc
open Kraken.Examples.Sbr.Parse (GbW labKey)

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.Noise

variable [CodeEnv]

/-- `bs_coupling && ch` as a number. -/
abbrev kb (x : NArgs) (t₀ : MachineData) : Nat :=
  if x.cpl ≠ 0#32 ∧ (arg4 t₀).setWidth 32 ≠ 0#32 then 1 else 0

abbrev kt (x : NArgs) (t₀ : MachineData) : Nat := 8 + kb x t₀
abbrev kf (x : NArgs) (t₀ : MachineData) : Nat := 5 + 2 * kb x t₀

/-- `t_huff` / `f_huff`. -/
abbrev TH (x : NArgs) (t₀ : MachineData) : VlcTab := x.v (kt x t₀)
abbrev FH (x : NArgs) (t₀ : MachineData) : VlcTab := x.v (kf x t₀)

abbrev Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x30#64) (t₀.regs.get64 .rbx) ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13) ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15) ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K)))))

abbrev BlankS (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x30#64) ⋆ (8 ?@ (r - 0x28#64) ⋆ (8 ?@ (r - 0x20#64) ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64) ⋆ (8 ?@ (r - 0x8#64) ⋆ K)))))

/-- The locals, written. -/
abbrev Loc (x : NArgs) (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x58#64) (arg3 t₀) ⋆ (c8 (r - 0x50#64) (arg3 t₀ + 0x15a50#64)
    ⋆ (c8 (r - 0x48#64) (arg0 t₀) ⋆ (c8 (r - 0x40#64) (TH x t₀).p ⋆ 8 ?@ (r - 0x38#64))))

/-- The locals, raw. -/
abbrev Blank (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x58#64) ⋆ (8 ?@ (r - 0x50#64) ⋆ (8 ?@ (r - 0x48#64) ⋆ (8 ?@ (r - 0x40#64)
    ⋆ 8 ?@ (r - 0x38#64))))

/-- The locals after the first and the second part of the prologue. -/
abbrev Loc1 (x : NArgs) (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x58#64) ⋆ (8 ?@ (r - 0x50#64)
    ⋆ (c8 (r - 0x48#64) (arg0 t₀) ⋆ (c8 (r - 0x40#64) (TH x t₀).p ⋆ 8 ?@ (r - 0x38#64))))

abbrev Loc2 (x : NArgs) (t₀ : MachineData) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x58#64) ⋆ (c8 (r - 0x50#64) (arg3 t₀ + 0x15a50#64)
    ⋆ (c8 (r - 0x48#64) (arg0 t₀) ⋆ (c8 (r - 0x40#64) (TH x t₀).p ⋆ 8 ?@ (r - 0x38#64))))

/-- The memory at every label: the return slot of the call, the callee's reservation, the
locals `LF`, the footprint with the reader's index `i`, the pushes `FR` over the caller's. -/
abbrev T (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (LF : Mem 64 → Prop) (FR : (Mem 64 → Prop) → Mem 64 → Prop) (i : BitVec 32) :
    Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64) ⋆ (LF ⋆ (NoiseF Ext x t₀ i ⋆ FR (Rest x.R ra t₀))))

/-- The registers kept after the prologue. -/
abbrev R1 (x : NArgs) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
  ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
  ∧ s.regs.get64 .r15 = (FH x t₀).p

/-- The memory with the locals `LF` and some reader index within bounds. -/
abbrev Mm (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (LF : Mem 64 → Prop) (s : MachineData) : Prop :=
  ∃ i : BitVec 32, i.toNat ≤ x.p8.toNat ∧ (s.dmem =⋆ T k Ext x ra t₀ LF (Saved t₀) i)

abbrev Base (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  NoiseC x ∧ R1 x t₀ s ∧ Mm k Ext x ra t₀ (Loc x t₀) s

/-- Inside the outer loop at row `c`. -/
abbrev Li (x : NArgs) (t₀ s : MachineData) (c : Nat) : Prop :=
  s.regs.get64 .r12 = BitVec.ofNat 64 c ∧ c < x.nn
  ∧ s.regs.get64 .r13 = arg3 t₀ + 0x15a56#64 + BitVec.ofNat 64 (5 * c)

abbrev Lp (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Base k Ext x ra t₀ s ∧ ∃ c, Li x t₀ s c
    ∧ s.regs.get64 .rbx = arg3 t₀ + 0x15a50#64 + BitVec.ofNat 64 (5 * c)

/-- After the first-level window (`rax` the index, `r10` the buffer, `r9` the window). -/
abbrev G1 (x : NArgs) (s : MachineData) : Prop :=
  (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  ∧ s.regs.get64 .r10 = x.buf ∧ (s.regs.get64 .r9).toNat < 512

/-- A subtable entry `e` of `t` (`len < 0`), reached in a walk with `d` levels left;
`sym` (zero-extended, as loaded) in `rs`, `len` (sign-extended) in `rl`. -/
abbrev Ent (t : VlcTab) (d : Nat) (rs rl : BitVec 64) : Prop :=
  ∃ e, VWalk t.es d e ∧ (vlen t.es e).msb = true
    ∧ rs = ((vsym t.es e).setWidth 32).setWidth 64
    ∧ rl = ((vlen t.es e).signExtend 32).setWidth 64

/-- The same with `sym` sign-extended (after `movswl`). -/
abbrev EntS (t : VlcTab) (d : Nat) (rs rl : BitVec 64) : Prop :=
  ∃ e, VWalk t.es d e ∧ (vlen t.es e).msb = true
    ∧ rs = ((vsym t.es e).signExtend 32).setWidth 64
    ∧ rl = ((vlen t.es e).signExtend 32).setWidth 64

/-- In the `f_huff` loop at element `j + 1`. -/
abbrev Dj (x : NArgs) (s : MachineData) : Prop :=
  ∃ j, s.regs.get64 .rdi = BitVec.ofNat 64 j ∧ j + 1 < x.nq

abbrev Lq (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  Base k Ext x ra t₀ s ∧ (∃ c, Li x t₀ s c) ∧ Dj x s

/-- On the way out: the locals raw. -/
abbrev Out (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  NoiseC x ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64 ∧ Mm k Ext x ra t₀ (Blank t₀) s

abbrev RetV (s : MachineData) : Prop :=
  (s.regs.get64 .rax).setWidth 32 = 0#32 ∨ (s.regs.get64 .rax).setWidth 32 = 0xbebbb1b7#32

abbrev tableK (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData) :
    Nat → MachineData → Prop
  | lkey "read_sbr_noise", s => s = t₀ ∧ NoiseC x
      ∧ (t₀.dmem =⋆ T k Ext x ra t₀ (Blank t₀) (BlankS (t₀.regs.get64 .rsp)) x.idx)
  | lkey "read_sbr_noise.L6111", s => NoiseC x
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .r8 = arg4 t₀
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Blank t₀) (Saved t₀) x.idx)
  | lkey "read_sbr_noise.L613d", s => NoiseC x ∧ 0 < x.nn
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .r9 = arg3 t₀ ∧ s.regs.get64 .rdi = arg0 t₀
      ∧ (s.regs.get64 .r10).setWidth 8 &&& (s.regs.get64 .rcx).setWidth 8
          = BitVec.ofNat 8 (kb x t₀)
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Blank t₀) (Saved t₀) x.idx)
  | lkey "read_sbr_noise.L615b", s => NoiseC x ∧ 0 < x.nn
      ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x58#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
      ∧ s.regs.get64 .r9 = arg3 t₀ ∧ s.regs.get64 .rax = VA
      ∧ s.regs.get64 .rcx = BitVec.ofNat 64 (kb x t₀)
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Loc1 x t₀) (Saved t₀) x.idx)
  | lkey "read_sbr_noise.L6172", s => NoiseC x ∧ 0 < x.nn ∧ R1 x t₀ s
      ∧ s.regs.get64 .r9 = arg3 t₀
      ∧ (s.dmem =⋆ T k Ext x ra t₀ (Loc2 x t₀) (Saved t₀) x.idx)
  | lkey "read_sbr_noise.L6190", s => Base k Ext x ra t₀ s ∧ (∃ c, Li x t₀ s c)
      ∧ s.regs.get64 .r9 = arg3 t₀
  | lkey "read_sbr_noise.L61a9", s => Base k Ext x ra t₀ s ∧ (∃ c, Li x t₀ s c)
  -- element 0 (`rbx = 5 c` until its tail)
  | lkey "read_sbr_noise.L61d7", s => Base k Ext x ra t₀ s
      ∧ (∃ c, Li x t₀ s c ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (5 * c)) ∧ G1 x s
  | lkey "read_sbr_noise.L61ee", s => Base k Ext x ra t₀ s
      ∧ (∃ c, Li x t₀ s c ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (5 * c))
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r10 = x.buf ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ Ent (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L6210", s => Base k Ext x ra t₀ s
      ∧ (∃ c, Li x t₀ s c ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (5 * c))
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ EntS (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L6224", s => Base k Ext x ra t₀ s
      ∧ (∃ c, Li x t₀ s c ∧ s.regs.get64 .rbx = BitVec.ofNat 64 (5 * c))
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  -- elements 1–4
  | lkey "read_sbr_noise.L624c", s => Lp k Ext x ra t₀ s
  | lkey "read_sbr_noise.L62f0", s => Lp k Ext x ra t₀ s
  | lkey "read_sbr_noise.L6394", s => Lp k Ext x ra t₀ s
  | lkey "read_sbr_noise.L6438", s => Lp k Ext x ra t₀ s
  | lkey "read_sbr_noise.L64dc", s => Lp k Ext x ra t₀ s
  | lkey "read_sbr_noise.L627f", s => Lp k Ext x ra t₀ s ∧ G1 x s
  | lkey "read_sbr_noise.L6323", s => Lp k Ext x ra t₀ s ∧ G1 x s
  | lkey "read_sbr_noise.L63c7", s => Lp k Ext x ra t₀ s ∧ G1 x s
  | lkey "read_sbr_noise.L646b", s => Lp k Ext x ra t₀ s ∧ G1 x s
  | lkey "read_sbr_noise.L6296", s => Lp k Ext x ra t₀ s
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r10 = x.buf ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ Ent (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L633a", s => Lp k Ext x ra t₀ s
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r10 = x.buf ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ Ent (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L63de", s => Lp k Ext x ra t₀ s
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r10 = x.buf ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ Ent (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L6482", s => Lp k Ext x ra t₀ s
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r10 = x.buf ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ Ent (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L62b8", s => Lp k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ EntS (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L635c", s => Lp k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ EntS (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L6400", s => Lp k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ EntS (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L64a4", s => Lp k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = (TH x t₀).p
      ∧ EntS (TH x t₀) 3 (s.regs.get64 .r9) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L62cc", s => Lp k Ext x ra t₀ s ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  | lkey "read_sbr_noise.L6370", s => Lp k Ext x ra t₀ s ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  | lkey "read_sbr_noise.L6414", s => Lp k Ext x ra t₀ s ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  | lkey "read_sbr_noise.L64b8", s => Lp k Ext x ra t₀ s ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  -- the `f_huff` path
  | lkey "read_sbr_noise.L64f0", s => Base k Ext x ra t₀ s ∧ (∃ c, Li x t₀ s c)
      ∧ s.regs.get64 .r9 = arg3 t₀
  | lkey "read_sbr_noise.L651b", s => Base k Ext x ra t₀ s ∧ (∃ c, Li x t₀ s c)
      ∧ s.regs.get64 .r9 = arg3 t₀ ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat
  | lkey "read_sbr_noise.L6540", s => Lq k Ext x ra t₀ s
  | lkey "read_sbr_noise.L6568", s => Lq k Ext x ra t₀ s
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r14 = x.buf ∧ (s.regs.get64 .r10).toNat < 512
  | lkey "read_sbr_noise.L657b", s => Lq k Ext x ra t₀ s
      ∧ (s.regs.get64 .rax).toNat ≤ x.p8.toNat ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ s.regs.get64 .r14 = x.buf
      ∧ Ent (FH x t₀) 3 (s.regs.get64 .r10) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L659b", s => Lq k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = x.buf
      ∧ EntS (FH x t₀) 3 (s.regs.get64 .r10) (s.regs.get64 .r11)
  | lkey "read_sbr_noise.L65b7", s => Lq k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64 ∧ s.regs.get64 .r14 = x.buf
      ∧ Ent (FH x t₀) 2 (s.regs.get64 .r10) (s.regs.get64 .rbx)
  | lkey "read_sbr_noise.L65d9", s => Lq k Ext x ra t₀ s
      ∧ s.regs.get64 .r8 = x.p8.setWidth 64
      ∧ EntS (FH x t₀) 2 (s.regs.get64 .r10) (s.regs.get64 .rbx)
  | lkey "read_sbr_noise.L65f0", s => Lq k Ext x ra t₀ s ∧ s.regs.get64 .r8 = x.p8.setWidth 64
  | lkey "read_sbr_noise.L6607", s => Lq k Ext x ra t₀ s
  -- the end of a row, the error path, the copy of the last row, the return
  | lkey "read_sbr_noise.L6640", s => Base k Ext x ra t₀ s ∧ ∃ c, Li x t₀ s c
  | lkey "read_sbr_noise.L6663", s => Base k Ext x ra t₀ s
  | lkey "read_sbr_noise.L6667", s => Base k Ext x ra t₀ s
  | lkey "read_sbr_noise.L66c9", s => Base k Ext x ra t₀ s
  | lkey "read_sbr_noise.L6689", s => Base k Ext x ra t₀ s ∧ s.regs.get64 .r9 = arg3 t₀
      ∧ s.regs.get64 .r8 = BitVec.ofNat 64 x.nn
  | lkey "read_sbr_noise.L6694", s => Out k Ext x ra t₀ s ∧ s.regs.get64 .r9 = arg3 t₀
      ∧ s.regs.get64 .r8 = BitVec.ofNat 64 x.nn ∧ s.regs.get64 .rax = 0#64
  | lkey "read_sbr_noise.L66ba", s => Out k Ext x ra t₀ s ∧ RetV s
  | lkey "read_sbr_noise.done", s => NoiseC x ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s ∧ RetV s
      ∧ Mm k Ext x ra t₀ (Blank t₀) s
  | _, _ => False

abbrev varK : Nat → MachineData → Nat
  | lkey "read_sbr_noise", _ => 1000
  | lkey "read_sbr_noise.L6111", _ => 1000
  | lkey "read_sbr_noise.L613d", _ => 1000
  | lkey "read_sbr_noise.L615b", _ => 1000
  | lkey "read_sbr_noise.L6172", _ => 1000
  | lkey "read_sbr_noise.L6190", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L61a9", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L61d7", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L61ee", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6210", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6224", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L624c", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L627f", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6296", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L62b8", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L62cc", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L62f0", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6323", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L633a", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L635c", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6370", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6394", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L63c7", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L63de", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6400", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6414", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6438", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L646b", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6482", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L64a4", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L64b8", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L64dc", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L64f0", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L651b", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 60
  | lkey "read_sbr_noise.L6540", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L6568", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L657b", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L659b", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L65b7", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L65d9", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L65f0", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L6607", s =>
      100 * (3 - (s.regs.get64 .r12).toNat) + 20 + (5 - (s.regs.get64 .rdi).toNat)
  | lkey "read_sbr_noise.L6640", s => 100 * (3 - (s.regs.get64 .r12).toNat) + 10
  | lkey "read_sbr_noise.L66c9", _ => 1
  | _, _ => 0

/-- The assertion at each label (a plain definition: `reduceTable` evaluates it at a literal
label). -/
def table (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (l : Label) (s : MachineData) : Prop :=
  tableK k Ext x ra t₀ (labKey l) s

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

/-- The edge order (`Program.EdgeLt`) once `var` is reduced. -/
macro "edge_lt" : tactic =>
  `(tactic| first
      | exact True.intro
      | (left; decide)
      | (right; exact True.intro)
      | (right; exact ⟨rfl, by decide +kernel⟩)
      | (right; exact ⟨True.intro, by decide +kernel⟩))

/-- The exit: the return, the footprint at some index, the locals raw. -/
abbrev Post' (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ s : MachineData) :
    Prop :=
  let r := t₀.regs.get64 .rsp
  ∃ i : BitVec 32, i.toNat ≤ x.p8.toNat ∧ RetV s
    ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
    ∧ (s.dmem =⋆ 8 ?@ (r - 0x60#64) ⋆ (Reserve k (r - 0x60#64) ⋆ (Blank t₀
      ⋆ (NoiseF Ext x t₀ i ⋆ Saved t₀ (8 ?@ r ⋆ x.R)))))

abbrev BlockOb (k : Nat) (Ext : Mem 64 → Prop) (x : NArgs) (ra : Int64) (t₀ : MachineData)
    (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k Ext x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k Ext x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k Ext x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k Ext x ra t₀ s) ⦄

macro "grind_cells'" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

end Kraken.Examples.Sbr.Noise
