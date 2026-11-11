import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.IntMisc
import Kraken.Rules.ScalarFloat
import Kraken.Rules.CallFrame
import Kraken.Rules.CfgList
import Kraken.Rules.LeafLemmas
import Kraken.Rules.FrameLemmas
import Kraken.Rules.HelperLemmas
import Kraken.X64.Examples.Sbr.Spec
import Kraken.X64.Examples.Sbr.LfGenText

/-!
# `sbr_lf_gen` as a `ProcSpec`

Memory safety of the compiled `sbr_lf_gen(sbr, X_low, W, buf_idx)` of
`libavcodec/aacsbr_template.c` (the four-argument version, `numTimeSlots = 16`,
so `i_f = 32`; recent upstream adds a `numTimeSlots` argument).

## Contract vs. the C code

The specification (`LfGenSpec`, footprint `LfGenF`, side conditions `LfGenC`,
the assumed `MemsetSpec`) is in `Spec.lean`; this file proves it (`spec`).

* Footprint: `X_low[32][40][2]` (10240 bytes, written: a `memset` of the whole
  array, then the two copy loops), `W[2][32][32][2]` (16384 bytes, read), and
  the two `int` cells `sbr->kx[0]` (`sbr + 0x54`), `sbr->kx[1]` (`sbr + 0x58`),
  read. The code reloads `kx` on every iteration (it cannot prove the stores
  to `X_low` do not alias `sbr`), so the cells must stay in the footprint and
  be disjoint from `X_low`.
* `LfGenC`: `buf_idx ∈ {0, 1}` (low 32 bits of `rcx`, `movslq`), and
  `kx[0], kx[1] ≤ 32`. Both loops are compiled as do-while after a `kx ≠ 0`
  test, with an unsigned exit test, and each has a bounds-check trap (`ud1`)
  reached exactly when `k` would reach 32: with `kx > 32` the code traps (and
  before that writes `X_low[k]` for `k < 32` only); with `kx < 0` (as unsigned
  `> 32`) the same. The traps are labels with table `False`: every edge into
  one is shown unreachable from `kx ≤ 32`.
* `memset` is called through the PLT on `(X_low, 0, 0x2800)`; its contract is
  the assumed `MemsetSpec` (writes `dst[0, n)`, nothing else).
* Frame: five pushes (`rbp`, `r15`, `r14`, `r12`, `rbx`), the call's return
  slot and `memset`'s own `k`: `lfNeed k = 0x30 + k`.

## SbrWF clauses this needs from the caller (`sbr_apply`'s call site)

* `0 ≤ sbr->kx[0], sbr->kx[1] ≤ 32`. Upstream: `sbr_make_f_derived` rejects
  `kx[1] > 32` ("Start frequency border too high") and `sbr_reset` then calls
  `sbr_turnoff`, which sets `kx[1] = 32`; `kx[0]` is only ever a copy of a
  previous `kx[1]` (`read_sbr_data`, `sbr_apply`, the context init, where it is
  0 from `av_mallocz`). So the invariant `kx[i] ∈ [0, 32]` holds of every
  `sbr` the decoder hands over.
* `buf_idx = sbr->data[ch].Ypos ∈ {0, 1}` (initialised 0, toggled by `^= 1`).
* `X_low = sbr->X_low`, `W = sbr->data[ch].W` and the `kx` cells as disjoint
  pieces of `*sbr` carved by the caller.

## Library

`Mem.Blocks.Inside.self_off` and the `inc` rule, first written here, are in
`Kraken.Rules.HelperLemmas` (the `inc` rule was written three more times in
the other M3 proofs).

## Costs (`lake env lean`, this machine)

Per block (heartbeats in units of 1000, wall ms, measured with `measure_hb`):
La190/a1..a7 126-130k, ~17 s each; La5b0/b1 127k, ~15 s; m1 235k, 47 s;
entry 89k, 8.6 s; a8 71k, 8.1 s; La6ba 49k, 5.3 s; b2 45k, 4.1 s;
La588 34k, 4.0 s; done 27k, 3.0 s; c 13k, 1.6 s. Whole file: about 72 s wall
(parallel elaboration), 4 min 20 s CPU. Each block's `maxHeartbeats` is at most
about 1.5 times its measured cost (the blocks at 126-130k use the default 200k).
-/

open Kraken
open Kraken.SysV
open Mem

/-! ## The proof -/

open Kraken.X64.Parser
open Std.WP
open MachineWP

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.LfGen

variable [CodeEnv]

abbrev K (n : Nat) : BitVec 64 := BitVec.ofNat 64 n

abbrev c8 (a v : BitVec 64) : Mem 64 → Prop := Int.toBytes 8 v.toInt =@ a

/-- The caller's memory behind the footprint: the return address and `R`. -/
def Rest (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ R

/-- `X_low` and `W`, behind a name `grind` does not unfold. -/
def DataW (t : MachineData) : Mem 64 → Prop := Blocks [(arg1 t, 10240), (arg2 t, 16384)]

/-- The two `kx` cells, behind a name `grind` does not unfold. -/
def KxW (x : LfGenArgs) (t : MachineData) : Mem 64 → Prop := LfGenKx x t

omit [CodeEnv] in
theorem KxW_open (x : LfGenArgs) (t : MachineData) (K : Mem 64 → Prop) :
    KxW x t ⋆ K = Int.toBytes 4 (x.kx0 : Int) =@ (arg0 t + 0x54#64)
      ⋆ (Int.toBytes 4 (x.kx1 : Int) =@ (arg0 t + 0x58#64) ⋆ K) := by
  simp only [KxW, LfGenKx, Std.ExtHashMap.sep_assoc]

/-- The five saved registers, `rbp` on top. -/
abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x28#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K))))

abbrev BlankS (r : BitVec 64) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  8 ?@ (r - 0x28#64)
    ⋆ (8 ?@ (r - 0x20#64)
    ⋆ (8 ?@ (r - 0x18#64)
    ⋆ (8 ?@ (r - 0x10#64)
    ⋆ (8 ?@ (r - 0x8#64) ⋆ K))))

/-- The memory at every label: the callee's return-address slot, its
reservation, the data, the `kx` cells, the frame `FR`, the rest. -/
abbrev T (k : Nat) (x : LfGenArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ (DataW t₀
    ⋆ (KxW x t₀ ⋆ FR (Rest x.R ra t₀))))

/-- `W[buf_idx]` and `W[1 - buf_idx]`. -/
abbrev Wb (t₀ : MachineData) : BitVec 64 := arg2 t₀ + K (8192 * lfBuf t₀)

/-- The registers the procedure keeps after the prologue. -/
abbrev Regs (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x28#64 ∧ s.regs.get64 .rbp = r - 8#64
    ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .r14 = arg1 t₀ ∧ s.regs.get64 .rbx = arg2 t₀
    ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13

/-- The first loop (`k = i - 1`, `i = rsi`). -/
abbrev LoopA (x : LfGenArgs) (t₀ s : MachineData) : Prop :=
  let i := (s.regs.get64 .rsi).toNat
  Regs t₀ s ∧ 1 ≤ i ∧ i ≤ x.kx1
    ∧ s.regs.get64 .rcx = Wb t₀
    ∧ s.regs.get64 .rdx = arg1 t₀ + 0x13c#64 + K (0x140 * (i - 1))
    ∧ s.regs.get64 .rax = K (lfBuf t₀)

/-- The second loop (`k = rax + 32`). -/
abbrev LoopB (x : LfGenArgs) (t₀ s : MachineData) : Prop :=
  let k := (s.regs.get64 .rax + 32#64).toNat
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r - 0x28#64 ∧ s.regs.get64 .rbp = r - 8#64
    ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13 ∧ k < x.kx0
    ∧ s.regs.get64 .rbx = arg2 t₀ - K (8192 * lfBuf t₀) + 0x3f04#64
    ∧ s.regs.get64 .r14 = arg1 t₀ + 0x3c#64 + K (0x140 * k)

abbrev table (k : Nat) (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    Label → MachineData → Prop
  | "sbr_lf_gen", s => s = t₀ ∧ LfGenC x t₀
      ∧ (t₀.dmem =⋆ T k x ra t₀ (BlankS (t₀.regs.get64 .rsp)))
  | "sbr_lf_gen.c", s => LfGenC x t₀ ∧ Regs t₀ s
      ∧ s.regs.get64 .r12 = ((arg3 t₀).setWidth 32).setWidth 64
      ∧ s.regs.get64 .rsi = arg1 t₀
      ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.m1", s => LfGenC x t₀ ∧ Regs t₀ s
      ∧ s.regs.get64 .r12 = ((arg3 t₀).setWidth 32).setWidth 64
      ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.La190", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a1", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a2", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a3", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a4", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a5", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a6", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a7", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.a8", s => LfGenC x t₀ ∧ LoopA x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.La588", s => LfGenC x t₀ ∧ Regs t₀ s ∧ s.regs.get64 .rax = K (lfBuf t₀)
      ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.La5b0", s => LfGenC x t₀ ∧ LoopB x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.b1", s => LfGenC x t₀ ∧ LoopB x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.b2", s => LfGenC x t₀ ∧ LoopB x t₀ s ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.La6ba", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x28#64
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64
      ∧ s.regs.get64 .r13 = t₀.regs.get64 .r13
      ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | "sbr_lf_gen.done", s =>
      s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp
      ∧ SavedRegs t₀ s
      ∧ (s.dmem =⋆ T k x ra t₀ (Saved t₀))
  | _, _ => False

/-- The variant: 300 before the loops, `200 - i` in the first loop, 100 at
its exit, `(-rax)` (iterations left) in the second loop, 0 at the exit. -/
abbrev var : Label → MachineData → Nat
  | "sbr_lf_gen", _ => 300
  | "sbr_lf_gen.c", _ => 300
  | "sbr_lf_gen.m1", _ => 300
  | "sbr_lf_gen.La190", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a1", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a2", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a3", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a4", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a5", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a6", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a7", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.a8", s => 200 - (s.regs.get64 .rsi).toNat
  | "sbr_lf_gen.La588", _ => 100
  | "sbr_lf_gen.La5b0", s => 64 - (s.regs.get64 .rax + 32#64).toNat
  | "sbr_lf_gen.b1", s => 64 - (s.regs.get64 .rax + 32#64).toNat
  | "sbr_lf_gen.b2", s => 64 - (s.regs.get64 .rax + 32#64).toNat
  | "sbr_lf_gen.La6ba", _ => 0
  | "sbr_lf_gen.done", _ => 0
  | _, _ => 2 ^ 64

/-- What the exit block leaves. -/
abbrev Post' (k : Nat) (x : LfGenArgs) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ 8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ (DataW t₀
    ⋆ (KxW x t₀ ⋆ Saved t₀ (8 ?@ r ⋆ x.R)))))

macro "grind_cells'" : tactic =>
  `(tactic| grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false)
      [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod])

/-- The block obligation of `ProcSpec.of_cfg_post` at label `l` of `body`. -/
abbrev BlockOb (k : Nat) (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k x ra t₀ s) ⦄

/-! ## Local lemmas -/

-- `Mem.Blocks.Inside.self_off` (with its scoped `grind` pattern) and the `inc`
-- rule `MachineWP.inc_reg_w64_spec` are in `Kraken.Rules.HelperLemmas`.
open scoped Kraken.HelperLemmas.SelfOff

omit [CodeEnv] in
/-- A stretch of `X_low` and a stretch of `W` inside the data. -/
theorem DataW_carve (t : MachineData) (xb wb : BitVec 64) (nx nw : Nat)
    (hx : (xb - arg1 t).toNat + nx ≤ 10240) (hw : (wb - arg2 t).toNat + nw ≤ 16384) :
    ∃ H, DataW t = Blocks [(xb, nx), (wb, nw)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex hx (by omega)
  obtain ⟨H2, e2⟩ := Block.carve_ex hw (by omega)
  refine ⟨H1 ⋆ H2, ?_⟩
  simp only [DataW, Blocks]
  rw [e1, e2]
  rcases nx with _ | nx <;> rcases nw with _ | nw <;> ac_rfl

omit [CodeEnv] in
theorem lf_off_x (X : BitVec 64) (a b : Nat) (ha : a ≤ 9920) (hb : b ≤ 224) :
    (X + 0x13c#64 + K a + (K b - 0xfc#64) - X).toNat = a + b + 64 := by
  bv_omega

omit [CodeEnv] in
theorem lf_off_w (W I : BitVec 64) (a b i : Nat) (hi : I.toNat = i) (h1 : 1 ≤ i) (h2 : i ≤ 32)
    (ha : a ≤ 8192) (hb : b ≤ 0x1c00) :
    (W + K a + I * 8#64 + (K b - 8#64) - W).toNat = a + 8 * i - 8 + b := by
  bv_omega

omit [CodeEnv] in
/-- The first loop's piece `p`: `X_low[k][8 + 8p .. 16 + 8p)` (32 bytes at
`rdx - 0xfc + 32p`) and rows `4p .. 4p+3` of column `k` of `W[buf]` (0x308
bytes at `rcx + 8 rsi - 8 + 0x400p`) lie inside `X_low` and `W`. -/
theorem lfA_bounds (X W r d I : BitVec 64) (B i p : Nat) (hB : B ≤ 1) (hi : I.toNat = i)
    (h1 : 1 ≤ i) (h2 : i ≤ 32) (hp : p < 8)
    (hr : r = W + K (8192 * B)) (hd : d = X + 0x13c#64 + K (0x140 * (i - 1))) :
    (d + (K (0x20 * p) - 0xfc#64) - X).toNat + 32 ≤ 10240
    ∧ (r + I * 8#64 + (K (0x400 * p) - 8#64) - W).toNat + 0x308 ≤ 16384 := by
  subst hr hd
  have hB' : 8192 * B ≤ 8192 := by omega
  refine ⟨?_, ?_⟩
  · rw [lf_off_x X _ _ (by omega) (by omega)]; omega
  · rw [lf_off_w W I _ _ i hi h1 h2 hB' (by omega)]; omega

/-- The straight-line vector run of a piece (16 `vmovss`) on the carved
blocks `bs` with the rest `G` of the memory: the `.ds` recipe of
`QmfSynthesis` (registers unchanged, the same memory shape). -/
macro "lf_run" : tactic => `(tactic| (
  vcgen
  all_goals call_simp
  all_goals try dsimp only at *
  all_goals opaque_stores
  all_goals try simp only [AddrIndex.offset64, Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat,
    BitVec.add_zero, Int64.toBitVec_neg_ofNat_norm, Width.bytes] at *
  all_goals try subst_vars
  all_goals grind_cells'))

set_option hygiene false in
/-- Piece `p` of the first loop's body, `cx`/`cw` the displacements of its
`X_low` and `W` stretches from `rdx` and `rcx + 8 rsi`. -/
macro "lfA_piece " p:term:max cx:term:max cw:term:max : tactic => `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, hL, hm⟩, hn⟩ := hs₀
  clear hc
  have hL' := hL
  obtain ⟨⟨hrsp, hrbp, h15, h14, hbx⟩, hi1, hi2, hrcx, hrdx, hrax⟩ := hL'
  obtain ⟨hb1, hb2⟩ := lfA_bounds (arg1 t₀) (arg2 t₀) _ _ (s₀.regs.get64 .rsi) (lfBuf t₀) _ $p
    hC.1 rfl hi1 (by have := hC.2.2; omega) (by decide) hrcx hrdx
  simp only [K, Nat.reduceMul, Nat.mul_zero, BitVec.reduceSub] at hb1 hb2
  obtain ⟨H, eH⟩ := DataW_carve t₀ (s₀.regs.get64 .rdx + $cx)
    (s₀.regs.get64 .rcx + s₀.regs.get64 .rsi * 8#64 + $cw) 32 0x308 hb1 hb2
  simp only [T, eH] at hm
  generalize hG : (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
    ⋆ (H ⋆ (KxW x t₀ ⋆ Saved t₀ (Rest x.R ra t₀))))) = G
  have hm2 : s₀.dmem =⋆ Blocks [(s₀.regs.get64 .rdx + $cx, 32),
      (s₀.regs.get64 .rcx + s₀.regs.get64 .rsi * 8#64 + $cw, 0x308)] ⋆ G := by
    subst hG; exact Mem.ac hm
  clear hm
  refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs ∧ (s.dmem =⋆ Blocks
      [(s₀.regs.get64 .rdx + $cx, 32),
      (s₀.regs.get64 .rcx + s₀.regs.get64 .rsi * 8#64 + $cw, 0x308)] ⋆ G)) ?_ ?_
  · lf_run
  · rintro s ⟨hr, hmem⟩
    refine ⟨⟨hC, ?_, ?_⟩, ?_⟩
    · simp only [LoopA, Regs, hr]; exact hL
    · subst hG; simp only [T]; rw [eH]; exact Mem.ac hmem
    · rw [← hn]; simp only [var, hr]; exact Nat.le_refl _))

theorem blk_La190 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.La190" := by
  cfg_block
  measure_hb "La190"
    lfA_piece 0 0xffffffffffffff04#64 0xfffffffffffffff8#64

theorem blk_a1 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a1" := by
  cfg_block
  measure_hb "a1"
    lfA_piece 1 0xffffffffffffff24#64 0x3f8#64

theorem blk_a2 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a2" := by
  cfg_block
  measure_hb "a2"
    lfA_piece 2 0xffffffffffffff44#64 0x7f8#64

theorem blk_a3 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a3" := by
  cfg_block
  measure_hb "a3"
    lfA_piece 3 0xffffffffffffff64#64 0xbf8#64

theorem blk_a4 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a4" := by
  cfg_block
  measure_hb "a4"
    lfA_piece 4 0xffffffffffffff84#64 0xff8#64

theorem blk_a5 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a5" := by
  cfg_block
  measure_hb "a5"
    lfA_piece 5 0xffffffffffffffa4#64 0x13f8#64

theorem blk_a6 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a6" := by
  cfg_block
  measure_hb "a6"
    lfA_piece 6 0xffffffffffffffc4#64 0x17f8#64

theorem blk_a7 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a7" := by
  cfg_block
  measure_hb "a7"
    lfA_piece 7 0xffffffffffffffe4#64 0x1bf8#64

omit [CodeEnv] in
theorem lf_off_x2 (X : BitVec 64) (a b : Nat) (ha : a ≤ 9920) (hb : b ≤ 32) :
    (X + 0x3c#64 + K a + (K b - 0x3c#64) - X).toNat = a + b := by
  bv_omega

omit [CodeEnv] in
theorem lf_off_w2 (W I : BitVec 64) (a b k : Nat) (hk : (I + 32#64).toNat = k) (hk32 : k < 32)
    (ha : a ≤ 8192) (hb : b ≤ 0x400) :
    (W - K a + 0x3f04#64 + I * 8#64 + (K b - 0x604#64) - W).toNat = 0x3800 + 8 * k + b - a := by
  bv_omega

omit [CodeEnv] in
/-- The second loop's piece `q`: `X_low[k][4q .. 4q+4)` (32 bytes at
`r14 - 0x3c + 32q`) and rows `24 + 4q .. 27 + 4q` of column `k` of
`W[1 - buf]` (0x308 bytes at `rbx + 8 rax - 0x604 + 0x400q`). -/
theorem lfB_bounds (X W b r I : BitVec 64) (B k q : Nat) (hB : B ≤ 1)
    (hk : (I + 32#64).toNat = k) (hk32 : k < 32) (hq : q < 2)
    (hb : b = W - K (8192 * B) + 0x3f04#64) (hr : r = X + 0x3c#64 + K (0x140 * k)) :
    (r + (K (0x20 * q) - 0x3c#64) - X).toNat + 32 ≤ 10240
    ∧ (b + I * 8#64 + (K (0x400 * q) - 0x604#64) - W).toNat + 0x308 ≤ 16384 := by
  subst hb hr
  refine ⟨?_, ?_⟩
  · rw [lf_off_x2 X _ _ (by omega) (by omega)]; omega
  · rw [lf_off_w2 W I _ _ k hk hk32 (by omega) (by omega)]; omega

set_option hygiene false in
/-- Piece `q` of the second loop's body. -/
macro "lfB_piece " q:term:max cx:term:max cw:term:max : tactic => `(tactic| (
  intro n
  refine Triple.pin fun s₀ hs₀ => ?_
  obtain ⟨⟨hC, hL, hm⟩, hn⟩ := hs₀
  clear hc
  have hL' := hL
  obtain ⟨hrsp, hrbp, h15, h13, hk0, hrbx, hr14⟩ := hL'
  obtain ⟨hb1, hb2⟩ := lfB_bounds (arg1 t₀) (arg2 t₀) _ _ (s₀.regs.get64 .rax) (lfBuf t₀) _ $q
    hC.1 rfl (by have := hC.2.1; omega) (by decide) hrbx hr14
  simp only [K, Nat.reduceMul, Nat.mul_zero, BitVec.reduceSub] at hb1 hb2
  obtain ⟨H, eH⟩ := DataW_carve t₀ (s₀.regs.get64 .r14 + $cx)
    (s₀.regs.get64 .rbx + s₀.regs.get64 .rax * 8#64 + $cw) 32 0x308 hb1 hb2
  simp only [T, eH] at hm
  generalize hG : (8 ?@ (t₀.regs.get64 .rsp - 0x30#64) ⋆ (Reserve k (t₀.regs.get64 .rsp - 0x30#64)
    ⋆ (H ⋆ (KxW x t₀ ⋆ Saved t₀ (Rest x.R ra t₀))))) = G
  have hm2 : s₀.dmem =⋆ Blocks [(s₀.regs.get64 .r14 + $cx, 32),
      (s₀.regs.get64 .rbx + s₀.regs.get64 .rax * 8#64 + $cw, 0x308)] ⋆ G := by
    subst hG; exact Mem.ac hm
  clear hm
  refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs ∧ (s.dmem =⋆ Blocks
      [(s₀.regs.get64 .r14 + $cx, 32),
      (s₀.regs.get64 .rbx + s₀.regs.get64 .rax * 8#64 + $cw, 0x308)] ⋆ G)) ?_ ?_
  · lf_run
  · rintro s ⟨hr, hmem⟩
    refine ⟨⟨hC, ?_, ?_⟩, ?_⟩
    · simp only [LoopB, hr]; exact hL
    · subst hG; simp only [T]; rw [eH]; exact Mem.ac hmem
    · rw [← hn]; simp only [var, hr]; exact Nat.le_refl _))

theorem blk_La5b0 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.La5b0" := by
  cfg_block
  measure_hb "La5b0"
    lfB_piece 0 0xffffffffffffffc4#64 0xfffffffffffff9fc#64

theorem blk_b1 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.b1" := by
  cfg_block
  measure_hb "b1"
    lfB_piece 1 0xffffffffffffffe4#64 0xfffffffffffffdfc#64

set_option maxHeartbeats 100000 in
theorem blk_La6ba (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.La6ba" := by
  cfg_block
  measure_hb "La6ba"
    intro n
    clear hc
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells'

set_option maxHeartbeats 60000 in
theorem blk_done (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.done" := by
  cfg_block
  measure_hb "done"
    intro n
    clear hc
    vcgen
    all_goals simp only [Rest] at *
    all_goals call_simp
    all_goals grind_cells'

set_option maxHeartbeats 180000 in
theorem blk_entry (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen" := by
  cfg_block
  measure_hb "entry"
    intro n
    clear hc
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try simp only [BitVec.sub_sub_eight, BitVec.reduceAdd] at *
    all_goals try dsimp only at *
    all_goals grind_cells'

omit [CodeEnv] in
theorem DataW_carve_memset (t : MachineData) (a : BitVec 64) (n : Nat) (ha : a = arg1 t)
    (hn : n = 10240) : ∃ H, DataW t = Blocks [(a, n)] ⋆ H :=
  ⟨16384 ?@ arg2 t, by subst ha hn; simp only [DataW, Blocks]⟩

set_option maxHeartbeats 40000 in
theorem blk_c (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.c" := by
  cfg_block
  measure_hb "c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hrsp, hrbp, h15, h14, hbx, h13⟩, h12, hrsi, hm⟩, hn⟩ := hs₀
    vcgen [MachineWP.call_proc_spec_at (DataW t₀, KxW x t₀ ⋆ Saved t₀ (Rest x.R ra t₀)) "memset"
      (Kraken.Executable.ProcSpec.widen (k := k) hc (Nat.le_refl k) (by omega))]
    clear hc
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by rw [hrsp]; show _ - 8#64 = _; bv_omega) _
         · exact True.intro
         · apply DataW_carve_memset <;> grind_cells'
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxHeartbeats 400000 in
theorem blk_m1 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.m1" := by
  cfg_block
  measure_hb "m1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, h12, hm⟩, hn⟩ := hs₀
    clear hc
    have hm' := hm
    simp only [T, KxW_open] at hm'
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals grind_cells'

/-- The two bounds-check traps (`ud1`): their table is `False`, so each
block that falls into one must show the edge unreachable. -/
theorem blk_t1 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.t1" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => False.elim hs.1

theorem blk_t2 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.t2" := by
  cfg_block
  intro n
  exact Triple.intro fun s hs => False.elim hs.1

set_option maxHeartbeats 150000 in
theorem blk_a8 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.a8" := by
  cfg_block
  measure_hb "a8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hL, hm⟩, hn⟩ := hs₀
    clear hc
    have hm' := hm
    simp only [T, KxW_open] at hm'
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals grind_cells'

set_option maxHeartbeats 70000 in
theorem blk_La588 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.La588" := by
  cfg_block
  measure_hb "La588"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, hrax, hm⟩, hn⟩ := hs₀
    clear hc
    have hm' := hm
    simp only [T, KxW_open] at hm'
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals grind_cells'

omit [CodeEnv] in
/-- The carry of `cmp w, r` (`r - w`): `r < w` unsigned. -/
theorem lf_cf (r w : BitVec 64) (a b : Nat) (hr : r.toNat = a) (hw : w.toNat = b) :
    ((((r - w).toNat : Int) != (r.toNat : Int) - (w.toNat : Int))) = decide (a < b) := by
  subst hr hw
  rw [BitVec.toNat_sub]
  by_cases h : r.toNat < w.toNat
  · simp only [h, decide_true, bne_iff_ne, ne_eq]; omega
  · simp only [h, decide_false, bne_eq_false_iff_eq]; omega

omit [CodeEnv] in
/-- A loaded small `int`, zero-extended (`mov m32, r32`). -/
theorem lf_w (n : Nat) (h : n ≤ 32) :
    (BitVec.setWidth 64 (BitVec.ofInt 32 (n : Int))).toNat = n := by
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  omega

omit [CodeEnv] in
/-- The zero flag of `inc %rax` in the second loop: zero exactly at `k = 31`. -/
theorem lf_zf (A : BitVec 64) (k : Nat) (hk : (A + 32#64).toNat = k) (h : k < 32) :
    (A + 1#64 == BitVec.zero 64) = decide (k = 31) := by
  rw [show BitVec.zero 64 = 0#64 from rfl]
  by_cases h31 : k = 31
  · simp only [h31, decide_true, beq_iff_eq]
    subst h31; bv_omega
  · simp only [h31, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h31; bv_omega

omit [CodeEnv] in
/-- The second loop's counter `A = rax` (`k = A + 32 < 32`): `lea 0x21(%rax)`
is `k + 1`, `inc %rax` gives `k + 1` and is zero exactly at `k = 31`. -/
theorem lfB_ctrl (A : BitVec 64) (k : Nat) (hk : (A + 32#64).toNat = k) (h : k < 32) :
    (A + 33#64).toNat = k + 1 ∧ (A + 1 + 32#64).toNat = k + 1 ∧ (A + 1 = 0#64 ↔ k = 31)
      ∧ A + 33#64 = A + 1 + 32#64 := by
  refine ⟨?_, ?_, ⟨fun e => ?_, fun e => ?_⟩, ?_⟩ <;> bv_omega

omit [CodeEnv] in
theorem lfB_r14 (X r : BitVec 64) (k : Nat) (hr : r = X + 60#64 + K (320 * k)) (h : k < 32) :
    320#64 + r = X + 60#64 + K (320 * (k + 1)) := by
  have e : K (320 * (k + 1)) = K (320 * k) + 320#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [K, BitVec.toNat_ofNat, BitVec.toNat_add]
    omega
  rw [e, hr]; ac_rfl

set_option maxHeartbeats 90000 in
theorem blk_b2 (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k)
    (x : LfGenArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "sbr_lf_gen.b2" := by
  cfg_block
  measure_hb "b2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hL, hm⟩, hn⟩ := hs₀
    clear hc
    have hm' := hm
    simp only [T, KxW_open] at hm'
    have hL' := hL
    obtain ⟨-, -, -, -, hk0, -, hr14⟩ := hL'
    obtain ⟨e1, e2, e3, e4⟩ := lfB_ctrl (s₀.regs.get64 .rax) _ rfl (by have := hC.2.1; omega)
    have e5 := lfB_r14 _ _ _ hr14 (by have := hC.2.1; omega)
    have hk32 : (s₀.regs.get64 .rax + 32#64).toNat < 32 := by have := hC.2.1; omega
    have hld : loadInt s₀.dmem (s₀.regs.get64 .r15 + 84#64) 4
        = some (Int.ofBytes (Int.toBytes 4 (x.kx0 : Int))) := by
      rw [hL.2.2.1]
      exact Mem.Val.loadInt hm' (Mem.Split.right (Mem.Split.right (Mem.Split.right
        (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have ew := lf_w _ hC.2.1
    have ecf := lf_cf _ _ _ _ e1 ew
    have ezf := lf_zf (s₀.regs.get64 .rax) _ rfl hk32
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals try simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.setWidth_eq]
      at *
    all_goals try simp only [hld, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    all_goals try simp only [CondCode.interp_nc, CondCode.interp_nz, StatusFlags.cf_from_result,
      StatusFlags.zf_from_result, BitVec.unsigned_eq,
      ecf, ezf, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not]
      at *
    -- the fall-through into the trap: `k + 1 < kx[0] ≤ 32` and `k = 31`
    case vc4 => exfalso; have := hC.2.1; omega
    case vc2 =>
      left
      refine Table.ofLabels_at (l := "sbr_lf_gen.La6ba") ?_
      refine ⟨by decide, ?_, ?_⟩
      all_goals try dsimp only at *
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ↓reduceIte] at *
      · exact ⟨hL.1, hL.2.1, hL.2.2.2.1, hm⟩
      · left; omega
    case vc3 =>
      left
      refine Table.ofLabels_at (l := "sbr_lf_gen.La5b0") ?_
      refine ⟨by decide, ?_, ?_⟩
      all_goals try dsimp only at *
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ↓reduceIte] at *
      · exact ⟨hC, ⟨hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, by rw [e2]; omega, hL.2.2.2.2.2.1,
          by rw [e2]; exact e5⟩, hm⟩
      · left; rw [e2]; omega

/-! ## The spec -/

omit [CodeEnv] in
theorem lf_reserve_frame (k : Nat) {r : BitVec 64} (hw : 0x30 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x30 + k) r ⋆ K
      = 8 ?@ (r - 0x30#64) ⋆ (Reserve k (r - 0x30#64) ⋆ (0x28 ?@ (r - 0x28#64) ⋆ K)) :=
  Reserve_split_frame 0x30 k (by decide) r (by omega) K

omit [CodeEnv] in
/-- A block of `n + 8` bytes is 8 bytes and the rest (`QmfSynthesis` has the
same lemma in its own namespace; a library candidate). -/
theorem Block.split8 (a : BitVec 64) (n : Nat) (hw : n + 8 ≤ 2 ^ 64) :
    (n + 8) ?@ a = 8 ?@ a ⋆ n ?@ (a + 8#64) := by
  rw [Nat.add_comm, Mem.Block.split a 8 n (by omega)]

omit [CodeEnv] in
theorem lf_frame_cells (r : BitVec 64) (K : Mem 64 → Prop) :
    0x28 ?@ (r - 0x28#64) ⋆ K = BlankS r K := by
  rw [show (40 ?@ (r - 0x28#64) : Mem 64 → Prop) = (32 + 8) ?@ (r - 0x28#64) from rfl,
    Block.split8 _ 32 (by decide), show r - 0x28#64 + 8#64 = r - 0x20#64 by bv_omega]
  rw [show (32 ?@ (r - 0x20#64) : Mem 64 → Prop) = (24 + 8) ?@ (r - 0x20#64) from rfl,
    Block.split8 _ 24 (by decide), show r - 0x20#64 + 8#64 = r - 0x18#64 by bv_omega]
  rw [show (24 ?@ (r - 0x18#64) : Mem 64 → Prop) = (16 + 8) ?@ (r - 0x18#64) from rfl,
    Block.split8 _ 16 (by decide), show r - 0x18#64 + 8#64 = r - 0x10#64 by bv_omega]
  rw [show (16 ?@ (r - 0x10#64) : Mem 64 → Prop) = (8 + 8) ?@ (r - 0x10#64) from rfl,
    Block.split8 _ 8 (by decide), show r - 0x10#64 + 8#64 = r - 0x8#64 by bv_omega]
  simp only [BlankS, Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem lf_Saved_blank (t₀ : MachineData) (K : Mem 64 → Prop) :
    Mem.Entails (Saved t₀ K) (BlankS (t₀.regs.get64 .rsp) K) :=
  Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.refl _)))))

omit [CodeEnv] in
theorem LfGenF_eq (x : LfGenArgs) (t : MachineData) :
    LfGenF x t ⋆ x.R = DataW t ⋆ (KxW x t ⋆ x.R) := by
  simp only [LfGenF, DataW, KxW, Std.ExtHashMap.sep_assoc]

theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32) (hc : MemsetSpec k) :
    LfGenSpec k := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table k)
    (Post' k) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
  · intro x ra t₀ _ l blk hblk
    have hmem := Program.isSome_blockAt body l
    cfg_view hblk as hview
    rw [hblk, hview] at hmem
    replace hmem := hmem.symm
    clear hview
    simp only [Option.isSome_some, List.map_cons, List.map_nil, List.contains_cons,
      List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at hmem
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hmem
    · exact blk_entry k hk hc x ra t₀ blk hblk
    · exact blk_c k hk hc x ra t₀ blk hblk
    · exact blk_m1 k hk hc x ra t₀ blk hblk
    · exact blk_La190 k hk hc x ra t₀ blk hblk
    · exact blk_a1 k hk hc x ra t₀ blk hblk
    · exact blk_a2 k hk hc x ra t₀ blk hblk
    · exact blk_a3 k hk hc x ra t₀ blk hblk
    · exact blk_a4 k hk hc x ra t₀ blk hblk
    · exact blk_a5 k hk hc x ra t₀ blk hblk
    · exact blk_a6 k hk hc x ra t₀ blk hblk
    · exact blk_a7 k hk hc x ra t₀ blk hblk
    · exact blk_a8 k hk hc x ra t₀ blk hblk
    · exact blk_t1 k hk hc x ra t₀ blk hblk
    · exact blk_La588 k hk hc x ra t₀ blk hblk
    · exact blk_La5b0 k hk hc x ra t₀ blk hblk
    · exact blk_b1 k hk hc x ra t₀ blk hblk
    · exact blk_b2 k hk hc x ra t₀ blk hblk
    · exact blk_t2 k hk hc x ra t₀ blk hblk
    · exact blk_La6ba k hk hc x ra t₀ blk hblk
    · exact blk_done k hk hc x ra t₀ blk hblk
  · -- hpre
    rintro x ra t ⟨hm, hC⟩
    refine ⟨rfl, hC, ?_⟩
    have hw := CallPre.le hm
    rw [LfGenF_eq] at hm
    simp only [CallPre, lfNeed] at hm
    rw [lf_reserve_frame k hw] at hm
    simp only [T, Rest]
    rw [← lf_frame_cells]
    exact Mem.ac hm
  · -- hpost
    rintro x ra t₀ s ⟨h0, -⟩ ⟨h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hm' := Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (lf_Saved_blank t₀ _)))) _ hm
    rw [← lf_frame_cells] at hm'
    rw [LfGenF_eq]
    rw [show lfNeed k = 0x30 + k from rfl, lf_reserve_frame k (CallPre.le h0)]
    exact Mem.ac hm'

end Kraken.Examples.Sbr.LfGen
