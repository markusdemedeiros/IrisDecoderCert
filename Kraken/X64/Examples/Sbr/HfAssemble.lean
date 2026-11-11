import Kraken.X64.Examples.Sbr.HfAssemble.Part1
import Kraken.X64.Examples.Sbr.HfAssemble.Part2

/-!
# `sbr_hf_assemble` as a `ProcSpec`

Memory safety of `sbr_hf_assemble(Y1, X_high, sbr, ch_data, e_a)` (FFmpeg
`aacsbr_template.c`, `-c opt` object). The proof is per block: a label table (`table`),
a variant (`var`), and one theorem `blk_<label>` per block; `spec` dispatches on labels.
The specification (`HfAssembleSpec k fs`: footprint `HfF`/`HfFPost`, side conditions
`HfC`, callees `HfCallees k fs`) is in `Spec.lean`.

Notes:
* The function is memory safe under the `SbrWF` clauses in `HfC`: `1 ≤ m[1] ≤ 48`,
  `kx[1] + m[1] ≤ 64`, `bs_num_env ≤ 8`, `t_env[e] ≤ 19` for `e ≤ bs_num_env` and
  `t_env_num_env_old ≤ 19`, `f_indexnoise ≤ 515`, `f_indexsine < 4`, the stack 16-aligned
  at the call, `sbr`/`ch_data` 16-aligned (aligned `vmovaps` spills, `hf_apply_noise`
  operands), the `ps_noise*` constants aligned, `Y1 = Y[ypos]` with `ypos ≤ 1`.
* Note A1: the envelope borders reach `numTimeSlots + 3 = 19`, not 16. With `t_env ≤ 19`
  the time-slot index `i < 2·t_env[e+1]` reaches 37: `Y1` row 37 (of 38), `X_high` row
  `i + 2 ≤ 39` (of 40), `g_temp`/`q_temp` row `h_SL + i ≤ 41` (of 42); every access stays
  in its array.
* Five `ud1` traps (compiler-inserted bounds checks: `kx ≥ 65`, `kx == 64` in the sine
  add, `f_indexsine ≥ 4`, the envelope loop reaching `e == 8`, the unrolled `s_m` copy
  ending with count ≠ 8) are not reached under `HfC`; the table excludes them.
* The `hf_apply_noise` window (`32 * ⌈m/4⌉` bytes from `Y1[i] + kx`, see `a2_row_spill`)
  is carved (`Lb1a0_carve`) from `Y1` and the second block of `HfData`.
  For `ypos = 1` that block lies in `g_temp`, which the footprint owns anyway, so there the
  24-byte bound rests on `Lb1a0_carve` citing `a2_row_spill` and on the row-crossing
  discipline: this file crosses a row of `Y` only through `a2_row_spill`
  (`scripts/sbr/tv/a2_discipline.py`), not on the footprint. Every other access to `Y1` stays inside one row (`Lb01d_carve`,
  `hf_inY*`: column `kx + j` with `j < m`, `kx + m ≤ 64`).
* The callees are assumed through their `LeafSpec`s (`HfGFiltSpec`,
  `HfApplyNoise{0,1,2,3}Spec`, `memcpy`), passed as `HfCallees k fs`.
* The noise call `call *0x60230(%r10,%rax,8)` indexes `sbr->dsp.hf_apply_noise` by
  `f_indexsine`; the proof abstracts the entry over the index (`hfNoiseFn fs q`,
  `hfNoiseK q`) so one symbolic execution covers all four callees.
* The `ud1` after `cmp $8,%rdi` in `Lb400` is discharged by a `False`-precondition rule
  for `ud1` (`MachineWP.ud1_spec`; the edge is unreachable: `rdi < bs_num_env ≤ 8`).
* Library (`Kraken.Rules.HelperLemmas`), first written here: the `ud1` and `inc` rules, the
  variable-index cell-array load (`Mem.CellArr.loadInt`), two stores into a view
  (`Mem.Block.storeInt_val2`), loads past a stack store (`Mem.loadInt_storeInt_sub_lo`/`_hi`),
  `Mem.loadInt_isSome_storeInt`, `Mem.Val.loadInt_lo4`, `Int.toBytes_add`, the `jl`/`jae`
  readings `CondCode.interp_l_sub32`/`64`, `CondCode.interp_nc_sub8`/`64`.

Costs (`measure_hb`, thousands of heartbeats; each block's `maxHeartbeats` is about twice
its measure). Blocks above one million, clean-up candidates:
* `Lb08f` (2.27M): about 20 goals, each running the generic `simp … at *` over the 45-cell
  frame view, plus per-load simps and the `.LCPI17_*` reads unfolding `DataW`.
* `La8f6` (1.75M): `grind` on about 28 register/value goals with the whole memory context
  in scope (no single unfolding hotspot; clearing the memory hypothesis for non-memory
  goals would help).
* `p1` (1.61M): the prologue spills, the generic closer over the full frame per cell goal.
* `Lb01d` (1.48M), `Lb1a0` (1.23M): the call blocks; symbolic execution over the frame
  view plus the callee frame, then `grind` for the footprint carve and the post.
* `m1` (1.96M): the `.LCPI17_12` load after three stores needs the store peel plus a full
  `DataW` unfold (about 0.6M); a variant of `hf_lcpi4` that finds `DataW` anywhere
  in the frame would remove it.
* `r0` (1.81M): three stores into the frame split at `s38`, closed by `grind`; a closed
  frame lemma would replace it.
* `a1` (1.21M): five `.LCPI17_*` loads, each unfolding `DataW`.
* `r8` (1.03M, was 0.83M before M4b; not profiled): the `Lb820` entry it jumps to now has `HfC` (for `Post'`
  to turn `DataW` back into `HfData x.ypos`); the rest as `r0`.
(M4b: measures after the `HfData`/`ypos` change and `t_env ≤ 19`; full check 783 s, peak 11.0 GB.)
Deviation from the proof-shape rules: `bv_omega` runs inside block proofs in the overrides
of `c4`–`c7`, `Labf0`, `Lac90`, `Lad30`, `Ladcc`, `Lb140`, `Lb16c` (proved and left as is;
the clean-up is closed address lemmas as in `hf_rsp_*`).
-/

open Kraken
open Kraken.SysV
open Mem

open Kraken.X64.Parser
open Std.WP
open MachineWP
open scoped Kraken.FrameLemmas.Int32Nat
open scoped Kraken.HelperLemmas.Bytes16

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.HfAssemble

variable [CodeEnv]

theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns)
    (hc : HfCallees k fs) : HfAssembleSpec k fs := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table k fs)
    (Post' k fs) var (hblocks := ?_) (hpre := ?_) (hpost := ?_)
    -- `hwf`, the labels are distinct: the kernel compares one `Nat` per label (its UTF-8 bytes
    -- as a base-256 numeral), about 6x cheaper than comparing the strings pairwise.
    (hwf := ⟨List.Pairwise.of_map (S := fun a b : Nat => a ≠ b)
      (fun s : String => s.toByteArray.data.toList.foldl (fun n b => n * 256 + b.toNat) 0)
      (fun _ _ h e => h (by subst e; rfl)) (by decide +kernel)⟩)
  · -- each block by its label's membership in the label list (`hall`), no case split
    intro x ra t₀ _ l blk hblk
    have hmem := Program.blockAt_mem_labels hblk
    rw [Program.labels_eq_view] at hmem
    cfg_view hblk as hview
    rw [hview] at hmem
    clear hview
    simp -implicitDefEqProofs only [List.map_cons, List.map_nil] at hmem
    have hall : ∀ l ∈ (["sbr_hf_assemble", "sbr_hf_assemble.p1", "sbr_hf_assemble.p2", "sbr_hf_assemble.r0",
        "sbr_hf_assemble.r0c", "sbr_hf_assemble.r1", "sbr_hf_assemble.r1c", "sbr_hf_assemble.r2",
        "sbr_hf_assemble.r2c", "sbr_hf_assemble.r3", "sbr_hf_assemble.r3c", "sbr_hf_assemble.r4",
        "sbr_hf_assemble.r4c", "sbr_hf_assemble.r5", "sbr_hf_assemble.r5c", "sbr_hf_assemble.r6",
        "sbr_hf_assemble.r6c", "sbr_hf_assemble.r7", "sbr_hf_assemble.r7c", "sbr_hf_assemble.r8",
        "sbr_hf_assemble.La8e1", "sbr_hf_assemble.La8ea", "sbr_hf_assemble.La8f6", "sbr_hf_assemble.s0",
        "sbr_hf_assemble.La970", "sbr_hf_assemble.c0", "sbr_hf_assemble.d0", "sbr_hf_assemble.x0",
        "sbr_hf_assemble.La9c2", "sbr_hf_assemble.s1", "sbr_hf_assemble.Laa10", "sbr_hf_assemble.c1",
        "sbr_hf_assemble.d1", "sbr_hf_assemble.x1", "sbr_hf_assemble.Laa62", "sbr_hf_assemble.s2",
        "sbr_hf_assemble.Laab0", "sbr_hf_assemble.c2", "sbr_hf_assemble.d2", "sbr_hf_assemble.x2",
        "sbr_hf_assemble.Lab02", "sbr_hf_assemble.s3", "sbr_hf_assemble.Lab50", "sbr_hf_assemble.c3",
        "sbr_hf_assemble.d3", "sbr_hf_assemble.x3", "sbr_hf_assemble.Laba2", "sbr_hf_assemble.s4",
        "sbr_hf_assemble.Labf0", "sbr_hf_assemble.c4", "sbr_hf_assemble.d4", "sbr_hf_assemble.x4",
        "sbr_hf_assemble.Lac42", "sbr_hf_assemble.s5", "sbr_hf_assemble.Lac90", "sbr_hf_assemble.c5",
        "sbr_hf_assemble.d5", "sbr_hf_assemble.x5", "sbr_hf_assemble.Lace2", "sbr_hf_assemble.s6",
        "sbr_hf_assemble.Lad30", "sbr_hf_assemble.c6", "sbr_hf_assemble.d6", "sbr_hf_assemble.x6",
        "sbr_hf_assemble.Lad82", "sbr_hf_assemble.s7", "sbr_hf_assemble.Ladcc", "sbr_hf_assemble.c7",
        "sbr_hf_assemble.d7", "sbr_hf_assemble.Lae0d", "sbr_hf_assemble.Lae20", "sbr_hf_assemble.m1",
        "sbr_hf_assemble.m2", "sbr_hf_assemble.m3", "sbr_hf_assemble.Laf40", "sbr_hf_assemble.Lafa0",
        "sbr_hf_assemble.Lafd9", "sbr_hf_assemble.Lb000", "sbr_hf_assemble.Lb01d", "sbr_hf_assemble.g1",
        "sbr_hf_assemble.Lb08f", "sbr_hf_assemble.n2", "sbr_hf_assemble.Lb140", "sbr_hf_assemble.Lb16c",
        "sbr_hf_assemble.Lb1a0", "sbr_hf_assemble.a1", "sbr_hf_assemble.Lb248", "sbr_hf_assemble.Lb26b",
        "sbr_hf_assemble.Lb280", "sbr_hf_assemble.v1", "sbr_hf_assemble.v2", "sbr_hf_assemble.Lb340",
        "sbr_hf_assemble.w1", "sbr_hf_assemble.w2", "sbr_hf_assemble.Lb400", "sbr_hf_assemble.Lb426",
        "sbr_hf_assemble.y1", "sbr_hf_assemble.y2", "sbr_hf_assemble.y3", "sbr_hf_assemble.y4",
        "sbr_hf_assemble.y5", "sbr_hf_assemble.y6", "sbr_hf_assemble.y7", "sbr_hf_assemble.y8",
        "sbr_hf_assemble.y9", "sbr_hf_assemble.y10", "sbr_hf_assemble.y11", "sbr_hf_assemble.y12",
        "sbr_hf_assemble.y13", "sbr_hf_assemble.y14", "sbr_hf_assemble.Lb820", "sbr_hf_assemble.done",
        "sbr_hf_assemble.Lb83e", "sbr_hf_assemble.Lb843", "sbr_hf_assemble.Lb848", "sbr_hf_assemble.Lb84d"] : List Label), BlockOb k fs x ra t₀ l :=
      List.forall_mem_cons.2 ⟨blk_start k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_p1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_p2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r0c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r1c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r2c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r3c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r4 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r4c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r5 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r5c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r6c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r7 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r7c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_r8 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_La8e1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_La8ea k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_La8f6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_La970 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_La9c2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Laa10 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Laa62 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Laab0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lab02 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lab50 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Laba2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s4 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Labf0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c4 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d4 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x4 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lac42 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s5 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lac90 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c5 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d5 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x5 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lace2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lad30 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_x6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lad82 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_s7 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Ladcc k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_c7 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_d7 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lae0d k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lae20 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_m1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_m2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_m3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Laf40 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lafa0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lafd9 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb000 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb01d k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_g1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb08f k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_n2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb140 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb16c k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb1a0 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_a1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb248 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb26b k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb280 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_v1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_v2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb340 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_w1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_w2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb400 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb426 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y1 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y2 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y3 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y4 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y5 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y6 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y7 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y8 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y9 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y10 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y11 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y12 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y13 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_y14 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb820 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_done k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb83e k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb843 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb848 k hk fs hc x ra t₀,
      List.forall_mem_cons.2 ⟨blk_Lb84d k hk fs hc x ra t₀,
      List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
    exact hall l hmem blk hblk
  · -- hpre
    rintro x ra t ⟨hm, hC⟩
    refine ⟨rfl, hC, ?_⟩
    have hw := CallPre.le hm
    simp -implicitDefEqProofs only [CallPre, hfNeed] at hm
    rw [reserve_frame k hw, frame_cells] at hm
    simp -implicitDefEqProofs only [T, Rest, FA, ScW, FnW, TeW, EaW, IdxC, HfF] at hm ⊢
    rw [DataW_eq x t (hfc_ypos hC) (hfc_y1 hC)] at hm
    exact Mem.ac hm
  · -- hpost
    rintro x ra t₀ s ⟨h0, -⟩ ⟨hC, h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hm' := Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Saved_blank t₀ _))))))))) _ hm
    rw [show hfNeed k = 0x290 + k from rfl, reserve_frame k (CallPre.le h0), frame_exit]
    simp -implicitDefEqProofs only [HfFPost, ScW, FnW, TeW, EaW] at hm' ⊢
    rw [DataW_eq x t₀ (hfc_ypos hC) (hfc_y1 hC)]
    exact Mem.ac hm'

end Kraken.Examples.Sbr.HfAssemble
