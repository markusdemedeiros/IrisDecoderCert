import Kraken.X64.Examples.Sbr.ApplyTable
import Kraken.X64.Examples.Sbr.Link

/-!
# Satisfiability witnesses for `ff_aac_sbr_apply`'s precondition

`ApplyPre` (with `SbrWF`, `LayoutC` and the footprint `ApplyF`) is a long conjunction; a
contradictory conjunct would make `Apply.spec` vacuous (V1 was of this kind). Here
each of four configurations is shown satisfiable at once, at the real definitions:

* `apply_pre_sat_sce`: a started SCE (`start = 1`, `id_aac = 0`), channel 0 live with one
  envelope, channel 1 in its `av_mallocz` state;
* `apply_pre_sat_ps`: the same with parametric stereo started;
* `apply_pre_sat_cpe`: a CPE with both channels live;
* `apply_pre_sat_a3`: not downsampled with `synthesis_filterbank_samples_offset = 1600`
  (the larger `qmfVSize` window).

Each also states `SbrSlots e`, the slot hypothesis of `Link.lean`.

The memory is built by `SatIn` (a predicate holds of a memory whose addresses lie in given
intervals): `⋆` of two such memories with disjoint intervals is their union (`SatIn.sep`),
and the interval checks are Boolean checks on numerals. The ambient code is a small program
of labels behind `.align 32` cells (`wProg`, laid out by `wLayout`, valid by
`wLayout_valid`). The generic part (`wit_mem`, `wit_pre`) takes the ambient code as an
instance and needs only that the read-only constants `CstW` fit below `2 ^ 32` and the
alignment facts, so another layout (a real image) can be substituted.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open Std Std.ExtHashMap

namespace Kraken.Examples.Sbr.Witness

/-! ## Memories with addresses in given intervals -/

/-- `n` lies in one of the half-open intervals `[a, b)` of `L`. -/
def InL (n : Nat) : List (Nat × Nat) → Prop
  | [] => False
  | (a, b) :: L => (a ≤ n ∧ n < b) ∨ InL n L

theorem InL_append {n : Nat} : ∀ {L1 L2 : List (Nat × Nat)},
    InL n (L1 ++ L2) ↔ InL n L1 ∨ InL n L2
  | [], _ => by simp [InL]
  | (a, b) :: L1, L2 => by
    simp only [List.cons_append, InL, InL_append (L1 := L1), or_assoc]

/-- The intervals of `L1` and of `L2` are pairwise disjoint (a Boolean check on numerals). -/
def DisjL (L1 L2 : List (Nat × Nat)) : Bool :=
  L1.all fun p => L2.all fun q => p.2 ≤ q.1 || q.2 ≤ p.1

theorem DisjL_spec {n : Nat} {L1 L2 : List (Nat × Nat)} (h : DisjL L1 L2 = true)
    (h1 : InL n L1) (h2 : InL n L2) : False := by
  induction L1 with
  | nil => exact h1
  | cons p L1 ih =>
    obtain ⟨a, b⟩ := p
    simp only [DisjL, List.all_cons, Bool.and_eq_true] at h
    rcases h1 with h1 | h1
    · obtain ⟨hp, -⟩ := h
      clear ih
      induction L2 with
      | nil => exact h2
      | cons q L2 ih2 =>
        obtain ⟨c, d⟩ := q
        simp only [List.all_cons, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hp
        rcases h2 with h2 | h2
        · omega
        · exact ih2 h2 hp.2
    · exact ih h.2 h1

/-- `P` is satisfied by a memory whose addresses lie in the intervals `L`. -/
def SatIn (P : Mem 64 → Prop) (L : List (Nat × Nat)) : Prop :=
  ∃ m : Mem 64, P m ∧ ∀ k, k ∈ m → InL k.toNat L

theorem SatIn.sep {P Q : Mem 64 → Prop} {L1 L2 : List (Nat × Nat)}
    (h1 : SatIn P L1) (h2 : SatIn Q L2) (hd : DisjL L1 L2 = true) : SatIn (P ⋆ Q) (L1 ++ L2) := by
  obtain ⟨m1, hP, hm1⟩ := h1
  obtain ⟨m2, hQ, hm2⟩ := h2
  refine ⟨m1.union m2, ⟨m1, m2, rfl, ?_, hP, hQ⟩, ?_⟩
  · rw [eq_empty_iff_forall_not_mem]
    intro k hk
    rw [inter_eq, mem_inter_iff] at hk
    exact DisjL_spec hd (hm1 k hk.1) (hm2 k hk.2)
  · intro k hk
    rw [union_eq, mem_union_iff] at hk
    rw [InL_append]
    exact hk.imp (hm1 k) (hm2 k)

theorem SatIn.val {a : BitVec 64} {bs : List UInt8} {n : Nat} (hl : bs.length = n)
    (hw : a.toNat + n ≤ 2 ^ 64) : SatIn (bs =@ a) [(a.toNat, a.toNat + n)] := by
  refine ⟨bs.At a, rfl, ?_⟩
  intro k hk
  rw [mem_At_iff] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  left
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem SatIn.block {a : BitVec 64} {n N : Nat} (hn : n ≤ N)
    (hw : a.toNat + N ≤ 2 ^ 64) : SatIn (n ?@ a) [(a.toNat, a.toNat + N)] := by
  obtain ⟨m, hm, hk⟩ := SatIn.val (bs := List.replicate n (0 : UInt8)) (a := a)
    List.length_replicate (by omega)
  refine ⟨m, ⟨by omega, _, List.length_replicate, hm⟩, fun k h => ?_⟩
  rcases hk k h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, by omega⟩
  · exact h.elim

theorem SatIn.emp : SatIn (Std.ExtHashMap.emp : Mem 64 → Prop) [] :=
  ⟨∅, rfl, fun k hk => by simp at hk⟩

/-- Merge the intervals into one enclosing interval. -/
theorem SatIn.widen {P : Mem 64 → Prop} {L : List (Nat × Nat)} (lo hi : Nat) (h : SatIn P L)
    (hL : (L.all fun p => lo ≤ p.1 && p.2 ≤ hi) = true) : SatIn P [(lo, hi)] := by
  obtain ⟨m, hm, hk⟩ := h
  refine ⟨m, hm, fun k hkm => ?_⟩
  have := hk k hkm
  clear hk hkm hm
  left
  induction L with
  | nil => exact this.elim
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hL
    rcases this with h | h
    · omega
    · exact ih hL.2 h

/-- The recursive tactic: split each `⋆`, place each cell. -/
syntax "sat_tac" : tactic
macro_rules
  | `(tactic| sat_tac) => `(tactic| first
      | (apply SatIn.val; exact Int.toBytes_length _ _; decide +kernel)
      | (apply SatIn.val; assumption; decide +kernel)
      | (apply SatIn.val; rfl; decide +kernel)
      | (apply SatIn.block; exact Nat.le_refl _; decide +kernel)
      | (apply SatIn.block; exact Nat.shiftRight_le _ _; decide +kernel)
      | exact SatIn.emp
      | assumption
      | (apply SatIn.sep; sat_tac; sat_tac; decide +kernel))

open Kraken.Examples.Sbr.Apply

/-! ## The machine and the environment -/

/-- The registers at entry: `ac` (`rdi`), `che` (`rsi`, so `sbr = che + 0x28920` is 32-aligned),
`id_aac` (`rdx`), `L` (`rcx`), `R` (`r8`), and `rsp` (with `rsp + 8` 16-aligned). -/
def wRegs (idArg : UInt64) : Reg64s :=
  { rdi := 0x200100000, rsi := 0x200000000, rdx := idArg, rcx := 0x200300000,
    r8 := 0x200304000, rsp := 0x2007FFFF8 }

def wT0 : MachineData := { regs := wRegs 0 }

/-- The callee stack `k`. -/
abbrev wK : Nat := 0x10000

section Generic

variable [CodeEnv]

/-- The slot contents of `SbrSlots`; the unconstrained slots hold 0. -/
def wFns : Fns where
  sum64x5 := entry "ff_sbr_sum64x5_sse"
  sumSquare := entry "ff_sbr_sum_square_sse"
  preShuffle := entry "ff_sbr_qmf_pre_shuffle_sse2"
  postShuffle := entry "ff_sbr_qmf_post_shuffle_sse"
  autocorr := entry "ff_sbr_autocorrelate_sse"
  hfGen := entry "ff_sbr_hf_gen_sse"
  hfs := { gfilt := entry "ff_sbr_hf_g_filt_sse", noise0 := entry "ff_sbr_hf_apply_noise_0_sse2",
           noise1 := entry "ff_sbr_hf_apply_noise_1_sse2",
           noise2 := entry "ff_sbr_hf_apply_noise_2_sse2",
           noise3 := entry "ff_sbr_hf_apply_noise_3_sse2" }
  qfs := { negOdd64 := entry "ff_sbr_neg_odd_64_sse", deintNeg := entry "ff_sbr_qmf_deint_neg_sse",
           deintBfly := entry "ff_sbr_qmf_deint_bfly_sse2", tx := 0,
           fmul := entry "ff_vector_fmul_sse", fmulAdd := entry "ff_vector_fmul_add_sse" }
  lfGen := entry "sbr_lf_gen"
  hfAsm := entry "sbr_hf_assemble"
  xGen := entry "sbr_x_gen"
  hfInv := entry "sbr_hf_inverse_filter"
  mdctAna := 0
  fmulRev := entry "ff_vector_fmul_reverse_sse"

/-- The environment: each `av_tx` context, the `av_tx` and PS tables and the logging state
are 64 owned bytes (non-trivial, pairwise disjoint). -/
def wEnv : Env where
  fs := wFns
  Ctx p := 64 ?@ p
  TxTab := 64 ?@ 0x200500000#64
  PsTab := 64 ?@ 0x200501000#64
  Ext := 64 ?@ 0x200502000#64

theorem wEnv_slots : SbrSlots wEnv :=
  ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- The memory: the convention's cells, the footprint and a 64-byte caller rest, given the
constants `CstW` below `2 ^ 32` (everything else is placed above). -/
theorem wit_mem (x : Args) (ra : Int64) (hC : SatIn CstW [(0, 2 ^ 32)])
    (hfd : x.fdsp = 0x200200000#64) (hana : x.anaCtx = 0x200400000#64)
    (hsyn : x.synCtx = 0x200401000#64) (hR : x.R = 64 ?@ 0x200600000#64)
    (h1 : x.ftLow.length = 50) (h2 : x.ftHigh.length = 98) (h3 : x.ftNoise.length = 12)
    (h4 : x.ftLim.length = 60) (h5 : x.pnum.length = 6) (h6 : x.pstart.length = 6)
    (h7 : x.d0.freqRes.length = 9) (h8 : x.d0.invf.length = 10) (h9 : x.d0.te.length = 10)
    (h10 : x.d0.tq.length = 3) (h11 : x.d1.freqRes.length = 9) (h12 : x.d1.invf.length = 10)
    (h13 : x.d1.te.length = 10) (h14 : x.d1.tq.length = 3) (h15 : x.psc.length = 764)
    (h16 : x.psh.length = 68) :
    ∃ m : Mem 64, m =⋆ RetCell ra (wT0.regs.get64 .rsp)
      ⋆ (Reserve (applyNeed wK) (wT0.regs.get64 .rsp) ⋆ (ApplyF wEnv x wT0 ⋆ x.R)) := by
  have : ∃ L, SatIn (RetCell ra (wT0.regs.get64 .rsp)
      ⋆ (Reserve (applyNeed wK) (wT0.regs.get64 .rsp) ⋆ (ApplyF wEnv x wT0 ⋆ x.R))) L := by
    rw [Reserve_eq _ _ (by decide +kernel)]
    simp only [ApplyF, FnW, hfd, hana, hsyn, hR]
    exact ⟨_, by sat_tac⟩
  obtain ⟨L, m, hm, -⟩ := this
  exact ⟨m, hm⟩

/-- The label alignments `LayoutC` needs. -/
def LabAligned : Prop :=
  isAligned 16 (lab "LCPI14_1") = true ∧ isAligned 16 (lab "LCPI14_2") = true
  ∧ isAligned 16 (lab "LCPI14_8") = true ∧ isAligned 32 (lab "sbr_qmf_window_ds") = true
  ∧ isAligned 16 (lab "ff_ps_neg") = true
  ∧ (isAligned 16 (lab "ps_mask") = true
      ∧ isAligned 32 (lab "sbr_qmf_window_us") = true ∧ isAligned 16 (lab "ps_mask2") = true)
  ∧ isAligned 16 (lab "ps_mask3") = true
  ∧ (isAligned 16 (lab "ps_noise0") = true ∧ isAligned 16 (lab "ps_noise13") = true
      ∧ isAligned 16 (lab "ps_noise2") = true)
  ∧ isAligned 32 (lab "pd_reverse") = true

theorem wit_layout (x : Args) (i : UInt64) (m : Mem 64) (hA : LabAligned) :
    LayoutC x { regs := wRegs i, dmem := m } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hA
  have h1 : isAligned 32 (arg1 wT0) = true := by decide +kernel
  have h2 : isAligned 32 (sbrA wT0) = true := by decide +kernel
  have h3 : isAligned 32 (arg3 wT0) = true := by decide +kernel
  have h4 : isAligned 32 (arg4 wT0) = true := by decide +kernel
  have h5 : isAligned 16 (wT0.regs.get64 .rsp + 8#64) = true := by decide +kernel
  have h6 : (sbrA wT0 + 0x5fcc0#64).toInt + 1280 < 2 ^ 63 := by decide +kernel
  exact ⟨h1, h2, h3, h4, h5, a1, a2, a3, a4, a5, a6, a7, a8, a9, h6⟩

/-- `ApplyPre` at the registers `wRegs i`, from `SbrWF`, the constants, the alignments and the
placement facts of `wit_mem`. -/
theorem wit_pre (x : Args) (ra : Int64) (i : UInt64) (hC : SatIn CstW [(0, 2 ^ 32)])
    (hA : LabAligned) (hx : SbrWF x)
    (hfd : x.fdsp = 0x200200000#64) (hana : x.anaCtx = 0x200400000#64)
    (hsyn : x.synCtx = 0x200401000#64) (hR : x.R = 64 ?@ 0x200600000#64)
    (h1 : x.ftLow.length = 50) (h2 : x.ftHigh.length = 98) (h3 : x.ftNoise.length = 12)
    (h4 : x.ftLim.length = 60) (h5 : x.pnum.length = 6) (h6 : x.pstart.length = 6)
    (h15 : x.psc.length = 764) (h16 : x.psh.length = 68) :
    ∃ t : MachineData, t.regs = wRegs i ∧ ApplyPre wK wEnv x ra t := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨h7, h8, h9, h10, -⟩, ⟨h11, h12, h13, h14, -⟩, -⟩ :=
    id hx
  obtain ⟨m, hm⟩ := wit_mem x ra hC hfd hana hsyn hR h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 h15 h16
  exact ⟨{ regs := wRegs i, dmem := m }, rfl, hm, hx, wit_layout x i m hA⟩

end Generic

/-! ## The ambient code: a program of labels -/

/-- Every label `CstW` and `SbrSlots` mention, each behind an `.align 32` cell. -/
def wProg : Program := parse("
    .align 32
LCPI14_0:
    .align 32
LCPI14_5:
    .align 32
LCPI14_6:
    .align 32
LCPI14_9:
    .align 32
LCPI14_10:
    .align 32
LCPI14_11:
    .align 32
LCPI14_12:
    .align 32
LCPI14_13:
    .align 32
LCPI14_14:
    .align 32
LCPI14_15:
    .align 32
LCPI14_16:
    .align 32
LCPI14_17:
    .align 32
LCPI14_3:
    .align 32
LCPI14_1:
    .align 32
LCPI14_2:
    .align 32
LCPI14_8:
    .align 32
exp2_tab:
    .align 32
bw_tab:
    .align 32
limgain:
    .align 32
sbr_qmf_window_ds:
    .align 32
ff_ps_neg:
    .align 32
ps_mask:
    .align 32
LCPI19_0:
    .align 32
LCPI19_1:
    .align 32
LCPI19_2:
    .align 32
ps_mask3:
    .align 32
sbr_qmf_window_us:
    .align 32
LCPI15_1:
    .align 32
ps_mask2:
    .align 32
ff_sbr_noise_table:
    .align 32
ps_noise0:
    .align 32
ps_noise13:
    .align 32
ps_noise2:
    .align 32
LCPI17_6:
    .align 32
LCPI17_7:
    .align 32
LCPI17_8:
    .align 32
LCPI17_9:
    .align 32
LCPI17_10:
    .align 32
LCPI17_12:
    .align 32
LCPI14_4:
    .align 32
LCPI17_11:
    .align 32
pd_reverse:
    .align 32
ff_aac_sbr_apply:
    .align 32
ff_sbr_sum64x5_sse:
    .align 32
ff_sbr_sum_square_sse:
    .align 32
ff_sbr_qmf_pre_shuffle_sse2:
    .align 32
ff_sbr_qmf_post_shuffle_sse:
    .align 32
ff_sbr_hf_gen_sse:
    .align 32
ff_sbr_autocorrelate_sse:
    .align 32
ff_sbr_hf_g_filt_sse:
    .align 32
ff_sbr_hf_apply_noise_0_sse2:
    .align 32
ff_sbr_hf_apply_noise_1_sse2:
    .align 32
ff_sbr_hf_apply_noise_2_sse2:
    .align 32
ff_sbr_hf_apply_noise_3_sse2:
    .align 32
ff_sbr_neg_odd_64_sse:
    .align 32
ff_sbr_qmf_deint_neg_sse:
    .align 32
ff_sbr_qmf_deint_bfly_sse2:
    .align 32
sbr_lf_gen:
    .align 32
sbr_hf_inverse_filter:
    .align 32
sbr_hf_assemble:
    .align 32
sbr_x_gen:
    .align 32
ff_vector_fmul_sse:
    .align 32
ff_vector_fmul_add_sse:
    .align 32
ff_vector_fmul_reverse_sse:
    .align 32
")

/-- The layout: the text at `0x400000`, labels take no bytes, every `.align` 8192, so every
label sits at a multiple of 8192, below `2 ^ 32`. -/
@[reducible] def wLayout : _root_.Layout where
  start := 0x400000
  size i := if (wProg[i]?.map Directive.isLabel).getD false then 0 else 8192

/-- Whether the cell at position `i` is an `.align n` that ends at a multiple of `n`, or no
`.align` at all. -/
private def wAligned (i : Nat) : Bool :=
  match wProg[i]? with
  | some (.instr (.regular _ _ (.nopalign n _))) =>
      ((wLayout wProg).addrOf (i + 1)).toBitVec.toNat % n == 0
  | _ => true

theorem wLayout_valid : Executable.ValidLayout (wLayout wProg) where
  label_size i l z h := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    show (if (wProg[i]?.map Directive.isLabel).getD false then 0 else 8192) = 0
    simp [hd, Directive.isLabel]
  instr_size i d z h hnl := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d', hd, rfl, rfl⟩ := h
    have : d'.isLabel = false := by
      cases d' <;> simp_all [Directive.isLabel]
    show 0 < (if (wProg[i]?.map Directive.isLabel).getD false then 0 else 8192)
    simp [hd, this]
  no_wrap := by decide +kernel
  align_addr i aw w n pad z h hn := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, hdeq, -⟩ := h
    subst hdeq
    have hi : i < wProg.length := (List.getElem?_eq_some_iff.mp hd).1
    have key : ∀ j, j < wProg.length → wAligned j = true := by
      decide +kernel
    have := key i hi
    simp only [wAligned, hd, beq_iff_eq] at this
    exact this

/-- The ambient code of the witnesses. -/
@[instance_reducible] def wCE : CodeEnv := ⟨wLayout wProg⟩

attribute [local instance] wCE

/-- `d` is not the label `l`. -/
def notLab (l : Label) : Directive × Nat → Bool
  | (.label l', _) => l' != l
  | _ => true

/-- A label's address, at its position `n` (`hn` and `hf` by `decide +kernel`). -/
theorem wlab (l : Label) (n : Nat) (hn : (wLayout wProg).2[n]? = some (.label l, 0))
    (hf : ((wLayout wProg).2.take n).all (notLab l) = true) :
    lab l = ((wLayout wProg).addrOf n).toBitVec := by
  unfold lab
  rw [Executable.label_addrOf _ l _ hn]
  intro dz hdz heq
  have := List.all_eq_true.mp hf dz hdz
  obtain ⟨d, z⟩ := dz
  simp only at heq
  subst heq
  simp [notLab] at this

theorem lab_LCPI14_0 : lab "LCPI14_0" = 0x402000#64 :=
  (wlab _ 1 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_5 : lab "LCPI14_5" = 0x404000#64 :=
  (wlab _ 3 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_6 : lab "LCPI14_6" = 0x406000#64 :=
  (wlab _ 5 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_9 : lab "LCPI14_9" = 0x408000#64 :=
  (wlab _ 7 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_10 : lab "LCPI14_10" = 0x40a000#64 :=
  (wlab _ 9 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_11 : lab "LCPI14_11" = 0x40c000#64 :=
  (wlab _ 11 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_12 : lab "LCPI14_12" = 0x40e000#64 :=
  (wlab _ 13 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_13 : lab "LCPI14_13" = 0x410000#64 :=
  (wlab _ 15 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_14 : lab "LCPI14_14" = 0x412000#64 :=
  (wlab _ 17 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_15 : lab "LCPI14_15" = 0x414000#64 :=
  (wlab _ 19 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_16 : lab "LCPI14_16" = 0x416000#64 :=
  (wlab _ 21 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_17 : lab "LCPI14_17" = 0x418000#64 :=
  (wlab _ 23 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_3 : lab "LCPI14_3" = 0x41a000#64 :=
  (wlab _ 25 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_1 : lab "LCPI14_1" = 0x41c000#64 :=
  (wlab _ 27 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_2 : lab "LCPI14_2" = 0x41e000#64 :=
  (wlab _ 29 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_8 : lab "LCPI14_8" = 0x420000#64 :=
  (wlab _ 31 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_exp2_tab : lab "exp2_tab" = 0x422000#64 :=
  (wlab _ 33 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_bw_tab : lab "bw_tab" = 0x424000#64 :=
  (wlab _ 35 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_limgain : lab "limgain" = 0x426000#64 :=
  (wlab _ 37 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_sbr_qmf_window_ds : lab "sbr_qmf_window_ds" = 0x428000#64 :=
  (wlab _ 39 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ff_ps_neg : lab "ff_ps_neg" = 0x42a000#64 :=
  (wlab _ 41 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ps_mask : lab "ps_mask" = 0x42c000#64 :=
  (wlab _ 43 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI19_0 : lab "LCPI19_0" = 0x42e000#64 :=
  (wlab _ 45 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI19_1 : lab "LCPI19_1" = 0x430000#64 :=
  (wlab _ 47 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI19_2 : lab "LCPI19_2" = 0x432000#64 :=
  (wlab _ 49 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ps_mask3 : lab "ps_mask3" = 0x434000#64 :=
  (wlab _ 51 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_sbr_qmf_window_us : lab "sbr_qmf_window_us" = 0x436000#64 :=
  (wlab _ 53 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI15_1 : lab "LCPI15_1" = 0x438000#64 :=
  (wlab _ 55 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ps_mask2 : lab "ps_mask2" = 0x43a000#64 :=
  (wlab _ 57 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ff_sbr_noise_table : lab "ff_sbr_noise_table" = 0x43c000#64 :=
  (wlab _ 59 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ps_noise0 : lab "ps_noise0" = 0x43e000#64 :=
  (wlab _ 61 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ps_noise13 : lab "ps_noise13" = 0x440000#64 :=
  (wlab _ 63 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_ps_noise2 : lab "ps_noise2" = 0x442000#64 :=
  (wlab _ 65 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_6 : lab "LCPI17_6" = 0x444000#64 :=
  (wlab _ 67 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_7 : lab "LCPI17_7" = 0x446000#64 :=
  (wlab _ 69 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_8 : lab "LCPI17_8" = 0x448000#64 :=
  (wlab _ 71 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_9 : lab "LCPI17_9" = 0x44a000#64 :=
  (wlab _ 73 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_10 : lab "LCPI17_10" = 0x44c000#64 :=
  (wlab _ 75 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_12 : lab "LCPI17_12" = 0x44e000#64 :=
  (wlab _ 77 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI14_4 : lab "LCPI14_4" = 0x450000#64 :=
  (wlab _ 79 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_LCPI17_11 : lab "LCPI17_11" = 0x452000#64 :=
  (wlab _ 81 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lab_pd_reverse : lab "pd_reverse" = 0x454000#64 :=
  (wlab _ 83 (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem wCst : SatIn CstW [(0, 2 ^ 32)] := by
  unfold CstW
  simp only [lab_LCPI14_0, lab_LCPI14_5, lab_LCPI14_6, lab_LCPI14_9, lab_LCPI14_10, lab_LCPI14_11, lab_LCPI14_12, lab_LCPI14_13, lab_LCPI14_14, lab_LCPI14_15, lab_LCPI14_16, lab_LCPI14_17, lab_LCPI14_3, lab_LCPI14_1, lab_LCPI14_2, lab_LCPI14_8, lab_exp2_tab, lab_bw_tab, lab_limgain, lab_sbr_qmf_window_ds, lab_ff_ps_neg, lab_ps_mask, lab_LCPI19_0, lab_LCPI19_1, lab_LCPI19_2, lab_ps_mask3, lab_sbr_qmf_window_us, lab_LCPI15_1, lab_ps_mask2, lab_ff_sbr_noise_table, lab_ps_noise0, lab_ps_noise13, lab_ps_noise2, lab_LCPI17_6, lab_LCPI17_7, lab_LCPI17_8, lab_LCPI17_9, lab_LCPI17_10, lab_LCPI17_12, lab_LCPI14_4, lab_LCPI17_11, lab_pd_reverse]
  exact SatIn.widen 0 (2 ^ 32) (by sat_tac) (by decide +kernel)

theorem wLab : LabAligned := by
  unfold LabAligned
  simp only [lab_LCPI14_1, lab_LCPI14_2, lab_LCPI14_8, lab_sbr_qmf_window_ds, lab_ff_ps_neg, lab_ps_mask, lab_sbr_qmf_window_us, lab_ps_mask2, lab_ps_mask3, lab_ps_noise0, lab_ps_noise13, lab_ps_noise2, lab_pd_reverse]
  decide +kernel

/-! ## The four configurations -/

/-- `n` zero bytes. -/
abbrev zs (n : Nat) : List UInt8 := List.replicate n 0

/-- `l` padded with zeros to `n` bytes. -/
abbrev pad (l : List UInt8) (n : Nat) : List UInt8 := l ++ zs (n - l.length)

/-- A channel in its `av_mallocz` state, with the initial `synthesis_filterbank_samples_offset`
(`SBR_SYNTHESIS_BUF_SIZE - (1280 - 128)`, `aacsbr_template.c`). -/
def dvMalloc : DV :=
  { nenv := 0, freqRes := zs 9, nnoise := 0, invf := zs 10, vOff := 1152, ypos := 0,
    te := zs 10, tq := zs 3, idx := 0 }

/-- A live channel: one envelope over the frame (`t_env = {0, 16}`), one noise floor, high
frequency resolution. -/
def dvLive : DV :=
  { nenv := 1, freqRes := pad [1, 1] 9, nnoise := 1, invf := pad [1] 10, vOff := 1152, ypos := 0,
    te := pad [0, 16] 9 ++ [16], tq := [0, 16, 0], idx := 0 }

/-- The SCE configuration: started, `kx[1] = m[1] = 32`, `n = {4, 8}`, `n_q = n_lim = 2`, one
patch of 32 subbands, downsampled (48000 vs. 24000), PS off. -/
def xSce : Args where
  R := 64 ?@ 0x200600000#64
  start := 1
  ready := 1
  idAac := 0
  reset := 0
  smooth := 1
  pushed := 0
  k0 := 32
  kx0 := 32
  kx1 := 32
  m0 := 32
  m1 := 32
  limGains := 2
  interpol := 1
  coupling := 0
  n0 := 4
  n1 := 8
  nq := 2
  nlim := 2
  npatch := 1
  pnum := pad [32] 6
  pstart := zs 6
  ftLow := pad [32, 0, 40, 0, 48, 0, 56, 0, 64, 0] 50
  ftHigh := pad [32, 0, 36, 0, 40, 0, 44, 0, 48, 0, 52, 0, 56, 0, 60, 0, 64, 0] 98
  ftNoise := pad [32, 0, 48, 0, 64, 0] 12
  ftLim := pad [32, 0, 48, 0, 64, 0] 60
  d0 := dvLive
  d1 := dvMalloc
  sampleRate := 48000
  avctx := 0x200700000
  fdsp := 0x200200000
  extRate := 24000
  ps := 0
  anaCtx := 0x200400000
  synCtx := 0x200401000
  psc := zs 764
  psh := zs 68
  spLo := BitVec.allOnes 32
  spHi := BitVec.allOnes 16

/-- `ps->common` with PS started: `enable_iid = 1`, `iid_quant = 0`, `nr_iid_par = 20`,
`num_env_old = num_env = 1`, `border_position = {-1, 31}`, `iid_par[0][0..20) = 3`,
`icc_par[0][*] = 2`, `ipd_par[0][*] = opd_par[0][*] = 1`, `is34bands = 0`. -/
def pscPs : List UInt8 :=
  [1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 0] ++ zs 24 ++ [1, 0, 0, 0, 1, 0, 0, 0] ++ zs 4
    ++ [255, 255, 255, 255, 31, 0, 0, 0] ++ zs 16
    ++ List.replicate 20 3 ++ zs 150 ++ List.replicate 34 2 ++ zs 136
    ++ List.replicate 34 1 ++ zs 136 ++ List.replicate 34 1 ++ zs 136 ++ zs 8

/-- `opd_hist = 5`, `ipd_hist = 7`. -/
def pshPs : List UInt8 := List.replicate 34 5 ++ List.replicate 34 7

def xPs : Args := { xSce with ps := 1, psc := pscPs, psh := pshPs }

/-- CPE, not downsampled (`ext_sample_rate = sample_rate`). -/
def xCpe : Args := { xSce with idAac := 1, d1 := dvLive, extRate := 48000 }

def xA3 : Args := { xSce with extRate := 48000, d0 := { dvLive with vOff := 1600 } }

/-! ### The invariants -/

theorem psWF_zero : PsWF (zs 764) (zs 68) := by
  unfold PsWF
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun h => absurd (by decide +kernel) h⟩

theorem psWF_ps : PsWF pscPs pshPs := by
  unfold PsWF
  have h44 : i32 pscPs 44 = 1 := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    fun _ => ⟨?_, by decide +kernel, ?_, ?_, by decide +kernel, ?_⟩⟩
  · rw [h44]; decide
  · intro e he
    rw [h44] at he
    obtain rfl : e = 0 := by omega
    decide +kernel
  · rw [h44]; decide +kernel
  · intro e he b hb hor
    rw [h44] at he
    obtain rfl : e = 0 := by omega
    revert b
    decide +kernel

/-- `SbrWF` of a configuration: the decidable clauses by `decide +kernel`, `PsWF` given. -/
theorem sbrWF_of (x : Args) (hps : PsWF x.psc x.psh)
    (h : (x.kx0 ≤ 32 ∧ x.kx1 ≤ 32 ∧ x.kx0 + x.m0 ≤ 64 ∧ x.kx1 + x.m1 ≤ 64 ∧ x.m1 ≤ 48 ∧ x.k0 ≤ 32
      ∧ x.limGains ≤ 3 ∧ x.n0 ≤ 24 ∧ x.n1 ≤ 48 ∧ x.nq ≤ 5 ∧ x.nlim ≤ 29 ∧ x.npatch ≤ 6)
      ∧ (x.start ≠ 0 → TabWF x)
      ∧ DWF (x.start ≠ 0) x.d0 ∧ DWF (x.start ≠ 0 ∧ x.idAac = 1) x.d1) : SbrWF x := by
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩, b, c, d⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, b, c, d, hps⟩

theorem wf_sce : SbrWF xSce := by
  refine sbrWF_of _ psWF_zero ⟨by decide +kernel, ?_, ?_, ?_⟩ <;>
    first | (unfold TabWF; decide +kernel) | (unfold DWF; decide +kernel)

theorem wf_ps : SbrWF xPs := by
  refine sbrWF_of _ psWF_ps ⟨by decide +kernel, ?_, ?_, ?_⟩ <;>
    first | (unfold TabWF; decide +kernel) | (unfold DWF; decide +kernel)

theorem wf_cpe : SbrWF xCpe := by
  refine sbrWF_of _ psWF_zero ⟨by decide +kernel, ?_, ?_, ?_⟩ <;>
    first | (unfold TabWF; decide +kernel) | (unfold DWF; decide +kernel)

theorem wf_a3 : SbrWF xA3 := by
  refine sbrWF_of _ psWF_zero ⟨by decide +kernel, ?_, ?_, ?_⟩ <;>
    first | (unfold TabWF; decide +kernel) | (unfold DWF; decide +kernel)

/-- `id_aac` in `rdx`. -/
theorem wArg2 {t : MachineData} {i : UInt64} (ht : t.regs = wRegs i) :
    arg2 t = (wRegs i).get64 .rdx := by
  show t.regs.get64 .rdx = _
  rw [ht]

/-! ## The witnesses -/

/-- SCE (the V1 case): started, `id_aac = TYPE_SCE` (also in `rdx`), channel 0 live with one
envelope and a strictly monotone `t_env` ending at 16 ≤ 19, channel 1 in its `av_mallocz`
state (`bs_num_env = 0`, `synthesis_filterbank_samples_offset = 1152`), downsampled. -/
theorem apply_pre_sat_sce : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @ApplyPre wCE k e x ra t ∧ @SbrSlots wCE e
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac
    ∧ 1 ≤ x.d0.nenv ∧ u8 x.d0.te 0 < u8 x.d0.te 1 ∧ u8 x.d0.te 1 ≤ 19
    ∧ x.d1 = dvMalloc ∧ x.d1.nenv = 0 ∧ x.d1.vOff = 1152 ∧ x.d0.vOff = 1152 ∧ dsN x = 1 := by
  obtain ⟨t, ht, h⟩ := wit_pre xSce 0 0 wCst wLab wf_sce rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xSce, 0, t, h, wEnv_slots, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl, rfl, rfl, rfl, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

/-- SCE with parametric stereo started (`ps->common.start ≠ 0`, `ac->...ps ≠ 0`): one PS
envelope, borders `{-1, 31}`, `enable_iid` with `nr_iid_par = 20`, non-zero `iid_par`, `icc_par`,
`ipd_par`, `opd_par` and phase histories. -/
theorem apply_pre_sat_ps : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @ApplyPre wCE k e x ra t ∧ @SbrSlots wCE e
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac ∧ 1 ≤ x.d0.nenv
    ∧ x.ps ≠ 0 ∧ i32 x.psc 0 ≠ 0 ∧ 1 ≤ i32 x.psc 44 ∧ i32 x.psc 52 = -1
    ∧ i32 x.psc (52 + 4 * (i32 x.psc 44).toNat) = 31 ∧ i32 x.psc 4 ≠ 0 ∧ i32 x.psc 12 = 20
    ∧ i8 x.psc 76 ≠ 0 := by
  obtain ⟨t, ht, h⟩ := wit_pre xPs 0 0 wCst wLab wf_ps rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xPs, 0, t, h, wEnv_slots, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

/-- CPE: `id_aac = TYPE_CPE` (also in `rdx`), both channels live with one envelope, not
downsampled (`L`, `R` 8192 bytes) with both offsets at 1152 (the common non-downsampled case). -/
theorem apply_pre_sat_cpe : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @ApplyPre wCE k e x ra t ∧ @SbrSlots wCE e
    ∧ x.start = 1 ∧ x.idAac = 1 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac
    ∧ 1 ≤ x.d0.nenv ∧ 1 ≤ x.d1.nenv
    ∧ dsN x = 0 ∧ x.d0.vOff = 1152 ∧ x.d1.vOff = 1152 := by
  obtain ⟨t, ht, h⟩ := wit_pre xCpe 0 1 wCst wLab wf_cpe rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xCpe, 0, t, h, wEnv_slots, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl, rfl⟩
  rw [wArg2 ht]; decide +kernel

/-- Not downsampled (`ext_sample_rate = sample_rate`, so `L`, `R` are 8192 bytes) with
channel 0's `synthesis_filterbank_samples_offset = 1600`, so that `sbr_qmf_synthesis` gets the
larger `qmfVSize` window. The footprint already owns its bytes: `synthesis_filterbank_samples`
(9216 bytes at `d + 0x80`) is followed by `analysis_filterbank_samples` (5248 bytes at
`d + 0x2480`), both in `DArrW`, and the larger window is 2048 bytes longer than the first. -/
theorem apply_pre_sat_a3 : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @ApplyPre wCE k e x ra t ∧ @SbrSlots wCE e
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac ∧ 1 ≤ x.d0.nenv
    ∧ dsN x = 0 ∧ 1152 < x.d0.vOff.toInt ∧ x.d0.vOff.toInt ≤ 1664 := by
  obtain ⟨t, ht, h⟩ := wit_pre xA3 0 0 wCst wLab wf_a3 rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xA3, 0, t, h, wEnv_slots, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

end Kraken.Examples.Sbr.Witness
