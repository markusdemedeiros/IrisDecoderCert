import Kraken.X64.Examples.Sbr.Witness
import Kraken.X64.Examples.Sbr.Placement

/-!
# Joint satisfiability of the three hypotheses of `ff_aac_sbr_apply_linked`

`Witness.lean` shows `ApplyPre ∧ SbrSlots` satisfiable under a label-only ambient code, where
`SbrPlaced` is false. Here one ambient code satisfies all three at once: the image `img` is
every text the proofs talk about (the six C procedures, the twelve `SBRDSPContext` texts of
`SbrDspPlaced`, the eight `float_dsp` texts of `FloatDspPlaced`) behind one cell per read-only constant of `CstW`, laid out by `lLayout`
(labels take no bytes, every other cell 8192, from `0x400000`).

* `lPlaced`: `SbrPlaced` under that code, from `Program.placed_of_layout` on the whole image
  and `Program.PlacedIn.of_flatten` for each text (no text is evaluated beyond its first
  cell; the labels of the image are distinct by a key check).
* `lCst`, `lLab`: the constants sit below `2 ^ 32`, aligned (each constant's label at
  `0x400000 + 8192 k`).
* `linked_hyps_sat_{sce,ps,cpe,a3}`: the four configurations of `Witness.lean`, now with
  `SbrPlaced` as well.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Witness

namespace Kraken.Examples.Sbr.Linked

/-! ## The image -/

/-- The read-only constants `CstW` reads, in its order. -/
def dataLabels : List Label :=
  ["LCPI14_0", "LCPI14_5", "LCPI14_6", "LCPI14_9", "LCPI14_10", "LCPI14_11", "LCPI14_12",
   "LCPI14_13", "LCPI14_14", "LCPI14_15", "LCPI14_16", "LCPI14_17", "LCPI14_3", "LCPI14_1",
   "LCPI14_2", "LCPI14_8", "exp2_tab", "bw_tab", "limgain", "sbr_qmf_window_ds", "ff_ps_neg",
   "ps_mask", "LCPI19_0", "LCPI19_1", "LCPI19_2", "ps_mask3", "sbr_qmf_window_us", "LCPI15_1",
   "ps_mask2", "ff_sbr_noise_table", "ps_noise0", "ps_noise13", "ps_noise2", "LCPI17_6",
   "LCPI17_7", "LCPI17_8", "LCPI17_9", "LCPI17_10", "LCPI17_12", "LCPI14_4", "LCPI17_11",
   "pd_reverse"]

/-- One data cell per constant, at its label. -/
def dataT : List Program := dataLabels.map fun l => [.label l, .byteArray ByteArray.empty]

/-- The texts of the callees: the C procedures, the `SbrDspPlaced` texts and the
`FloatDspPlaced` texts. -/
def codeT : List Program :=
  [LfGen.body, HfInverseFilter.body, XGen.body, HfAssemble.body, QmfSynthesis.body,
   NegOdd64.body, Sum64x5.body, SumSquare.body, QmfPreShuffle.body, QmfPostShuffle.body,
   QmfDeintNeg.body, QmfDeintBfly.body, Autocorrelate.body, Autocorrelate.body3, HfGen.body,
   HfGFilt.body, HfApplyNoise.body,
   VectorFmul.bodySse, VectorFmul.bodyAvx, VectorFmulAdd.bodySse, VectorFmulAdd.bodyAvx,
   VectorFmulAdd.bodyFma3, VectorFmulRev.bodySse, VectorFmulRev.bodyAvx, VectorFmulRev.bodyAvx2]

/-- All texts; `ff_aac_sbr_apply` last. -/
def texts : List Program := dataT ++ codeT ++ [Kraken.Examples.Sbr.Apply.body]

/-- The image. -/
def img : Program := texts.flatten

/-- Every text starts at a label. -/
theorem texts_entry : ∀ t ∈ texts, (Program.view t).1 = [] := by
  intro t ht
  simp only [texts, dataT, codeT, List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at ht
  rcases ht with ((⟨l, -, rfl⟩ | ht) | rfl)
  · rfl
  · rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rw [@Kraken.Examples.Sbr.Apply.view_body wCE]

/-- The labels of the callees and constants. -/
def otherLabels : List Label := (dataT ++ codeT).flatMap Program.labels

theorem labels_img : Program.labels img = otherLabels ++ labelList := by
  rw [img, Program.labels_flatten, texts, List.flatMap_append, otherLabels]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [@Kraken.Examples.Sbr.Apply.labels_body wCE]

/-- The prefix of every label of `ff_aac_sbr_apply`'s text. -/
abbrev applyPrefix : String := "ff_aac_sbr_apply"

theorem otherKeys_nodup : (otherLabels.map labelKey).Nodup := by decide +kernel

theorem other_noPrefix : otherLabels.all (fun l => !l.startsWith applyPrefix) = true := by
  decide +kernel

theorem labelList_prefix : labelList.all (fun l => l.startsWith applyPrefix) = true := by
  decide +kernel

theorem img_wf : Program.WF img := by
  refine ⟨?_⟩
  rw [labels_img, List.nodup_append]
  refine ⟨(List.pairwise_map.mp otherKeys_nodup).imp fun h e => h (congrArg labelKey e), @labelList_nodup wCE, ?_⟩
  intro a ha b hb hab
  subst hab
  have h1 := List.all_eq_true.mp other_noPrefix a ha
  have h2 := List.all_eq_true.mp labelList_prefix a hb
  simp only [Bool.not_eq_true'] at h1
  rw [h1] at h2
  cases h2

/-! ## The layout -/

/-- The image at `0x400000`: labels take no bytes, every other cell 8192. -/
@[reducible] def lLayout : _root_.Layout where
  start := 0x400000
  size i := if (img[i]?.map Directive.isLabel).getD false then 0 else 8192

attribute [local instance] lLayout

/-- No cell of the image is an `.align`. -/
def noAlign : Directive → Bool
  | .instr (.regular _ _ (.nopalign _ _)) => false
  | _ => true

theorem img_noAlign : img.all noAlign = true := by decide +kernel

theorem img_length : img.length < 2 ^ 40 := by decide +kernel

theorem sum_snd_le : ∀ (l : List (Directive × Nat)) (c : Nat), (∀ x ∈ l, x.2 ≤ c) →
    (l.map (·.2)).sum ≤ c * l.length
  | [], _, _ => by simp
  | x :: l, c, h => by
    have ih := sum_snd_le l c (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
    omega

theorem lLayout_valid : Executable.ValidLayout (lLayout img) where
  label_size i l z h := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    show (if (img[i]?.map Directive.isLabel).getD false then 0 else 8192) = 0
    simp [hd, Directive.isLabel]
  instr_size i d z h hnl := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d', hd, rfl, rfl⟩ := h
    have : d'.isLabel = false := by
      cases d' <;> simp_all [Directive.isLabel]
    show 0 < (if (img[i]?.map Directive.isLabel).getD false then 0 else 8192)
    simp [hd, this]
  no_wrap := by
    have hle : ∀ x ∈ (lLayout img).2, x.2 ≤ 8192 := by
      intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff] at hi
      obtain ⟨d, -, rfl⟩ := hi
      show (if (img[i]?.map Directive.isLabel).getD false then 0 else 8192) ≤ 8192
      split <;> omega
    have h := sum_snd_le _ 8192 hle
    have hlen : (lLayout img).2.length = img.length := by simp [Kraken.Layout.apply]
    have := img_length
    omega
  align_addr i aw w n pad z h hn := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, hdeq, -⟩ := h
    subst hdeq
    have := List.all_eq_true.mp img_noAlign _ (List.mem_of_getElem? hd)
    simp [noAlign] at this

attribute [local instance] lLayout_valid

/-- The ambient code: the laid-out image. -/
@[instance_reducible] def lCE : CodeEnv := ⟨lLayout img⟩

attribute [local instance] lCE

theorem img_head : ∃ tl, img = .label "LCPI14_0" :: tl :=
  List.head?_eq_some_iff.mp (show img.head? = some (.label "LCPI14_0") by decide +kernel)

theorem img_placed : Program.Placed img "LCPI14_0" := by
  obtain ⟨tl, h⟩ := img_head
  exact Program.placed_of_layout img_wf h (by decide +kernel)

/-- A text of the image is placed. -/
theorem placedIn_of_mem {p : Program} (hp : p ∈ texts) : Program.PlacedIn p :=
  Program.PlacedIn.of_flatten img_placed.toPlacedIn img_wf.nodup texts_entry hp

/-- The `i`-th text is in the image (by its index: no comparison of texts). -/
theorem text_mem (i : Nat) (h : i < texts.length) : texts[i] ∈ texts := List.getElem_mem h

theorem lPlaced : SbrPlaced where
  apply := placedIn_of_mem (text_mem 67 (by decide))
  lfGen := placedIn_of_mem (text_mem 42 (by decide))
  hfInv := placedIn_of_mem (text_mem 43 (by decide))
  xGen := placedIn_of_mem (text_mem 44 (by decide))
  hfAsm := placedIn_of_mem (text_mem 45 (by decide))
  qmfSyn := placedIn_of_mem (text_mem 46 (by decide))
  dsp := ⟨placedIn_of_mem (text_mem 47 (by decide)), placedIn_of_mem (text_mem 48 (by decide)),
    placedIn_of_mem (text_mem 49 (by decide)), placedIn_of_mem (text_mem 50 (by decide)),
    placedIn_of_mem (text_mem 51 (by decide)), placedIn_of_mem (text_mem 52 (by decide)),
    placedIn_of_mem (text_mem 53 (by decide)), placedIn_of_mem (text_mem 54 (by decide)),
    placedIn_of_mem (text_mem 55 (by decide)), placedIn_of_mem (text_mem 56 (by decide)),
    placedIn_of_mem (text_mem 57 (by decide)), placedIn_of_mem (text_mem 58 (by decide))⟩
  fdsp := ⟨placedIn_of_mem (text_mem 59 (by decide)), placedIn_of_mem (text_mem 60 (by decide)),
    placedIn_of_mem (text_mem 61 (by decide)), placedIn_of_mem (text_mem 62 (by decide)),
    placedIn_of_mem (text_mem 63 (by decide)), placedIn_of_mem (text_mem 64 (by decide)),
    placedIn_of_mem (text_mem 65 (by decide)), placedIn_of_mem (text_mem 66 (by decide))⟩

/-! ## The addresses of the constants

Read off the data prefix `dataP` (84 cells) of the laid-out image: the rest of the image is
never evaluated. -/

/-- The data cells. -/
def dataP : Program := dataT.flatten

theorem dataP_length : dataP.length = 84 := by decide +kernel

theorem img_split : img = dataP ++ (codeT ++ [Kraken.Examples.Sbr.Apply.body]).flatten := by
  rw [img, texts, List.append_assoc, List.flatten_append, dataP]

/-- The laid-out image, up to the end of the data cells. -/
theorem take_layout : (lLayout img).2.take 84 = Layout.frag 0 dataP := by
  rw [Layout.apply_snd]
  conv => lhs; rw [img_split]
  rw [Layout.frag_append, ← dataP_length, List.take_left' (by rw [Layout.frag_length])]

/-- A label's address, at its position `n` within the data cells. -/
theorem labAt (l : Label) (n : Nat) (hlt : n < 84)
    (hn : (Layout.frag 0 dataP)[n]? = some (.label l, 0))
    (hf : ((Layout.frag 0 dataP).take n).all (notLab l) = true) :
    lab l = ((0x400000 : Int64)
      + Int64.ofNat ((((Layout.frag 0 dataP).take n).map (·.2)).sum)).toBitVec := by
  have htake : (lLayout img).2.take n = (Layout.frag 0 dataP).take n := by
    rw [← take_layout, List.take_take, Nat.min_eq_left (by omega)]
  unfold lab
  rw [Executable.label_addrOf _ l n ?hn ?hf]
  · show ((0x400000 : Int64) + Int64.ofNat ((((lLayout img).2.take n).map (·.2)).sum)).toBitVec = _
    rw [htake]
  case hn =>
    show (lLayout img).2[n]? = _
    have h82 : (lLayout img).2[n]? = ((lLayout img).2.take 84)[n]? :=
      (List.getElem?_take_of_lt hlt).symm
    rw [h82, take_layout]
    exact hn
  case hf =>
    show ∀ dz ∈ (lLayout img).2.take n, _
    rw [htake]
    intro dz hdz heq
    have := List.all_eq_true.mp hf dz hdz
    obtain ⟨d, z⟩ := dz
    simp only at heq
    subst heq
    simp [notLab] at this

theorem llab_LCPI14_0 : lab "LCPI14_0" = 0x400000#64 :=
  (labAt _ 0 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_5 : lab "LCPI14_5" = 0x402000#64 :=
  (labAt _ 2 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_6 : lab "LCPI14_6" = 0x404000#64 :=
  (labAt _ 4 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_9 : lab "LCPI14_9" = 0x406000#64 :=
  (labAt _ 6 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_10 : lab "LCPI14_10" = 0x408000#64 :=
  (labAt _ 8 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_11 : lab "LCPI14_11" = 0x40a000#64 :=
  (labAt _ 10 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_12 : lab "LCPI14_12" = 0x40c000#64 :=
  (labAt _ 12 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_13 : lab "LCPI14_13" = 0x40e000#64 :=
  (labAt _ 14 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_14 : lab "LCPI14_14" = 0x410000#64 :=
  (labAt _ 16 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_15 : lab "LCPI14_15" = 0x412000#64 :=
  (labAt _ 18 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_16 : lab "LCPI14_16" = 0x414000#64 :=
  (labAt _ 20 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_17 : lab "LCPI14_17" = 0x416000#64 :=
  (labAt _ 22 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_3 : lab "LCPI14_3" = 0x418000#64 :=
  (labAt _ 24 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_1 : lab "LCPI14_1" = 0x41a000#64 :=
  (labAt _ 26 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_2 : lab "LCPI14_2" = 0x41c000#64 :=
  (labAt _ 28 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_8 : lab "LCPI14_8" = 0x41e000#64 :=
  (labAt _ 30 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_exp2_tab : lab "exp2_tab" = 0x420000#64 :=
  (labAt _ 32 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_bw_tab : lab "bw_tab" = 0x422000#64 :=
  (labAt _ 34 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_limgain : lab "limgain" = 0x424000#64 :=
  (labAt _ 36 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_sbr_qmf_window_ds : lab "sbr_qmf_window_ds" = 0x426000#64 :=
  (labAt _ 38 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ff_ps_neg : lab "ff_ps_neg" = 0x428000#64 :=
  (labAt _ 40 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ps_mask : lab "ps_mask" = 0x42a000#64 :=
  (labAt _ 42 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI19_0 : lab "LCPI19_0" = 0x42c000#64 :=
  (labAt _ 44 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI19_1 : lab "LCPI19_1" = 0x42e000#64 :=
  (labAt _ 46 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI19_2 : lab "LCPI19_2" = 0x430000#64 :=
  (labAt _ 48 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ps_mask3 : lab "ps_mask3" = 0x432000#64 :=
  (labAt _ 50 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_sbr_qmf_window_us : lab "sbr_qmf_window_us" = 0x434000#64 :=
  (labAt _ 52 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI15_1 : lab "LCPI15_1" = 0x436000#64 :=
  (labAt _ 54 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ps_mask2 : lab "ps_mask2" = 0x438000#64 :=
  (labAt _ 56 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ff_sbr_noise_table : lab "ff_sbr_noise_table" = 0x43a000#64 :=
  (labAt _ 58 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ps_noise0 : lab "ps_noise0" = 0x43c000#64 :=
  (labAt _ 60 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ps_noise13 : lab "ps_noise13" = 0x43e000#64 :=
  (labAt _ 62 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_ps_noise2 : lab "ps_noise2" = 0x440000#64 :=
  (labAt _ 64 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_6 : lab "LCPI17_6" = 0x442000#64 :=
  (labAt _ 66 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_7 : lab "LCPI17_7" = 0x444000#64 :=
  (labAt _ 68 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_8 : lab "LCPI17_8" = 0x446000#64 :=
  (labAt _ 70 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_9 : lab "LCPI17_9" = 0x448000#64 :=
  (labAt _ 72 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_10 : lab "LCPI17_10" = 0x44a000#64 :=
  (labAt _ 74 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_12 : lab "LCPI17_12" = 0x44c000#64 :=
  (labAt _ 76 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI14_4 : lab "LCPI14_4" = 0x44e000#64 :=
  (labAt _ 78 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_LCPI17_11 : lab "LCPI17_11" = 0x450000#64 :=
  (labAt _ 80 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem llab_pd_reverse : lab "pd_reverse" = 0x452000#64 :=
  (labAt _ 82 (by decide) (by decide +kernel) (by decide +kernel)).trans (by decide +kernel)

theorem lCst : SatIn CstW [(0, 2 ^ 32)] := by
  unfold CstW
  simp only [llab_LCPI14_0, llab_LCPI14_5, llab_LCPI14_6, llab_LCPI14_9, llab_LCPI14_10, llab_LCPI14_11, llab_LCPI14_12, llab_LCPI14_13, llab_LCPI14_14, llab_LCPI14_15, llab_LCPI14_16, llab_LCPI14_17, llab_LCPI14_3, llab_LCPI14_1, llab_LCPI14_2, llab_LCPI14_8, llab_exp2_tab, llab_bw_tab, llab_limgain, llab_sbr_qmf_window_ds, llab_ff_ps_neg, llab_ps_mask, llab_LCPI19_0, llab_LCPI19_1, llab_LCPI19_2, llab_ps_mask3, llab_sbr_qmf_window_us, llab_LCPI15_1, llab_ps_mask2, llab_ff_sbr_noise_table, llab_ps_noise0, llab_ps_noise13, llab_ps_noise2, llab_LCPI17_6, llab_LCPI17_7, llab_LCPI17_8, llab_LCPI17_9, llab_LCPI17_10, llab_LCPI17_12, llab_LCPI14_4, llab_LCPI17_11, llab_pd_reverse]
  exact SatIn.widen 0 (2 ^ 32) (by sat_tac) (by decide +kernel)

theorem lLab : LabAligned := by
  unfold LabAligned
  simp only [llab_LCPI14_1, llab_LCPI14_2, llab_LCPI14_8, llab_sbr_qmf_window_ds, llab_ff_ps_neg, llab_ps_mask, llab_sbr_qmf_window_us, llab_ps_mask2, llab_ps_mask3, llab_ps_noise0, llab_ps_noise13, llab_ps_noise2, llab_pd_reverse]
  decide +kernel

/-! ## The witnesses: `SbrPlaced`, `SbrSlots` and `ApplyPre` at once

The configurations and their conjuncts are those of `Witness.apply_pre_sat_*`; the ambient
code is the laid-out image `lCE`. The code is bound (`C`) and passed explicitly to all
three hypotheses, so they hold of the same code; the proofs instantiate `C := lCE`. -/

/-- SCE (the V1 case): started, `id_aac = TYPE_SCE` (also in `rdx`), channel 0 live with one
envelope and a strictly monotone `t_env` ending at 16 ≤ 19, channel 1 in its `av_mallocz`
state (`bs_num_env = 0`, `synthesis_filterbank_samples_offset = 1152`), downsampled. -/
theorem linked_hyps_sat_sce : ∃ (C : CodeEnv) (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced C ∧ @SbrSlots C e ∧ @ApplyPre C k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac
    ∧ 1 ≤ x.d0.nenv ∧ u8 x.d0.te 0 < u8 x.d0.te 1 ∧ u8 x.d0.te 1 ≤ 19
    ∧ x.d1 = dvMalloc ∧ x.d1.nenv = 0 ∧ x.d1.vOff = 1152 ∧ x.d0.vOff = 1152 ∧ dsN x = 1 := by
  obtain ⟨t, ht, h⟩ := wit_pre xSce 0 0 lCst lLab wf_sce rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨lCE, wK, wEnv, xSce, 0, t, lPlaced, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl, rfl, rfl, rfl, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

/-- SCE with parametric stereo started (`ps->common.start ≠ 0`, `ac->...ps ≠ 0`): one PS
envelope, borders `{-1, 31}`, `enable_iid` with `nr_iid_par = 20`, non-zero `iid_par`, `icc_par`,
`ipd_par`, `opd_par` and phase histories. -/
theorem linked_hyps_sat_ps : ∃ (C : CodeEnv) (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced C ∧ @SbrSlots C e ∧ @ApplyPre C k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac ∧ 1 ≤ x.d0.nenv
    ∧ x.ps ≠ 0 ∧ i32 x.psc 0 ≠ 0 ∧ 1 ≤ i32 x.psc 44 ∧ i32 x.psc 52 = -1
    ∧ i32 x.psc (52 + 4 * (i32 x.psc 44).toNat) = 31 ∧ i32 x.psc 4 ≠ 0 ∧ i32 x.psc 12 = 20
    ∧ i8 x.psc 76 ≠ 0 := by
  obtain ⟨t, ht, h⟩ := wit_pre xPs 0 0 lCst lLab wf_ps rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨lCE, wK, wEnv, xPs, 0, t, lPlaced, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

/-- CPE: `id_aac = TYPE_CPE` (also in `rdx`), both channels live with one envelope, not
downsampled (`L`, `R` 8192 bytes) with both offsets at 1152 (the common non-downsampled case). -/
theorem linked_hyps_sat_cpe : ∃ (C : CodeEnv) (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced C ∧ @SbrSlots C e ∧ @ApplyPre C k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 1 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac
    ∧ 1 ≤ x.d0.nenv ∧ 1 ≤ x.d1.nenv
    ∧ dsN x = 0 ∧ x.d0.vOff = 1152 ∧ x.d1.vOff = 1152 := by
  obtain ⟨t, ht, h⟩ := wit_pre xCpe 0 1 lCst lLab wf_cpe rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨lCE, wK, wEnv, xCpe, 0, t, lPlaced, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, rfl, rfl⟩
  rw [wArg2 ht]; decide +kernel

/-- Not downsampled (`ext_sample_rate = sample_rate`, so `L`, `R` are 8192 bytes) with
channel 0's `synthesis_filterbank_samples_offset = 1600`, so that `sbr_qmf_synthesis` gets the
larger `qmfVSize` window. The footprint already owns its bytes: `synthesis_filterbank_samples`
(9216 bytes at `d + 0x80`) is followed by `analysis_filterbank_samples` (5248 bytes at
`d + 0x2480`), both in `DArrW`, and the larger window is 2048 bytes longer than the first. -/
theorem linked_hyps_sat_a3 : ∃ (C : CodeEnv) (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced C ∧ @SbrSlots C e ∧ @ApplyPre C k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac ∧ 1 ≤ x.d0.nenv
    ∧ dsN x = 0 ∧ 1152 < x.d0.vOff.toInt ∧ x.d0.vOff.toInt ≤ 1664 := by
  obtain ⟨t, ht, h⟩ := wit_pre xA3 0 0 lCst lLab wf_a3 rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨lCE, wK, wEnv, xA3, 0, t, lPlaced, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

end Kraken.Examples.Sbr.Linked
