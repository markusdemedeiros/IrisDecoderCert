import Kraken.X64.Examples.Sbr.Linked
import Kraken.X64.Examples.Sbr.FloatDsp
import KrakenSbrReal.RealData

/-!
# `SbrPlaced` for the layout of the linked binary

`Linked.lean` shows the three hypotheses of `ff_aac_sbr_apply_linked` jointly satisfiable
under a constructed image. Here the ambient code is the image of a real artifact: the
FFmpeg 8.1 `ffmpeg` PIE (opt build), which links the objects the texts were validated
against, unchanged (see `scripts/sbr/README.md`, "The binary").

* `rImg`: the address range from the QMF windows (`.lrodata`) to `_GLOBAL_OFFSET_TABLE_` as
  the binary has it, in address order (`RealData.rPieces`, generated): the twenty-six proved
  texts at their addresses; one cell per constant, string, callee and the GOT, at the address
  the binary's own instructions encode for it; labelled gaps for the bytes in between.
* `rCE b`: that image laid out at `b + rStart` with the binary's cell sizes
  (`RealData.rTextSizes`: 0 for a label, the instruction's length otherwise). `b` is the load
  bias of the PIE; `b = 0` is the link-time layout.
* `rPlaced b`: `SbrPlaced` under `rCE b`, for every `b`.
* `ff_aac_sbr_apply_real`: the linked theorem under `rCE b` with `SbrPlaced` discharged.
* `rlab_*`, `rLab`, `rCst`, `real_hyps_sat_*`: the constants at their real addresses,
  aligned for every page-aligned `b`; the four witnesses of `Linked.lean` under `rCE 0`.

`scripts/sbr/real/check.sh` ties `rCE 0` to the binary: every instruction cell, re-assembled
at its `rCE 0` address with the labels at their `rCE 0` addresses, gives the binary's bytes
there, and its size is the binary instruction's length.
-/

open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem
open Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Witness Kraken.Examples.Sbr.Linked

namespace Kraken.Examples.Sbr.Real

/-! ## The image -/

/-- The texts, in the order of `scripts/sbr/real/real_lib.py`'s `TEXTS`. -/
def rTexts : List Program :=
  [NegOdd64.body, Sum64x5.body, SumSquare.body, QmfPreShuffle.body, QmfPostShuffle.body,
   QmfDeintNeg.body, QmfDeintBfly.body, Autocorrelate.body, Autocorrelate.body3, HfGen.body,
   HfGFilt.body, HfApplyNoise.body, QmfSynthesis.body, LfGen.body, HfInverseFilter.body,
   XGen.body, HfAssemble.body, Kraken.Examples.Sbr.Apply.body,
   VectorFmul.bodySse, VectorFmul.bodyAvx, VectorFmulAdd.bodySse, VectorFmulAdd.bodyAvx,
   VectorFmulAdd.bodyFma3, VectorFmulRev.bodySse, VectorFmulRev.bodyAvx, VectorFmulRev.bodyAvx2]

/-- A piece of the image: a label with one cell of `n` bytes behind it (none if `n = 0`),
or a text. -/
def pieceProg : (String × Nat) ⊕ Nat → Program
  | .inl (l, 0) => [.label l]
  | .inl (l, _ + 1) => [.label l, .byteArray ByteArray.empty]
  | .inr i => rTexts.getD i []

/-- The sizes of a piece's cells. -/
def pieceSizes : (String × Nat) ⊕ Nat → List Nat
  | .inl (_, 0) => [0]
  | .inl (_, n + 1) => [0, n + 1]
  | .inr i => rTextSizes.getD i []

def rProgs : List Program := rPieces.map pieceProg

/-- The image. -/
def rImg : Program := rProgs.flatten

/-- The size of each cell of the image. -/
def rSizes : List Nat := (rPieces.map pieceSizes).flatten

theorem rTexts_entry : ∀ t ∈ rTexts, (Program.view t).1 = [] := by
  intro t ht
  simp only [rTexts, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rw [@Kraken.Examples.Sbr.Apply.view_body wCE] | rfl

theorem rProgs_entry : ∀ t ∈ rProgs, (Program.view t).1 = [] := by
  intro t ht
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp ht
  rcases p with ⟨l, _ | n⟩ | i
  · rfl
  · rfl
  · show (Program.view (rTexts.getD i [])).1 = []
    rw [List.getD_eq_getElem?_getD]
    rcases h : rTexts[i]? with _ | t
    · rfl
    · exact rTexts_entry t (List.mem_of_getElem? h)

/-! ## Labels: distinct

`ff_aac_sbr_apply`'s text is the piece `.inr 17`; its labels (`labelList`) all start with
`ff_aac_sbr_apply`, no other label does, and the other labels have distinct keys. -/

theorem rPieces_split :
    rPieces = rPieces.take rApplyIdx ++ .inr 17 :: rPieces.drop (rApplyIdx + 1) := by
  decide +kernel

/-- The labels of the pieces other than `ff_aac_sbr_apply`. -/
def rOther : List Label :=
  (rPieces.take rApplyIdx ++ rPieces.drop (rApplyIdx + 1)).flatMap
    (fun p => Program.labels (pieceProg p))

theorem rOther_keys : (rOther.map labelKey).Nodup := by decide +kernel

theorem rOther_noPrefix : rOther.all (fun l => !l.startsWith applyPrefix) = true := by
  decide +kernel

theorem labels_rImg : (Program.labels rImg).Perm (rOther ++ labelList) := by
  have hA : Program.labels (pieceProg (.inr 17)) = labelList :=
    @Kraken.Examples.Sbr.Apply.labels_body wCE
  have e : Program.labels rImg = (rPieces.take rApplyIdx).flatMap (fun p => Program.labels (pieceProg p))
      ++ (labelList ++ (rPieces.drop (rApplyIdx + 1)).flatMap (fun p => Program.labels (pieceProg p))) := by
    rw [rImg, Program.labels_flatten, rProgs, List.flatMap_map]
    conv => lhs; rw [rPieces_split]
    rw [List.flatMap_append, List.flatMap_cons, hA]
  rw [e, rOther, List.flatMap_append, List.append_assoc]
  exact List.Perm.append_left _ List.perm_append_comm

theorem rImg_wf : Program.WF rImg := by
  refine ⟨(List.Perm.nodup_iff labels_rImg).mpr ?_⟩
  rw [List.nodup_append]
  refine ⟨(List.pairwise_map.mp rOther_keys).imp fun h e => h (congrArg labelKey e),
    @labelList_nodup wCE, ?_⟩
  intro a ha b hb hab
  subst hab
  have h1 := List.all_eq_true.mp rOther_noPrefix a ha
  have h2 := List.all_eq_true.mp labelList_prefix a hb
  simp only [Bool.not_eq_true'] at h1
  rw [h1] at h2
  cases h2

/-! ## The layout -/

/-- The cell check: a label takes no bytes, every other cell at least one, and no cell is an
`.align`. -/
def cellOk : Directive × Nat → Bool
  | (d, z) => if d.isLabel then z == 0 else (0 < z && noAlign d)

theorem rCells_ok : rImg.length = rSizes.length ∧ (rImg.zip rSizes).all cellOk = true := by
  decide +kernel

theorem rSizes_sum : rSizes.sum < 2 ^ 64 := by decide +kernel

theorem zip_all_get {ds : List Directive} {zs : List Nat} (hl : ds.length = zs.length)
    (h : (ds.zip zs).all cellOk = true) {i : Nat} {d : Directive} (hd : ds[i]? = some d) :
    cellOk (d, zs.getD i 0) = true := by
  have hi : i < ds.length := (List.getElem?_eq_some_iff.mp hd).1
  have hz : zs[i]? = some (zs[i]'(hl ▸ hi)) := List.getElem?_eq_getElem _
  have hmem : (d, zs[i]'(hl ▸ hi)) ∈ ds.zip zs :=
    List.mem_iff_getElem?.mpr ⟨i, by rw [List.getElem?_zip_eq_some]; exact ⟨hd, hz⟩⟩
  rw [List.getD_eq_getElem?_getD, hz]
  exact List.all_eq_true.mp h _ hmem

/-- The image at `b + rStart`, each cell with its size in the binary. -/
@[reducible] def rLayout (b : Int64) : _root_.Layout where
  start := b + Int64.ofNat rStart
  size i := rSizes.getD i 0

theorem rLayout_snd (b : Int64) :
    ((rLayout b) rImg).2 = rImg.mapIdx (fun i d => (d, rSizes.getD i 0)) := by
  rw [@Layout.apply_snd (rLayout b)]
  simp only [Layout.frag, Nat.zero_add]
  rfl

theorem rLayout_get {b : Int64} {i : Nat} {d : Directive} {z : Nat}
    (h : ((rLayout b) rImg).2[i]? = some (d, z)) : rImg[i]? = some d ∧ z = rSizes.getD i 0 := by
  rw [rLayout_snd, List.getElem?_mapIdx] at h
  obtain ⟨d', hd, he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact ⟨hd, rfl⟩

theorem rLayout_valid (b : Int64) : Executable.ValidLayout ((rLayout b) rImg) where
  label_size i l z h := by
    obtain ⟨hd, rfl⟩ := rLayout_get h
    have := zip_all_get rCells_ok.1 rCells_ok.2 hd
    simpa [cellOk, Directive.isLabel] using this
  instr_size i d z h hnl := by
    obtain ⟨hd, rfl⟩ := rLayout_get h
    have := zip_all_get rCells_ok.1 rCells_ok.2 hd
    have hl : d.isLabel = false := by cases d <;> simp_all [Directive.isLabel]
    simp only [cellOk, hl, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  no_wrap := by
    have : (((rLayout b) rImg).2.map (·.2)) = rSizes := by
      rw [rLayout_snd]
      apply List.ext_getElem
      · simp [rCells_ok.1]
      · intro i h1 h2
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rw [this]
    exact rSizes_sum
  align_addr i aw w n pad z h hn := by
    obtain ⟨hd, rfl⟩ := rLayout_get h
    have := zip_all_get rCells_ok.1 rCells_ok.2 hd
    simp [cellOk, Directive.isLabel, noAlign] at this

/-- The ambient code: the binary's image at load bias `b`. -/
@[instance_reducible] def rCE (b : Int64) : CodeEnv := ⟨(rLayout b) rImg⟩

theorem rImg_head : ∃ tl, rImg = .label "sbr_qmf_window_ds" :: tl :=
  List.head?_eq_some_iff.mp (show rImg.head? = some (.label "sbr_qmf_window_ds") by decide +kernel)

theorem rImg_placed (b : Int64) : @Program.Placed (rCE b) rImg "sbr_qmf_window_ds" := by
  obtain ⟨tl, h⟩ := rImg_head
  haveI := rLayout_valid b
  exact @Program.placed_of_layout (rLayout b) _ _ _ _ rImg_wf h (by decide +kernel)

/-- A text of `rTexts` whose piece is in the image is placed. -/
theorem placed_text (b : Int64) (i : Nat) (hi : (.inr i : (String × Nat) ⊕ Nat) ∈ rPieces) :
    @Program.PlacedIn (rCE b) (rTexts.getD i []) :=
  @Program.PlacedIn.of_flatten (rCE b) rProgs _ (@Program.Placed.toPlacedIn (rCE b) _ _ (rImg_placed b)) rImg_wf.nodup
    rProgs_entry (List.mem_map_of_mem hi)

/-- **Placement in the binary**: every text `SbrPlaced` names is placed in the binary's
image, at every load bias. -/
theorem rPlaced (b : Int64) : @SbrPlaced (rCE b) := by
  letI := rCE b
  exact {
  apply := placed_text b 17 (by decide)
  lfGen := placed_text b 13 (by decide)
  hfInv := placed_text b 14 (by decide)
  xGen := placed_text b 15 (by decide)
  hfAsm := placed_text b 16 (by decide)
  qmfSyn := placed_text b 12 (by decide)
  dsp := ⟨placed_text b 0 (by decide), placed_text b 1 (by decide),
    placed_text b 2 (by decide), placed_text b 3 (by decide),
    placed_text b 4 (by decide), placed_text b 5 (by decide),
    placed_text b 6 (by decide), placed_text b 7 (by decide),
    placed_text b 8 (by decide), placed_text b 9 (by decide),
    placed_text b 10 (by decide), placed_text b 11 (by decide)⟩
  fdsp := ⟨placed_text b 18 (by decide), placed_text b 19 (by decide),
    placed_text b 20 (by decide), placed_text b 21 (by decide),
    placed_text b 22 (by decide), placed_text b 23 (by decide),
    placed_text b 24 (by decide), placed_text b 25 (by decide)⟩ }

/-- **`ff_aac_sbr_apply` in the binary.** `ff_aac_sbr_apply_linked` with the ambient code the
image of the linked binary at load bias `b`: placement is proved (`rPlaced`), so the slot
contents and the assumed external contracts remain. -/
theorem ff_aac_sbr_apply_real (b : Int64) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (hslots : @SbrSlots (rCE b) e) (hasm : @SbrAssumed (rCE b) k e) : @ApplySpec (rCE b) k e :=
  @ff_aac_sbr_apply_linked (rCE b) (rPlaced b) k hk e hslots hasm

/-! ## The constants at their real addresses

Read off the data pieces `rDataP` (everything below the first text): the texts are never
evaluated. The sizes a layout gives do not depend on the load bias. -/

/-- The data pieces. -/
def rDataP : Program := ((rPieces.take rDataN).map pieceProg).flatten

theorem rDataP_length : rDataP.length = 104 := by decide +kernel

theorem rImg_split : rImg = rDataP ++ ((rPieces.drop rDataN).map pieceProg).flatten := by
  rw [rImg, rProgs, rDataP, ← List.flatten_append, ← List.map_append, List.take_append_drop]

theorem frag_bias (b : Int64) (p : Program) :
    @Layout.frag (rLayout b) 0 p = @Layout.frag (rLayout 0) 0 p := by
  have h : ∀ b' : Int64, @Layout.size Directive (rLayout b') = fun i => rSizes.getD i 0 :=
    fun _ => rfl
  simp only [Layout.frag, h]

theorem take_layout (b : Int64) :
    ((rLayout b) rImg).2.take 104 = @Layout.frag (rLayout 0) 0 rDataP := by
  rw [@Layout.apply_snd (rLayout b), frag_bias b]
  conv => lhs; rw [rImg_split]
  rw [@Layout.frag_append (rLayout 0), ← rDataP_length,
    List.take_left' (by rw [@Layout.frag_length (rLayout 0)])]

/-- A label's address, at its position `n` within the data pieces: the load bias plus its
link-time address. -/
theorem rlabAt (b : Int64) (l : Label) (n : Nat) (hlt : n < 104)
    (hn : (@Layout.frag (rLayout 0) 0 rDataP)[n]? = some (.label l, 0))
    (hf : ((@Layout.frag (rLayout 0) 0 rDataP).take n).all (notLab l) = true) {c : BitVec 64}
    (hc : BitVec.ofNat 64 (rStart
      + (((@Layout.frag (rLayout 0) 0 rDataP).take n).map (·.2)).sum) = c) :
    @lab (rCE b) l = b.toBitVec + c := by
  have htake : ((rLayout b) rImg).2.take n = (@Layout.frag (rLayout 0) 0 rDataP).take n := by
    rw [← take_layout b, List.take_take, Nat.min_eq_left (by omega)]
  unfold lab
  rw [Executable.label_addrOf _ l n ?hn ?hf]
  · show ((b + Int64.ofNat rStart) + Int64.ofNat (((((rLayout b) rImg).2.take n).map (·.2)).sum)).toBitVec = _
    rw [htake, ← hc, Int64.toBitVec_add, Int64.toBitVec_add, BitVec.add_assoc]
    congr 1
    rw [Int64.toBitVec_ofNat', Int64.toBitVec_ofNat', BitVec.ofNat_add]
  case hn =>
    show ((rLayout b) rImg).2[n]? = _
    have h : ((rLayout b) rImg).2[n]? = (((rLayout b) rImg).2.take 104)[n]? :=
      (List.getElem?_take_of_lt hlt).symm
    rw [h, take_layout]
    exact hn
  case hf =>
    show ∀ dz ∈ ((rLayout b) rImg).2.take n, _
    rw [htake]
    intro dz hdz heq
    have := List.all_eq_true.mp hf dz hdz
    obtain ⟨d, z⟩ := dz
    simp only at heq
    subst heq
    simp [notLab] at this

theorem rlab_LCPI14_0 (b : Int64) : @lab (rCE b) "LCPI14_0" = b.toBitVec + 0x325ae8#64 :=
  rlabAt b _ 48 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_5 (b : Int64) : @lab (rCE b) "LCPI14_5" = b.toBitVec + 0x323de8#64 :=
  rlabAt b _ 26 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_6 (b : Int64) : @lab (rCE b) "LCPI14_6" = b.toBitVec + 0x324890#64 :=
  rlabAt b _ 30 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_9 (b : Int64) : @lab (rCE b) "LCPI14_9" = b.toBitVec + 0x324cf0#64 :=
  rlabAt b _ 36 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_10 (b : Int64) : @lab (rCE b) "LCPI14_10" = b.toBitVec + 0x325d78#64 :=
  rlabAt b _ 50 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_11 (b : Int64) : @lab (rCE b) "LCPI14_11" = b.toBitVec + 0x326c68#64 :=
  rlabAt b _ 54 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_12 (b : Int64) : @lab (rCE b) "LCPI14_12" = b.toBitVec + 0x3250c8#64 :=
  rlabAt b _ 38 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_13 (b : Int64) : @lab (rCE b) "LCPI14_13" = b.toBitVec + 0x3250d0#64 :=
  rlabAt b _ 40 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_14 (b : Int64) : @lab (rCE b) "LCPI14_14" = b.toBitVec + 0x3274f0#64 :=
  rlabAt b _ 60 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_15 (b : Int64) : @lab (rCE b) "LCPI14_15" = b.toBitVec + 0x326e78#64 :=
  rlabAt b _ 56 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_16 (b : Int64) : @lab (rCE b) "LCPI14_16" = b.toBitVec + 0x327b90#64 :=
  rlabAt b _ 64 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_17 (b : Int64) : @lab (rCE b) "LCPI14_17" = b.toBitVec + 0x324050#64 :=
  rlabAt b _ 28 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_3 (b : Int64) : @lab (rCE b) "LCPI14_3" = b.toBitVec + 0x320b00#64 :=
  rlabAt b _ 20 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_1 (b : Int64) : @lab (rCE b) "LCPI14_1" = b.toBitVec + 0x31cfc0#64 :=
  rlabAt b _ 18 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_2 (b : Int64) : @lab (rCE b) "LCPI14_2" = b.toBitVec + 0x314980#64 :=
  rlabAt b _ 8 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_8 (b : Int64) : @lab (rCE b) "LCPI14_8" = b.toBitVec + 0x30dfa0#64 :=
  rlabAt b _ 4 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_exp2_tab (b : Int64) : @lab (rCE b) "exp2_tab" = b.toBitVec + 0x318b70#64 :=
  rlabAt b _ 10 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_bw_tab (b : Int64) : @lab (rCE b) "bw_tab" = b.toBitVec + 0x3108c0#64 :=
  rlabAt b _ 6 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_limgain (b : Int64) : @lab (rCE b) "limgain" = b.toBitVec + 0x318b80#64 :=
  rlabAt b _ 12 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_sbr_qmf_window_ds (b : Int64) : @lab (rCE b) "sbr_qmf_window_ds" = b.toBitVec + 0x27340#64 :=
  rlabAt b _ 0 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ff_ps_neg (b : Int64) : @lab (rCE b) "ff_ps_neg" = b.toBitVec + 0x4322d0#64 :=
  rlabAt b _ 98 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ps_mask (b : Int64) : @lab (rCE b) "ps_mask" = b.toBitVec + 0x42b0e0#64 :=
  rlabAt b _ 86 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI19_0 (b : Int64) : @lab (rCE b) "LCPI19_0" = b.toBitVec + 0x327538#64 :=
  rlabAt b _ 62 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI19_1 (b : Int64) : @lab (rCE b) "LCPI19_1" = b.toBitVec + 0x324ce8#64 :=
  rlabAt b _ 34 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI19_2 (b : Int64) : @lab (rCE b) "LCPI19_2" = b.toBitVec + 0x31cdf0#64 :=
  rlabAt b _ 16 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ps_mask3 (b : Int64) : @lab (rCE b) "ps_mask3" = b.toBitVec + 0x42b100#64 :=
  rlabAt b _ 90 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_sbr_qmf_window_us (b : Int64) : @lab (rCE b) "sbr_qmf_window_us" = b.toBitVec + 0x27840#64 :=
  rlabAt b _ 2 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI15_1 (b : Int64) : @lab (rCE b) "LCPI15_1" = b.toBitVec + 0x325700#64 :=
  rlabAt b _ 44 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ps_mask2 (b : Int64) : @lab (rCE b) "ps_mask2" = b.toBitVec + 0x42b0f0#64 :=
  rlabAt b _ 88 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ff_sbr_noise_table (b : Int64) : @lab (rCE b) "ff_sbr_noise_table" = b.toBitVec + 0x47c3f0#64 :=
  rlabAt b _ 100 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ps_noise0 (b : Int64) : @lab (rCE b) "ps_noise0" = b.toBitVec + 0x42b110#64 :=
  rlabAt b _ 92 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ps_noise13 (b : Int64) : @lab (rCE b) "ps_noise13" = b.toBitVec + 0x42b130#64 :=
  rlabAt b _ 96 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_ps_noise2 (b : Int64) : @lab (rCE b) "ps_noise2" = b.toBitVec + 0x42b120#64 :=
  rlabAt b _ 94 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_6 (b : Int64) : @lab (rCE b) "LCPI17_6" = b.toBitVec + 0x3248a8#64 :=
  rlabAt b _ 32 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_7 (b : Int64) : @lab (rCE b) "LCPI17_7" = b.toBitVec + 0x325580#64 :=
  rlabAt b _ 42 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_8 (b : Int64) : @lab (rCE b) "LCPI17_8" = b.toBitVec + 0x326ef8#64 :=
  rlabAt b _ 58 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_9 (b : Int64) : @lab (rCE b) "LCPI17_9" = b.toBitVec + 0x325990#64 :=
  rlabAt b _ 46 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_10 (b : Int64) : @lab (rCE b) "LCPI17_10" = b.toBitVec + 0x323c30#64 :=
  rlabAt b _ 24 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_12 (b : Int64) : @lab (rCE b) "LCPI17_12" = b.toBitVec + 0x325f58#64 :=
  rlabAt b _ 52 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI14_4 (b : Int64) : @lab (rCE b) "LCPI14_4" = b.toBitVec + 0x321518#64 :=
  rlabAt b _ 22 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_LCPI17_11 (b : Int64) : @lab (rCE b) "LCPI17_11" = b.toBitVec + 0x31a680#64 :=
  rlabAt b _ 14 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rlab_pd_reverse (b : Int64) : @lab (rCE b) "pd_reverse" = b.toBitVec + 0x5614e0#64 :=
  rlabAt b _ 102 (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Alignment of a page-aligned base plus an aligned offset. -/
theorem aligned_add {x c : BitVec 64} {a : Nat} (ha : a = 16 ∨ a = 32) (hx : x.toNat % 4096 = 0)
    (hc : c.toNat % a = 0) : isAligned a (x + c) = true := by
  simp only [isAligned, BitVec.toNat_add, beq_iff_eq]
  rcases ha with rfl | rfl <;> omega

/-- The alignments `LayoutC` needs, at every page-aligned load bias (a PIE is mapped at a
multiple of the page size). -/
theorem rLab (b : Int64) (hb : b.toBitVec.toNat % 4096 = 0) : @LabAligned (rCE b) := by
  unfold LabAligned
  simp only [rlab_LCPI14_1, rlab_LCPI14_2, rlab_LCPI14_8, rlab_sbr_qmf_window_ds, rlab_ff_ps_neg,
    rlab_ps_mask, rlab_sbr_qmf_window_us, rlab_ps_mask2, rlab_ps_mask3, rlab_ps_noise0,
    rlab_ps_noise13, rlab_ps_noise2, rlab_pd_reverse]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩ <;>
    exact aligned_add (by decide) hb (by decide)

/-! ## The witnesses under the link-time layout

`Witness.wit_pre` builds the memory with the constants of `CstW` below `2 ^ 32` and every
other object above (from `0x200200000`). Under `rCE b` the constants lie at
`b + 0x27340 … b + 0x561500`, so that arrangement needs `b + 0x561500 ≤ 2 ^ 32`; the
witnesses take the link-time layout `b = 0`. -/

theorem rlab0 {l : Label} {c : BitVec 64} (h : @lab (rCE 0) l = (0 : Int64).toBitVec + c) :
    @lab (rCE 0) l = c := by
  rw [h]; simp

section Witnesses

/-- The link-time layout, as the ambient code of this section. -/
@[instance_reducible] def rCE0 : CodeEnv := rCE 0

attribute [local instance] rCE0

theorem rCst : SatIn CstW [(0, 2 ^ 32)] := by
  unfold CstW
  simp only [rlab0 (rlab_LCPI14_0 0), rlab0 (rlab_LCPI14_5 0), rlab0 (rlab_LCPI14_6 0),
    rlab0 (rlab_LCPI14_9 0), rlab0 (rlab_LCPI14_10 0), rlab0 (rlab_LCPI14_11 0),
    rlab0 (rlab_LCPI14_12 0), rlab0 (rlab_LCPI14_13 0), rlab0 (rlab_LCPI14_14 0),
    rlab0 (rlab_LCPI14_15 0), rlab0 (rlab_LCPI14_16 0), rlab0 (rlab_LCPI14_17 0),
    rlab0 (rlab_LCPI14_3 0), rlab0 (rlab_LCPI14_1 0), rlab0 (rlab_LCPI14_2 0),
    rlab0 (rlab_LCPI14_8 0), rlab0 (rlab_exp2_tab 0), rlab0 (rlab_bw_tab 0),
    rlab0 (rlab_limgain 0), rlab0 (rlab_sbr_qmf_window_ds 0), rlab0 (rlab_ff_ps_neg 0),
    rlab0 (rlab_ps_mask 0), rlab0 (rlab_LCPI19_0 0), rlab0 (rlab_LCPI19_1 0),
    rlab0 (rlab_LCPI19_2 0), rlab0 (rlab_ps_mask3 0), rlab0 (rlab_sbr_qmf_window_us 0),
    rlab0 (rlab_LCPI15_1 0), rlab0 (rlab_ps_mask2 0), rlab0 (rlab_ff_sbr_noise_table 0),
    rlab0 (rlab_ps_noise0 0), rlab0 (rlab_ps_noise13 0), rlab0 (rlab_ps_noise2 0),
    rlab0 (rlab_LCPI17_6 0), rlab0 (rlab_LCPI17_7 0), rlab0 (rlab_LCPI17_8 0),
    rlab0 (rlab_LCPI17_9 0), rlab0 (rlab_LCPI17_10 0), rlab0 (rlab_LCPI17_12 0),
    rlab0 (rlab_LCPI14_4 0), rlab0 (rlab_LCPI17_11 0), rlab0 (rlab_pd_reverse 0)]
  exact SatIn.widen 0 (2 ^ 32) (by sat_tac) (by decide +kernel)

theorem rLab0 : LabAligned := rLab 0 (by decide)

/-- SCE (the V1 case), as `Linked.linked_hyps_sat_sce`, under the binary's image. -/
theorem real_hyps_sat_sce : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced (rCE 0) ∧ @SbrSlots (rCE 0) e ∧ @ApplyPre (rCE 0) k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac
    ∧ 1 ≤ x.d0.nenv ∧ u8 x.d0.te 0 < u8 x.d0.te 1 ∧ u8 x.d0.te 1 ≤ 19
    ∧ x.d1 = dvMalloc ∧ x.d1.nenv = 0 ∧ x.d1.vOff = 1152 ∧ x.d0.vOff = 1152 ∧ dsN x = 1 := by
  obtain ⟨t, ht, h⟩ := wit_pre xSce 0 0 rCst rLab0 wf_sce rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xSce, 0, t, rPlaced 0, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, rfl, rfl, rfl, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

/-- SCE with parametric stereo, as `Linked.linked_hyps_sat_ps`, under the binary's image. -/
theorem real_hyps_sat_ps : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced (rCE 0) ∧ @SbrSlots (rCE 0) e ∧ @ApplyPre (rCE 0) k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac ∧ 1 ≤ x.d0.nenv
    ∧ x.ps ≠ 0 ∧ i32 x.psc 0 ≠ 0 ∧ 1 ≤ i32 x.psc 44 ∧ i32 x.psc 52 = -1
    ∧ i32 x.psc (52 + 4 * (i32 x.psc 44).toNat) = 31 ∧ i32 x.psc 4 ≠ 0 ∧ i32 x.psc 12 = 20
    ∧ i8 x.psc 76 ≠ 0 := by
  obtain ⟨t, ht, h⟩ := wit_pre xPs 0 0 rCst rLab0 wf_ps rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xPs, 0, t, rPlaced 0, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

/-- CPE, as `Linked.linked_hyps_sat_cpe`, under the binary's image. -/
theorem real_hyps_sat_cpe : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced (rCE 0) ∧ @SbrSlots (rCE 0) e ∧ @ApplyPre (rCE 0) k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 1 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac
    ∧ 1 ≤ x.d0.nenv ∧ 1 ≤ x.d1.nenv
    ∧ dsN x = 0 ∧ x.d0.vOff = 1152 ∧ x.d1.vOff = 1152 := by
  obtain ⟨t, ht, h⟩ := wit_pre xCpe 0 1 rCst rLab0 wf_cpe rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xCpe, 0, t, rPlaced 0, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, rfl⟩
  rw [wArg2 ht]; decide +kernel

/-- The larger `qmfVSize` window, as `Linked.linked_hyps_sat_a3`, under the binary's image. -/
theorem real_hyps_sat_a3 : ∃ (k : Nat) (e : Env) (x : Args) (ra : Int64) (t : MachineData),
    @SbrPlaced (rCE 0) ∧ @SbrSlots (rCE 0) e ∧ @ApplyPre (rCE 0) k e x ra t
    ∧ x.start = 1 ∧ x.idAac = 0 ∧ BitVec.setWidth 32 (arg2 t) = x.idAac ∧ 1 ≤ x.d0.nenv
    ∧ dsN x = 0 ∧ 1152 < x.d0.vOff.toInt ∧ x.d0.vOff.toInt ≤ 1664 := by
  obtain ⟨t, ht, h⟩ := wit_pre xA3 0 0 rCst rLab0 wf_a3 rfl rfl rfl rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨wK, wEnv, xA3, 0, t, rPlaced 0, wEnv_slots, h, rfl, rfl, ?_, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩
  rw [wArg2 ht]; decide +kernel

end Witnesses

end Kraken.Examples.Sbr.Real
