"""Skeleton: frame split lemmas, Post', hpre/hpost, spec dispatch."""
import re
R = "t₀.regs.get64 .rsp"


def labels():
    out = []
    for line in open(__file__.replace("skel.py", "body.s")):
        m = re.match(r"^(sbr_hf_assemble[\w.]*):\s*$", line)
        if m:
            nm = m.group(1)
            out.append("" if nm == "sbr_hf_assemble" else nm.split(".", 1)[1])
    return out


def split_chain(r, base, sizes):
    """rewrite chain turning `sum ?@ (r - base)` into cells of `sizes`."""
    tac = []
    n = sum(sizes)
    o = base
    for sz in sizes[:-1]:
        rest = n - sz
        tac.append(f"  rw [show ({n} ?@ ({r} - {o:#x}#64) : Mem 64 → Prop) = ({sz} + {rest}) ?@ ({r} - {o:#x}#64) from rfl,\n"
                   f"    Block.split ({r} - {o:#x}#64) {sz} {rest} (by decide), show {r} - {o:#x}#64 + BitVec.ofNat 64 {sz} = {r} - {o - sz:#x}#64 by bv_omega]")
        n = rest
        o -= sz
    return "\n".join(tac)


def slot_cell_sizes(g):
    out = []
    for name, off, size in g.SLOTS:
        for c in g.cell(name, off, size, None):
            out.append(int(c.split(" ?@")[0]))
    return out


def frame_sizes(g):
    sizes = slot_cell_sizes(g) + [8] * 6
    assert sum(sizes) == 0x288, hex(sum(sizes))
    return sizes


def chain_cells(r, base, sizes, tail):
    cs = []
    o = base
    for sz in sizes:
        cs.append(f"{sz} ?@ ({r} - {o:#x}#64)")
        o -= sz
    return " ⋆ (".join(cs) + f" ⋆ {tail}" + ")" * (len(cs) - 1)


def lemmas(g):
    sizes = frame_sizes(g)
    r = "r"
    out = []
    out.append(f"""omit [CodeEnv] in
/-- The 0x288 bytes of the frame as its slots (all blank). -/
theorem frame_cells (r : BitVec 64) (K : Mem 64 → Prop) :
    0x288 ?@ (r - 0x288#64) ⋆ K = {chain_cells(r, 0x288, sizes, 'K')} := by
{split_chain(r, 0x288, sizes)}
  simp only [Std.ExtHashMap.sep_assoc]
""")
    zs = [0x258] + [8] * 6
    out.append(f"""omit [CodeEnv] in
/-- The frame at the exit: 0x258 blank bytes under the six saved-register slots. -/
theorem frame_exit (r : BitVec 64) (K : Mem 64 → Prop) :
    0x288 ?@ (r - 0x288#64) ⋆ K = {chain_cells(r, 0x288, zs, 'K')} := by
{split_chain(r, 0x288, zs)}
  simp only [Std.ExtHashMap.sep_assoc]

/-- The saved registers' slots. -/
abbrev Saved (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  c8 (r - 0x30#64) (t₀.regs.get64 .rbx)
    ⋆ (c8 (r - 0x28#64) (t₀.regs.get64 .r12)
    ⋆ (c8 (r - 0x20#64) (t₀.regs.get64 .r13)
    ⋆ (c8 (r - 0x18#64) (t₀.regs.get64 .r14)
    ⋆ (c8 (r - 0x10#64) (t₀.regs.get64 .r15)
    ⋆ (c8 (r - 0x8#64) (t₀.regs.get64 .rbp) ⋆ K)))))

/-- The frame at `.Lb820` and `.done`: the spill area forgotten. -/
abbrev FZ (x : HfArgs) (t₀ : MachineData) (K : Mem 64 → Prop) : Mem 64 → Prop :=
  0x258 ?@ (t₀.regs.get64 .rsp - 0x288#64) ⋆ Saved t₀ K

omit [CodeEnv] in
theorem Saved_blank (t₀ : MachineData) (K : Mem 64 → Prop) :
    Mem.Entails (Saved t₀ K)
      ({chain_cells(R, 0x30, [8] * 6, 'K')}) :=
  Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _ (Mem.Entails.forget8 _ _
    (Mem.Entails.forget8 _ _ (Mem.Entails.refl _))))))

omit [CodeEnv] in
theorem off_toNat (a : BitVec 64) (b c o : Nat) (hb : b ≤ c) (hc : c < 2 ^ 32) (ho : o < 2 ^ 32) :
    (a + BitVec.ofNat 64 c + BitVec.ofNat 64 o - (a + BitVec.ofNat 64 b)).toNat = c - b + o := by
  have : a + BitVec.ofNat 64 c + BitVec.ofNat 64 o - (a + BitVec.ofNat 64 b) = BitVec.ofNat 64 (c - b + o) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [this, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem off_toNat0 (a : BitVec 64) (b c : Nat) (hb : b ≤ c) (hc : c < 2 ^ 32) :
    (a + BitVec.ofNat 64 c - (a + BitVec.ofNat 64 b)).toNat = c - b := by
  have := off_toNat a b c 0 hb hc (by decide)
  simpa using this

omit [CodeEnv] in
/-- `3 * te << 7` of a zero-extended byte, as the code computes a `g_temp` row offset. -/
theorem te_row (v : Int) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 v))
      + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 8 v)) * 2#64) <<< 7)
      = BitVec.ofNat 64 (384 * (v % 256).toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, Nat.shiftLeft_eq]
  have hw : (v % 256).toNat < 256 := by omega
  generalize (v % 256).toNat = w at *
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- A `memcpy` footprint: `n` bytes at `arg3 + c1 + o1` inside `g_temp`/`q_temp`
and `n` bytes at `arg2 + c2` inside `sbr->q_m`/`s_m`/`gain`. -/
theorem DataW_carve_mc (x : HfArgs) (t : MachineData) (c1 o1 c2 n : Nat) (h1 : 0x11130 ≤ c1)
    (h1' : c1 - 0x11130 + o1 + n ≤ 16128) (hc1 : c1 < 2 ^ 32) (ho1 : o1 < 2 ^ 32)
    (h2 : 0x5eac0 ≤ c2) (h2' : c2 - 0x5eac0 + n ≤ 4608) (hc2 : c2 < 2 ^ 32) :
    ∃ H, DataW x t = Blocks [(arg3 t + BitVec.ofNat 64 c1 + BitVec.ofNat 64 o1, n),
      (arg2 t + BitVec.ofNat 64 c2, n)] ⋆ H := by
  obtain ⟨H1, e1⟩ := Block.carve_ex (a := arg3 t + 0x11130#64) (b := arg3 t + BitVec.ofNat 64 c1 + BitVec.ofNat 64 o1)
    (len := 16128) (n := n) (by rw [off_toNat _ _ _ _ h1 hc1 ho1]; omega) (by omega)
  obtain ⟨H2, e2⟩ := Block.carve_ex (a := arg2 t + 0x5eac0#64) (b := arg2 t + BitVec.ofNat 64 c2)
    (len := 4608) (n := n) (by rw [off_toNat0 _ _ _ h2 hc2]; omega) (by omega)
  refine ⟨H2 ⋆ (H1 ⋆ DataWGS x t), ?_⟩
  rw [DataW_GS, e1, e2]
  rcases n with _ | n
  · simp only [Blocks, Std.ExtHashMap.sep_assoc]; ac_rfl
  · simp only [Blocks, Std.ExtHashMap.sep_assoc]; ac_rfl

theorem reserve_frame (k : Nat) {{r : BitVec 64}} (hw : 0x290 + k ≤ r.toNat) (K : Mem 64 → Prop) :
    Reserve (0x290 + k) r ⋆ K
      = 8 ?@ (r - 0x290#64) ⋆ (Reserve k (r - 0x290#64) ⋆ (0x288 ?@ (r - 0x288#64) ⋆ K)) :=
  Reserve_split_frame 0x290 k (by decide) r (by omega) K
""")
    return "\n".join(out)


POST = """
/-- What the exit block leaves. -/
abbrev Post' (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ s : MachineData) : Prop :=
  let r := t₀.regs.get64 .rsp
  HfC x t₀ ∧ s.regs.get64 .rsp = r + 8 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ 8 ?@ (r - 0x290#64) ⋆ (Reserve k (r - 0x290#64) ⋆ (DataW x t₀ ⋆ (ScW x t₀ ⋆ (FnW fs t₀
    ⋆ (TeW x t₀ ⋆ (EaW x t₀ ⋆ (HfIdxOut t₀ ⋆ FZ x t₀ (8 ?@ r ⋆ x.R)))))))))
"""


def false_block(l):
    nm = l or "start"
    return f"""theorem blk_{nm} (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.{l}" := by
  intro blk _ n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact hs₀.1.elim
"""


def spec(g):
    labs = labels()
    full = [f'"sbr_hf_assemble{"." + l if l else ""}"' for l in labs]
    lablist = "[" + ",\n        ".join(", ".join(full[i:i + 4]) for i in range(0, len(full), 4)) + "]"
    # `∀ l ∈ [l₁, …], BlockOb … l` from the block theorems, one `forall_mem_cons` per label
    hall = "List.forall_mem_nil _"
    for l in reversed(labs):
        hall = f"List.forall_mem_cons.2 ⟨blk_{l or 'start'} k hk fs hc x ra t₀,\n      {hall}⟩"
    sz = frame_sizes(g)
    return f"""
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
    simp only [List.map_cons, List.map_nil] at hmem
    have hall : ∀ l ∈ ({lablist} : List Label), BlockOb k fs x ra t₀ l :=
      {hall}
    exact hall l hmem blk hblk
  · -- hpre
    rintro x ra t ⟨hm, hC⟩
    refine ⟨rfl, hC, ?_⟩
    have hw := CallPre.le hm
    simp only [CallPre, hfNeed] at hm
    rw [reserve_frame k hw, frame_cells] at hm
    simp only [T, Rest, FA, ScW, FnW, TeW, EaW, IdxC, HfF] at hm ⊢
    rw [DataW_eq x t (hfc_ypos hC) (hfc_y1 hC)] at hm
    exact Mem.ac hm
  · -- hpost
    rintro x ra t₀ s ⟨h0, -⟩ ⟨hC, h1, h2, h3, hm⟩
    refine ⟨h1, h2, h3, ?_⟩
    have hm' := Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
      (Mem.Entails.sep_left (Saved_blank t₀ _))))))))) _ hm
    rw [show hfNeed k = 0x290 + k from rfl, reserve_frame k (CallPre.le h0), frame_exit]
    simp only [HfFPost, ScW, FnW, TeW, EaW] at hm' ⊢
    rw [DataW_eq x t₀ (hfc_ypos hC) (hfc_y1 hC)]
    exact Mem.ac hm'
"""


def exit_lemmas(g, frames):
    """FZ cells split + `<FR>_exit` entailments + T_exit."""
    slot_sizes = slot_cell_sizes(g)
    assert sum(slot_sizes) == 0x258
    out = [f"""omit [CodeEnv] in
theorem fz_cells (r : BitVec 64) (K : Mem 64 → Prop) :
    0x258 ?@ (r - 0x288#64) ⋆ K = {chain_cells('r', 0x288, slot_sizes, 'K')} := by
{split_chain('r', 0x288, slot_sizes)}
  simp only [Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
/-- `q_temp` row minus `0x1f80` is the `g_temp` row. -/
theorem qrow_g (a o : BitVec 64) : a + 0x130b0#64 + o + Int64.toBitVec (-8064) = a + 0x11130#64 + o := by
  rw [show Int64.toBitVec (-8064) = 0xffffffffffffe080#64 from rfl]; bv_omega

omit [CodeEnv] in
theorem s38_join (r : BitVec 64) (K : Mem 64 → Prop) :
    4 ?@ (r - 0x40#64) ⋆ K = 1 ?@ (r - 0x40#64) ⋆ (3 ?@ (r - 0x3f#64) ⋆ K) := by
  rw [show (4 ?@ (r - 0x40#64) : Mem 64 → Prop) = (1 + 3) ?@ (r - 0x40#64) from rfl,
    Block.split (r - 0x40#64) 1 3 (by decide), show r - 0x40#64 + BitVec.ofNat 64 1 = r - 0x3f#64 by bv_omega,
    Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem s38_join8 (r : BitVec 64) (K : Mem 64 → Prop) :
    8 ?@ (r - 0x40#64) ⋆ K = 4 ?@ (r - 0x40#64) ⋆ (4 ?@ (r - 0x3c#64) ⋆ K) := by
  rw [show (8 ?@ (r - 0x40#64) : Mem 64 → Prop) = (4 + 4) ?@ (r - 0x40#64) from rfl,
    Block.split (r - 0x40#64) 4 4 (by decide), show r - 0x40#64 + BitVec.ofNat 64 4 = r - 0x3c#64 by bv_omega,
    Std.ExtHashMap.sep_assoc]

omit [CodeEnv] in
theorem s38_split0 (q : BitVec 64) (K : Mem 64 → Prop) :
    4 ?@ (q - 64#64) ⋆ K = 1 ?@ (q - 64#64) ⋆ (3 ?@ (q - 63#64) ⋆ K) := by
  rw [show (4 ?@ (q - 64#64) : Mem 64 → Prop) = (1 + 3) ?@ (q - 64#64) from rfl,
    Block.split (q - 64#64) 1 3 (by decide), show q - 64#64 + BitVec.ofNat 64 1 = q - 63#64 by bv_omega,
    Std.ExtHashMap.sep_assoc]

theorem T_forget (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData)
    (IC : Mem 64 → Prop) (F1 F2 : (Mem 64 → Prop) → Mem 64 → Prop) (h : ∀ K, Mem.Entails (F1 K) (F2 K)) :
    Mem.Entails (T k fs x ra t₀ IC F1) (T k fs x ra t₀ IC F2) := by
  simp only [T]
  exact Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.sep_left (h _))))))))

theorem T_exit (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (h : ∀ K, Mem.Entails (FR K) (FZ x t₀ K)) :
    Mem.Entails (T k fs x ra t₀ (IdxC x t₀) FR) (T k fs x ra t₀ (8 ?@ (arg3 t₀ + 0x15aac#64)) (FZ x t₀)) := by
  simp only [T, IdxC]
  exact Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.sep_left (Mem.Entails.sep_left (Mem.Entails.sep_left
    (Mem.Entails.forget8 _ _ (h _))))))))
"""]
    for fr in frames:
        vals, sv, params = g.FRAMES[fr]
        term = "Mem.Entails.refl _"
        cells = []
        for name, off, size in g.SLOTS:
            cells += [(name, size, c) for c in g.cell(name, off, size, vals.get(name))]
        for name, size, c in reversed(cells):
            if "?@" in c:
                term = f"Mem.Entails.sep_left ({term})"
            elif c.startswith("c8 "):
                term = f"Mem.Entails.forget8 _ _ ({term})"
            else:
                term = f"Mem.Entails.forget (Mem.Split.here _ _) ({term}) (by simp [Int.toBytes_length]) (by decide)"
        out.append(f"""omit [CodeEnv] in
theorem {fr}_exit (x : HfArgs) (t₀ : MachineData){params} (K : Mem 64 → Prop) :
    Mem.Entails ({fr} x t₀{''.join(' ' + p for p in g.pnames(fr))} K) (FZ x t₀ K) := by
  simp only [{fr}, FZ, Saved, c8]
  rw [fz_cells{", s38_join" if isinstance(vals.get("s38"), tuple) and vals["s38"][0] == "b" else ""}{", ← s38_join8" if isinstance(vals.get("s38"), tuple) and vals["s38"][0] == "q" else ""}]
  exact {term}
""")
    return "\n".join(out)
