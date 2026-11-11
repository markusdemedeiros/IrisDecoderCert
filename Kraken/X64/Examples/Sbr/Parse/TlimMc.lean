import Kraken.X64.Examples.Sbr.Parse.TlimBlkE

/-!
# `sbr_make_f_tablelim`: the two `memcpy` calls (`L3fcc`, `L400a`)

The footprint `memcpy` gets: the source bytes and the destination prefix of `f_tablelim`; the
rest of `T` (with the other parts of `f_tablelim` and of the source split off) is its frame.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

/-! ## Splitting a cell -/

theorem cell_split (l : List UInt8) (a : BitVec 64) (n : Nat) (hn : n ≤ l.length)
    (hw : l.length ≤ 2 ^ 64) :
    (l =@ a) = (l.take n =@ a ⋆ l.drop n =@ (a + BitVec.ofNat 64 n)) := by
  have e := At_append_sep (l.take n) (l.drop n) a
    (by simp only [List.length_take, List.length_drop]; omega)
  rw [List.take_append_drop] at e
  simp only [Mem.Val.eq, e, List.length_take, Nat.min_eq_left hn]

theorem append_split (l₁ l₂ : List UInt8) (a : BitVec 64) (hw : l₁.length + l₂.length ≤ 2 ^ 64) :
    ((l₁ ++ l₂) =@ a) = (l₁ =@ a ⋆ l₂ =@ (a + BitVec.ofNat 64 l₁.length)) := by
  rw [Mem.Val.eq, At_append_sep _ _ _ hw]
  rfl

theorem getD_take_drop (a b : List UInt8) (n i : Nat) (ha : n ≤ a.length) (_hb : n ≤ b.length) :
    (a.take n ++ b.drop n).getD i 0 = if i < n then a.getD i 0 else b.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simp only [List.length_take]; omega)]
    simp only [List.getElem?_take, h, ↓reduceIte]
  · rw [List.getElem?_append_right (by simp only [List.length_take]; omega)]
    simp only [List.length_take, List.getElem?_drop, h, ↓reduceIte, Nat.min_eq_left ha]
    congr 2; omega

theorem u16_take_drop (a b : List UInt8) (n q : Nat) (ha : 2 * n ≤ a.length)
    (hb : 2 * n ≤ b.length) :
    u16 (a.take (2 * n) ++ b.drop (2 * n)) q = if q < n then u16 a q else u16 b q := by
  simp only [u16, u8, getD_take_drop a b _ _ ha hb]
  by_cases h : q < n
  · simp only [show 2 * q < 2 * n by omega, show 2 * q + 1 < 2 * n by omega, h, ↓reduceIte]
  · simp only [show ¬ 2 * q < 2 * n by omega, show ¬ 2 * q + 1 < 2 * n by omega, h, ↓reduceIte]

theorem u16_app (a b : List UInt8) (n q : Nat) (ha : a.length = 2 * n) :
    u16 (a ++ b) q = if q < n then u16 a q else u16 b (q - n) := by
  simp only [u16, u8, List.getD_eq_getElem?_getD]
  by_cases h : q < n
  · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    simp only [h, ↓reduceIte]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    simp only [h, ↓reduceIte, ha]
    rw [show 2 * q - 2 * n = 2 * (q - n) by omega, show 2 * q + 1 - 2 * n = 2 * (q - n) + 1 by omega]

theorem u16_take' (l : List UInt8) (m n q : Nat) (hm : m = 2 * n) (hq : q < n) :
    u16 (l.take m) q = u16 l q := by
  subst hm
  simp only [u16, u8, List.getD_eq_getElem?_getD, List.getElem?_take,
    show 2 * q < 2 * n by omega, show 2 * q + 1 < 2 * n by omega, ↓reduceIte]

theorem u16_drop' (l : List UInt8) (m n q : Nat) (hm : m = 2 * n) :
    u16 (l.drop m) q = u16 l (q + n) := by
  subst hm
  simp only [u16, u8, List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [show 2 * n + 2 * q = 2 * (q + n) by omega, show 2 * n + (2 * q + 1) = 2 * (q + n) + 1 by omega]

theorem rdx2 (n : Nat) (h : n < 2 ^ 31) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + 1#64))
      + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n + 1#64))).toNat = 2 * (n + 1) := by
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sub448_8 (r : BitVec 64) : r - 0x448#64 - 8#64 = r - 0x450#64 := by bv_omega
theorem add450_8 (r : BitVec 64) : r - 0x450#64 + 8#64 = r - 0x448#64 := by bv_omega

theorem rbp_pb2 (r : BitVec 64) :
    r - 8#64 + 18446744073709551572#64 = r - 0x36#64 + BitVec.ofNat 64 2 := by bv_omega

theorem rdi_dst (p : BitVec 64) (n : Nat) (h : n < 2 ^ 31) :
    BitVec.setWidth 64 2#64 + (p + BitVec.ofNat 64 n * 2#64) = p + BitVec.ofNat 64 (2 * (n + 1)) := by
  bv_omega

theorem rdx3 (n : Nat) (h1 : 1 ≤ n) (h : n < 2 ^ 31) :
    (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) - 1#32)
      + BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n) - 1#32)).toNat = 2 * (n - 1) := by
  bv_omega

variable [CodeEnv]

/-! ## The first copy: `f_tablelow[0..n] → f_tablelim[0..n]` -/

omit [CodeEnv] in
theorem perm1 (a8 rs tf df nl sk pb jk tl dl ro fr : Mem 64 → Prop) :
    a8 ⋆ (rs ⋆ ((tf ⋆ df) ⋆ (nl ⋆ (sk ⋆ (pb ⋆ (jk ⋆ (((tl ⋆ dl) ⋆ ro) ⋆ fr))))))) =
    tf ⋆ (a8 ⋆ (rs ⋆ (tl ⋆ (df ⋆ (dl ⋆ (ro ⋆ (nl ⋆ (sk ⋆ (pb ⋆ (jk ⋆ fr)))))))))) := by
  ac_rfl

omit [CodeEnv] in
theorem perm2 (a8 rs tf df nl sk pb jk tl dl ro fr : Mem 64 → Prop) :
    a8 ⋆ (rs ⋆ ((tl ⋆ tf) ⋆ (df ⋆ (dl ⋆ (ro ⋆ (nl ⋆ (sk ⋆ (pb ⋆ (jk ⋆ fr))))))))) =
    a8 ⋆ (rs ⋆ ((tf ⋆ df) ⋆ (nl ⋆ (sk ⋆ (pb ⋆ (jk ⋆ (((tl ⋆ dl) ⋆ ro) ⋆ fr))))))) := by
  ac_rfl

/-- The read-only group without `f_tablelow`. -/
def ROx (x : TArgs) (t₀ : MachineData) : Mem 64 → Prop :=
  let s := sA t₀
  cell4 (s + 0x2c#64) x.lb ⋆ (c4 (s + 0x58#64) x.a.kx1 ⋆ (c4 (s + 0x4c1e0#64) x.a.n0
    ⋆ (c4 (s + 0x4c330#64) x.a.npatch ⋆ (x.a.pnum =@ (s + 0x4c334#64) ⋆ Blocks [(BW, 12)]))))

theorem RO_eq (x : TArgs) (t₀ : MachineData) :
    RO x t₀ = x.a.ftLow =@ (sA t₀ + 0x4c252#64) ⋆ ROx x t₀ := by
  simp only [RO, ROx]; ac_rfl

/-- The frame of the first copy (`n` bytes). -/
def Mc1G (x : TArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (st : TSt) (n : Nat) : Mem 64 → Prop :=
  st.fl.drop n =@ (pA t₀ + BitVec.ofNat 64 n)
    ⋆ (x.a.ftLow.drop n =@ (sA t₀ + 0x4c252#64 + BitVec.ofNat 64 n)
    ⋆ (ROx x t₀ ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (rS t₀ - 0x448#64)
    ⋆ (st.pb =@ (rS t₀ - 0x36#64) ⋆ (Junk (rS t₀) ⋆ FR (Rest x.R ra t₀)))))))

theorem mc1_pre {k : Nat} {x : TArgs} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt} {m : Mem 64} (n : Nat)
    (h : m =⋆ T k x ra t₀ FR st) (hfl : st.fl.length = 60) (hlow : x.a.ftLow.length = 50)
    (hn : n ≤ 50) :
    m =⋆ 8 ?@ (rS t₀ - 0x450#64) ⋆ (Reserve k (rS t₀ - 0x450#64)
      ⋆ ((x.a.ftLow.take n =@ (sA t₀ + 0x4c252#64) ⋆ n ?@ pA t₀) ⋆ Mc1G x ra t₀ FR st n)) := by
  simp only [T] at h
  rw [RO_eq] at h
  rw [cell_split st.fl _ n (by omega) (by omega),
    cell_split x.a.ftLow _ n (by omega) (by omega)] at h
  rw [perm1] at h
  have h1 : m =⋆ st.fl.take n =@ pA t₀ ⋆ (8 ?@ (rS t₀ - 0x450#64)
    ⋆ (Reserve k (rS t₀ - 0x450#64) ⋆ (x.a.ftLow.take n =@ (sA t₀ + 0x4c252#64)
    ⋆ Mc1G x ra t₀ FR st n))) := by simp only [Mc1G]; exact h
  have h2 := Block.sep_intro (len := n) (by simp only [List.length_take]; omega) (by omega) h1
  exact Mem.ac h2 (by ac_rfl)

theorem mc1_post {k : Nat} {x : TArgs} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt} {m : Mem 64} (n : Nat)
    (hfl : st.fl.length = 60) (hlow : x.a.ftLow.length = 50) (hn : n ≤ 50)
    (h : m =⋆ 8 ?@ (rS t₀ - 0x450#64) ⋆ (Reserve k (rS t₀ - 0x450#64)
      ⋆ ((x.a.ftLow.take n =@ (sA t₀ + 0x4c252#64) ⋆ x.a.ftLow.take n =@ pA t₀)
      ⋆ Mc1G x ra t₀ FR st n))) :
    m =⋆ T k x ra t₀ FR ⟨x.a.ftLow.take n ++ st.fl.drop n, st.nl, st.stk, st.pb⟩ := by
  simp only [T]
  rw [RO_eq, append_split _ _ _ (by simp only [List.length_take, List.length_drop]; omega),
    cell_split x.a.ftLow _ n (by omega) (by omega)]
  simp only [List.length_take, Nat.min_eq_left (show n ≤ x.a.ftLow.length by omega)]
  simp only [Mc1G] at h
  rw [perm2] at h
  exact h

theorem blk_L3fcc (k : Nat) (_hk : k ≤ 2 ^ 32) (hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L3fcc" := by
  cfg_block
  measure_hb "L3fcc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, stk, pb, hL, hP, hm⟩, hn⟩ := hs₀
    rw [var_L3fcc] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, -, -, hlow, hlim, -⟩ := hC'
    have hld := RO_n0 (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hld
    have ej : s₀.regs.get64 .rbp + 18446744073709551564#64 = rS t₀ - 0x3c#64 := by
      rw [hbp]; simp only [rS]; bv_omega
    have hj : ∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551564#64) 4 v =⋆
        T k x ra t₀ (Saved t₀) (st0 x stk pb) := fun v => by
      rw [ej]
      exact focus (T_j k x ra t₀ (Saved t₀) _).symm (Block.storeInt_split
        (focus (T_j k x ra t₀ (Saved t₀) _) hm) (Split.left (Split.right (Split.here _ _) _) _)
        (by simp) v)
    have hl34 : (s₀.dmem.loadInt (s₀.regs.get64 .rbp + 18446744073709551564#64) 4).isSome = true := by
      have h := focus (T_j k x ra t₀ (Saved t₀) _) hm
      simp only [Junk] at h
      obtain ⟨F, h⟩ := pick_lr h
      obtain ⟨F, h⟩ := pick_ll h
      rw [ej]
      exact slot_load h (by omega)
    have hldn : ∀ v, (s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551564#64) 4 v).loadInt
        (s₀.regs.get64 .rbx + 311776#64) 4 = some (Int.ofBytes (Int.toBytes 4 (x.a.n0 : Int))) :=
      fun v => by
        have h := RO_n0 (focus (T_ro k x ra t₀ (Saved t₀) _) (hj v))
        rwa [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at h
    have hpre := fun v => mc1_pre (2 * (x.a.n0 + 1)) (hj v) hlim hlow (by omega)
    have hld8 : ∀ v, ((s₀.dmem.storeInt (s₀.regs.get64 .rbp + 18446744073709551564#64) 4 v).loadInt
        (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := fun v => by
      rw [hsp, sub448_8]
      exact Block.loadInt_isSome (hpre v) (by simp)
    have hpush : Hide _ := fun v w => Block.storeInt_val (hpre v) (Split.here _ _) w
    have hjH : Hide _ := hj
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = rS t₀ - 0x450#64 := by
      rw [hsp]; exact sub448_8 _
    have elen := rdx2 x.a.n0 (by omega)
    clear hm hj hpre hld
    vcgen [MachineWP.call_proc_spec_at (⟨Mc1G x ra t₀ (Saved t₀) (st0 x stk pb) (2 * (x.a.n0 + 1)),
      x.a.ftLow.take (2 * (x.a.n0 + 1))⟩ : McA) "memcpy" hMc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm, BitVec.toNat_ofNat,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.ofNat_eq_ofNat, AddrIndex.offset64_none,
      BitVec.add_zero, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hld8, hldn, hl34,
      Option.isSome_some, Option.some.injEq, true_and, and_true] at *
    all_goals try subst_vars
    all_goals simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_toInt,
      BitVec.ofInt_natCast, zx_small _ (show x.a.n0 < 2 ^ 31 by omega)] at *
    intro ra'
    refine ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩
    · rw [e8, elen, hbx]
      unfold Hide at hpush
      exact hpush _ _
    · rw [elen, List.length_take, hlow]; omega
    · obtain ⟨hsp', hbp', ⟨hbx', -, h13', h14', h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      rw [tab_L3ff5, var_L3ff5]
      rw [e8, hbx] at hm'
      have hL' := hL
      obtain ⟨-, hL2, hL3⟩ := hL'
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, ?_, h15', x.a.ftLow.take (2 * (x.a.n0 + 1)) ++ x.a.ftLim.drop (2 * (x.a.n0 + 1)),
        stk, pb, ⟨?_, hL2, hL3⟩, hP, ?_,
        mc1_post (st := st0 x stk pb) _ hlim hlow (by omega) hm'⟩, by decide⟩
      · rw [hsp', e8]; exact add450_8 _
      · rw [hbp', hbp]
      · rw [h13', h13]
      · rw [hbx', hbx]
      · rw [h14', hbx]
      · simp only [List.length_append, List.length_take, List.length_drop, hlow, hlim]
        all_goals omega
      · intro q
        simp only [AV]
        rw [u16_take_drop _ _ _ _ (by omega) (by omega)]
        by_cases hq : q ≤ x.a.n0
        · simp only [hq, show q < x.a.n0 + 1 by omega, ↓reduceIte]
        · simp only [hq, show ¬ q < x.a.n0 + 1 by omega, ↓reduceIte]

/-! ## The second copy: `patch_borders[1..np) → f_tablelim[n+1..n+np)` -/

omit [CodeEnv] in
theorem perm3 (a8 rs fa fb fc nl sk pa pm pc jk ro fr : Mem 64 → Prop) :
    a8 ⋆ (rs ⋆ ((fa ⋆ (fb ⋆ fc)) ⋆ (nl ⋆ (sk ⋆ ((pa ⋆ (pm ⋆ pc)) ⋆ (jk ⋆ (ro ⋆ fr))))))) =
    fb ⋆ (a8 ⋆ (rs ⋆ (pm ⋆ (fa ⋆ (fc ⋆ (pa ⋆ (pc ⋆ (ro ⋆ (nl ⋆ (sk ⋆ (jk ⋆ fr))))))))))) := by
  ac_rfl

omit [CodeEnv] in
theorem perm5 (a8 rs fa fb fc nl sk pa pm pc jk ro fr : Mem 64 → Prop) :
    a8 ⋆ (rs ⋆ ((pm ⋆ fb) ⋆ (fa ⋆ (fc ⋆ (pa ⋆ (pc ⋆ (ro ⋆ (nl ⋆ (sk ⋆ (jk ⋆ fr)))))))))) =
    a8 ⋆ (rs ⋆ ((fa ⋆ (fb ⋆ fc)) ⋆ (nl ⋆ (sk ⋆ ((pa ⋆ (pm ⋆ pc)) ⋆ (jk ⋆ (ro ⋆ fr))))))) := by
  ac_rfl

omit [CodeEnv] in
theorem perm6 (a8 rs fa fb fc nl sk pa pm pc jk ro fr : Mem 64 → Prop) :
    a8 ⋆ (rs ⋆ ((pm ⋆ fb) ⋆ (fa ⋆ (fc ⋆ (pa ⋆ (pc ⋆ (ro ⋆ (nl ⋆ (sk ⋆ (jk ⋆ fr)))))))))) =
    fb ⋆ (a8 ⋆ (rs ⋆ (pm ⋆ (fa ⋆ (fc ⋆ (pa ⋆ (pc ⋆ (ro ⋆ (nl ⋆ (sk ⋆ (jk ⋆ fr))))))))))) := by
  ac_rfl

/-- The frame of the second copy (`f_tablelim` bytes `[d, d + L)` written from
`patch_borders` bytes `[2, 2 + L)`). -/
def Mc2G (x : TArgs) (ra : Int64) (t₀ : MachineData)
    (FR : (Mem 64 → Prop) → Mem 64 → Prop) (st : TSt) (d L : Nat) : Mem 64 → Prop :=
  st.fl.take d =@ pA t₀ ⋆ ((st.fl.drop d).drop L =@ (pA t₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 L)
    ⋆ (st.pb.take 2 =@ (rS t₀ - 0x36#64)
    ⋆ ((st.pb.drop 2).drop L =@ (rS t₀ - 0x36#64 + BitVec.ofNat 64 2 + BitVec.ofNat 64 L)
    ⋆ (RO x t₀ ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (rS t₀ - 0x448#64)
    ⋆ (Junk (rS t₀) ⋆ FR (Rest x.R ra t₀))))))))

theorem mc2_pre {k : Nat} {x : TArgs} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt} {m : Mem 64} (d L : Nat)
    (h : m =⋆ T k x ra t₀ FR st) (hfl : st.fl.length = 60) (hpb : st.pb.length = 14)
    (hd : d + L ≤ 60) (hL : 2 + L ≤ 14) :
    m =⋆ 8 ?@ (rS t₀ - 0x450#64) ⋆ (Reserve k (rS t₀ - 0x450#64)
      ⋆ (((st.pb.drop 2).take L =@ (rS t₀ - 0x36#64 + BitVec.ofNat 64 2)
        ⋆ L ?@ (pA t₀ + BitVec.ofNat 64 d)) ⋆ Mc2G x ra t₀ FR st d L)) := by
  simp only [T] at h
  rw [cell_split st.fl _ d (by omega) (by omega),
    cell_split (st.fl.drop d) _ L (by simp only [List.length_drop]; omega)
      (by simp only [List.length_drop]; omega),
    cell_split st.pb _ 2 (by omega) (by omega),
    cell_split (st.pb.drop 2) _ L (by simp only [List.length_drop]; omega)
      (by simp only [List.length_drop]; omega)] at h
  rw [perm3] at h
  have h2 := Block.sep_intro (len := L)
    (by simp only [List.length_take, List.length_drop]; omega) (by omega) h
  have h3 : m =⋆ 8 ?@ (rS t₀ - 0x450#64) ⋆ (Reserve k (rS t₀ - 0x450#64)
      ⋆ (((st.pb.drop 2).take L =@ (rS t₀ - 0x36#64 + BitVec.ofNat 64 2)
        ⋆ L ?@ (pA t₀ + BitVec.ofNat 64 d)) ⋆ (st.fl.take d =@ pA t₀
        ⋆ ((st.fl.drop d).drop L =@ (pA t₀ + BitVec.ofNat 64 d + BitVec.ofNat 64 L)
        ⋆ (st.pb.take 2 =@ (rS t₀ - 0x36#64)
        ⋆ ((st.pb.drop 2).drop L =@ (rS t₀ - 0x36#64 + BitVec.ofNat 64 2 + BitVec.ofNat 64 L)
        ⋆ (RO x t₀ ⋆ (c4 (sA t₀ + 0x4c1ec#64) st.nl ⋆ (st.stk =@ (rS t₀ - 0x448#64)
        ⋆ (Junk (rS t₀) ⋆ FR (Rest x.R ra t₀))))))))))) := by
    rw [perm6]; exact h2
  exact h3

theorem mc2_post {k : Nat} {x : TArgs} {ra : Int64} {t₀ : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt} {m : Mem 64} (d L : Nat)
    (hfl : st.fl.length = 60) (hpb : st.pb.length = 14) (hd : d + L ≤ 60) (hL : 2 + L ≤ 14)
    (h : m =⋆ 8 ?@ (rS t₀ - 0x450#64) ⋆ (Reserve k (rS t₀ - 0x450#64)
      ⋆ (((st.pb.drop 2).take L =@ (rS t₀ - 0x36#64 + BitVec.ofNat 64 2)
        ⋆ (st.pb.drop 2).take L =@ (pA t₀ + BitVec.ofNat 64 d)) ⋆ Mc2G x ra t₀ FR st d L))) :
    m =⋆ T k x ra t₀ FR ⟨st.fl.take d ++ ((st.pb.drop 2).take L ++ (st.fl.drop d).drop L),
      st.nl, st.stk, st.pb⟩ := by
  simp only [Mc2G] at h
  rw [perm5] at h
  have e1 : (st.fl.take d).length = d := by simp only [List.length_take]; omega
  have e2 : ((st.pb.drop 2).take L).length = L := by
    simp only [List.length_take, List.length_drop]; omega
  simp only [T]
  rw [append_split _ _ _ (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    append_split _ _ _ (by simp only [List.length_append, List.length_take, List.length_drop]; omega),
    cell_split st.pb _ 2 (by omega) (by omega),
    cell_split (st.pb.drop 2) _ L (by simp only [List.length_drop]; omega)
      (by simp only [List.length_drop]; omega), e1, e2]
  exact h

omit [CodeEnv] in
/-- After the second copy the array is `limIn`. -/
theorem cp2_av (x : TArgs) (fl pb : List UInt8) (hfl : fl.length = 60) (hpb : pb.length = 14)
    (h2 : 2 ≤ x.a.npatch) (h6 : x.a.npatch ≤ 6) (hn : x.a.n0 + x.a.npatch ≤ 30) (hP : PBto x pb (x.a.npatch + 1))
    (hAV : ∀ q, AV fl q = if q ≤ x.a.n0 then u16 x.a.ftLow q else u16 x.a.ftLim q) (q : Nat) :
    AV (fl.take (2 * (x.a.n0 + 1)) ++ ((pb.drop 2).take (2 * (x.a.npatch - 1))
      ++ (fl.drop (2 * (x.a.n0 + 1))).drop (2 * (x.a.npatch - 1)))) q = A0 x q := by
  simp only [AV, A0, limIn]
  rw [u16_app _ _ (x.a.n0 + 1) _ (by simp only [List.length_take]; omega)]
  by_cases hq : q < x.a.n0 + 1
  · rw [if_pos hq, u16_take' _ _ (x.a.n0 + 1) _ rfl hq, if_pos (by omega)]
    have := hAV q
    simp only [AV, show q ≤ x.a.n0 by omega, ↓reduceIte] at this
    exact this
  rw [if_neg hq, u16_app _ _ (x.a.npatch - 1) _
    (by simp only [List.length_take, List.length_drop]; omega)]
  by_cases hq2 : q - (x.a.n0 + 1) < x.a.npatch - 1
  · simp only [hq2, ↓reduceIte, show ¬ q ≤ x.a.n0 by omega, show q < x.a.n0 + x.a.npatch by omega]
    rw [u16_take' _ _ _ _ rfl hq2, u16_drop' _ 2 1 _ rfl, hP _ (by omega)]
    congr 2; omega
  · simp only [hq2, ↓reduceIte, show ¬ q ≤ x.a.n0 by omega,
      show ¬ q < x.a.n0 + x.a.npatch by omega]
    rw [u16_drop' _ _ _ _ rfl, u16_drop' _ _ _ _ rfl]
    have := hAV (q - (x.a.n0 + 1) - (x.a.npatch - 1) + (x.a.npatch - 1) + (x.a.n0 + 1))
    simp only [AV, show ¬ (q - (x.a.n0 + 1) - (x.a.npatch - 1) + (x.a.npatch - 1) + (x.a.n0 + 1)
      ≤ x.a.n0) by omega, ↓reduceIte] at this
    rw [this]
    congr 1; omega

theorem blk_L400a (k : Nat) (_hk : k ≤ 2 ^ 32) (hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L400a" := by
  cfg_block
  measure_hb "L400a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, hlb0, h14, h15, fl, stk, pb, hL, hP, hAV, hm⟩, hdx, hnp2⟩,
      hn⟩ := hs₀
    rw [var_L400a] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hL' := hL
    obtain ⟨hL1, hL2, hL3⟩ := hL'
    replace hL1 : fl.length = 60 := hL1
    replace hL3 : pb.length = 14 := hL3
    have hpre := mc2_pre (st := ⟨fl, x.a.nlim, stk, pb⟩) (2 * (x.a.n0 + 1)) (2 * (x.a.npatch - 1))
      hm hL1 hL3 (by omega) (by omega)
    have hld8 : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, sub448_8]
      exact Block.loadInt_isSome hpre (by simp)
    have hpush : Hide _ := fun w => Block.storeInt_val hpre (Split.here _ _) w
    have e8 : s₀.regs.get64 .rsp - Width.W64.bytesv = rS t₀ - 0x450#64 := by
      rw [hsp]; exact sub448_8 _
    have esrc : s₀.regs.get64 .rbp + 18446744073709551572#64 = rS t₀ - 0x36#64 + BitVec.ofNat 64 2 := by
      rw [hbp]; exact rbp_pb2 _
    have edst := rdi_dst (pA t₀) x.a.n0 (by omega)
    have elen := rdx3 x.a.npatch (by omega) (by omega)
    clear hm hpre
    vcgen [MachineWP.call_proc_spec_at (⟨Mc2G x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩
      (2 * (x.a.n0 + 1)) (2 * (x.a.npatch - 1)), (pb.drop 2).take (2 * (x.a.npatch - 1))⟩ : McA)
      "memcpy" hMc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, Int64.toBitVec_neg_ofNat_norm,
      Nat.reduceMod, Nat.reducePow, Nat.reduceSub, BitVec.ofNat_eq_ofNat, AddrIndex.offset64_none,
      AddrIndex.offset64_scale2, BitVec.add_zero, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hld8,
      Option.isSome_some, true_and, and_true, h14, h15, hdx] at *
    intro ra'
    refine ⟨⟨?_, ?_⟩, fun s' hpost => ?_⟩
    · rw [e8, elen, esrc, edst]
      unfold Hide at hpush
      exact hpush _
    · rw [elen, List.length_take, List.length_drop, hL3]; omega
    · obtain ⟨hsp', hbp', ⟨hbx', -, h13', h14', h15'⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      rw [tab_L4020, var_L4020]
      rw [e8, esrc, edst] at hm'
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hlb0, h14', h15', _, stk, pb, ⟨?_, hL2, hL3⟩, hP,
        cp2_av x fl pb hL1 hL3 hnp2 hnp6 (by omega) hP hAV,
        mc2_post (st := ⟨fl, x.a.nlim, stk, pb⟩) _ _ hL1 hL3 (by omega) (by omega) hm'⟩, by decide⟩
      · rw [hsp', e8]; exact add450_8 _
      · rw [hbp', hbp]
      · rw [h13', h13]
      · rw [hbx', hbx]
      · simp only [List.length_append, List.length_take, List.length_drop, hL1, hL3]
        all_goals omega

end Kraken.Examples.Sbr.Tlim
