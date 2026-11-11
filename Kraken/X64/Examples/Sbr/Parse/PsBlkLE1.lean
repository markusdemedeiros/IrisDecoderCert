import Kraken.X64.Examples.Sbr.Parse.PsBlkL6
import Kraken.X64.Examples.Sbr.Parse.PsBlkLPLib

/-! # `ff_ps_read_data`, shard L: the second `icc` band loop (`0xbe0`–`0xc5f`) -/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- The 9-bit window at the reader's index. -/
theorem blk_Lbe0 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lbe0" := by
  cfg_block
  simp only [tab_Lbe0, var_Lbe0, tab_Lbf8, var_Lbf8]
  measure_hb "Lbe0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hpos, h11, hb, hTb, hj⟩, hW⟩,
      hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have h13 := hLB.2.1.1
    have hI := hLB.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (by
        simp only [BitVec.toNat_setWidth, toNat_ushiftRight_div]; omega)
    case vc2 =>
      refine ⟨⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx,
          by rs; exact hsi⟩, hpos, by rs; exact h11, hb, by rs; exact hTb, hj⟩, hW, ?_⟩, ?_⟩
      · simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans (shr23_lt _) (by decide))]
        exact shr23_lt _
      · first | var_step | (simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
                            exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
                              (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
                                (Kraken.lex_cons_le_of_lt (by rfl) (by decide))))))

omit [CodeEnv] in
/-- A depth-2 (`icc`) table: every 9-bit index starts a 2-level walk. -/
theorem le_vlc2 {v : Nat → VlcTab} (hv : VlcC v) {j : Nat} (hj : j = 4 ∨ j = 5) {i : Nat}
    (hi : i < 512) :
    4 * i + 4 ≤ (v j).es.length ∧ (v j).es.length < 2 ^ 32 ∧ VWalk (v j).es 2 i := by
  have h := hv j (by omega)
  have hb : vbits j = 9 := by rcases hj with rfl | rfl <;> rfl
  have hd : vdepth j = 2 := by rcases hj with rfl | rfl <;> rfl
  rw [hb, hd] at h
  obtain ⟨h4, hN, hw⟩ := h
  have hW := hw i (by omega)
  have hlt : i < (v j).es.length / 4 := by simp only [VWalk] at hW; exact hW.1
  simp only [VlcTab.N] at hN
  exact ⟨by omega, by omega, hW⟩

set_option maxRecDepth 20000 in
/-- Level 1 of the walk: the entry at the window. -/
theorem blk_Lbf8 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lbf8" := by
  cfg_block
  simp only [tab_Lbf8, var_Lbf8, tab_Lc09, var_Lc09, tab_Lc3a, var_Lc3a]
  measure_hb "Lbf8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hpos, h11, hb, hTb, hj⟩, hW,
      hax⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have hv := le_vlc2 hC.2.1 hj hax
    have l2 := Fr_vtab_load hm j (by omega) hv.2.1 (4 * (s₀.regs.get64 .rax).toNat + 2) 2 (by omega)
    have l0 := Fr_vtab_load hm j (by omega) hv.2.1 (4 * (s₀.regs.get64 .rax).toNat) 2 (by omega)
    have h30 : (s₀.regs.get64 .rax).toNat < 2 ^ 30 := by omega
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    vcgen
    case vc1 =>
      rename_i s hs; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0]; rfl
    case vc2 =>
      rename_i s hs _ _; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, hTb,
        tab_addr2' _ _ h30, l2]; rfl
    case vc3 =>
      rename_i s hs v0 hv0 v1 hv1 _ hc; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, add_i64z, hTb,
        tab_addr2' _ _ h30, l2, Option.some.injEq] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [ns_sx16, Bool.not_eq_true'] at hc
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lc3a") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lc3a _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx,
          by rs; exact hsi⟩, hpos, by rs; exact h11, hb, by rs; exact hTb, hj⟩, hW, ⟨_, hc, by rs; exact BitVec.setWidth_32_64_32 _⟩⟩
      · rw [var_Lc3a]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
            (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))))
    case vc4 =>
      rename_i s hs v0 hv0 v1 hv1 _ hc; subst hs
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', i2, add_i64z, hTb,
        tab_addr2' _ _ h30, l2, Option.some.injEq] at hv1 hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, offs4', add_i64z, hTb,
        tab_addr0' _ _ h30, l0, Option.some.injEq] at hv0
      subst hv0 hv1
      rw [ns_sx16, Bool.not_eq_false'] at hc
      refine ⟨⟨c, f, e, b, j, _, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx,
          by rs; exact hsi⟩, hpos, by rs; exact h11, hb, by rs; exact hTb, hj⟩, hW,
          hv.2.2, hc, by rs; exact BitVec.setWidth_32_64_32 _, by rs; exact BitVec.setWidth_32_64_32 _⟩, ?_⟩
      simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
      exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
        (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

set_option maxRecDepth 20000 in
/-- Level 2 of the walk: the next window. -/
theorem blk_Lc09 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc09" := by
  cfg_block
  simp only [tab_Lc09, var_Lc09, tab_Lc29, var_Lc29]
  measure_hb "Lc09"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, i, ⟨⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hpos, h11, hb, hTb, hj⟩, hW,
      hWk⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    have h13 := hLB.2.1.1
    have hI := hLB.2.2.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hpL : x.p8.toNat / 8 + 4 ≤ x.L := hC.2.2.2.2.1
    have hr32 : (s₀.regs.get64 .r8).toNat < 2 ^ 32 := by omega
    have hR12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hLB.2.1.2
    have hcw := fun af of => lix_clampW x (s₀.regs.get64 .r8) 9#64 (by decide) hI hp31 hC.2.2.1 af of
    vcgen [ps_bswap32_havoc, ps_shl_cl32_havoc]
    all_goals try call_simp
    all_goals try subst_vars
    all_goals try dsimp only at *
    all_goals pnorm at *
    all_goals try simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      ite_self, AddrIndex.offset64, Width.bytes, BitVec.mul_one, BitVec.setWidth_32_64_32] at *
    all_goals try simp only [h13, hR12, BitVec.setWidth_32_64_32]
    case vc1 =>
      exact Fr_buf_load hm _ 4 (buf_ix hpL (hcw _ _).1)
    case vc2 =>
      refine ⟨⟨c, f, e, b, j, i, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          ?ix hm, h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx,
          by rs; exact hsi⟩, hpos, by rs; exact h11, hb, by rs; exact hTb, hj⟩, hW, ?wk⟩, ?lex⟩
      case wk =>
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact hWk
      case ix =>
        rs
        exact (hcw _ _).1
      case lex =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

set_option maxRecDepth 20000 in
/-- Level 2 of the walk: the last entry. -/
theorem blk_Lc29 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc29" := by
  cfg_block
  simp only [tab_Lc29, var_Lc29, tab_Lc3a, var_Lc3a, qc29]
  measure_hb "Lc29"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, i, ⟨⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hpos, h11, hb, hTb, hj⟩, hW,
      hV, hmsb, hrl, hrs⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hC := hLB.1.1
    obtain ⟨h4, hN, -⟩ := hC.2.1 j (by omega)
    simp only [VlcTab.N] at hN
    have hm32 : (vlen (x.v j).es i).toNat % 32 < 32 := Nat.mod_lt _ (by decide)
    have hI := vwalk_next hV hmsb ((BitVec.setWidth 32 (s₀.regs.get64 .rdi)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)) (shr_lt _ _ hm32)
    rw [BitVec.add_comm] at hI
    have hIN := vwalk_lt hI
    have h30 : ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rdi)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat < 2 ^ 30 := by omega
    have l0 := Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rdi)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat) 2 (by omega)
    have l2 := Fr_vtab_load hm j (by omega) (by omega) (4 * ((vsym (x.v j).es i).signExtend 32 + (BitVec.setWidth 32 (s₀.regs.get64 .rdi)).ushiftRight
      ((vlen (x.v j).es i).toNat % 32)).toNat + 2) 2 (by omega)
    have i2 : Int64.toBitVec 2 = 2#64 := rfl
    vcgen
    all_goals subst_vars
    all_goals try dsimp only at *
    case vc1 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI0 _ _ h30, l0]; rfl
    case vc2 =>
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', i2, hTb, BitVec.setWidth_32_64_32]
      rw [tab_addrI2 _ _ h30, l2]; rfl
    case vc3 =>
      rename_i v0 hv0 v1 hv1
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        ite_self, sw_shr_ite, cnt_sx hrl, hrs, offs4', add_i64z, i2, hTb, BitVec.setWidth_32_64_32] at hv0 hv1
      rw [tab_addrI0 _ _ h30, l0, Option.some.injEq] at hv0
      rw [tab_addrI2 _ _ h30, l2, Option.some.injEq] at hv1
      subst hv0 hv1
      simp only [get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, ite_self]
      refine ⟨⟨c, f, e, b, j, ⟨⟨LB_mv hLB (by rsw) (by rsw) (by rsw; exact hLB.2.1)
          (by rsw; exact hLB.2.2.1) hm, h1c, h48, h50, he, by rsw; exact h9, by rsw; exact hbx,
          by rsw; exact hsi⟩, hpos, by rsw; exact h11, hb, by rsw; exact hTb, hj⟩, hW,
          ⟨_, vwalk1_msb hI, ?_⟩⟩, ?_⟩
      · (try rsw) <;> (try simp only [BitVec.setWidth_32_64_32])
      · simp only [slot64, get64_ite, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, ite_self]
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

/-- A store into `icc_par` keeps `LB`. -/
theorem le_LB_wrc {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {o n : Nat} (v : Int) (h : LB k Ext x ra t₀ s c f)
    (ho : 48 ≤ o) (hn : o + n ≤ 764)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (hR : Rdr x s') (hI : Ix x (s'.regs.get64 .r8))
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 o) n v) :
    LB k Ext x ra t₀ s' (wr c o n v) f := by
  obtain ⟨⟨hC, ⟨hsp0, hbp0, hfl, hP, hb⟩, hM⟩, _, _, ⟨⟨h0, h4, h58, h38⟩, h34, h68, h40⟩⟩ := h
  have hl : c.length = 764 := hP.1
  have e32 : ∀ o', o' + 4 ≤ 48 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' h' => i32_wr c o n o' v (by omega) (by omega)
  refine ⟨⟨hC, ⟨by rw [hsp, hsp0], by rw [hbp, hbp0], hfl, PsInv_wrz v hP (by omega) (by omega),
    hb⟩, by rw [hm]; exact Fr_c_store hM hl o n (by omega) v⟩, hR, hI, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h68, ?_⟩⟩
  all_goals simp only [ne, e32 44 (by omega), e32 40 (by omega), e32 4 (by omega)]
  all_goals assumption

omit [CodeEnv] in
/-- The `icc` byte `o` stored: `WC` becomes `WCx` at `o`. -/
theorem le_WCx_wr {c f : List UInt8} {e b : Nat} (v : Int) (hl : c.length = 764) (h : WC c f)
    (he : e < 5) (hb : b < 34) : WCx (wr c (246 + 34 * e + b) 1 v) f (246 + 34 * e + b) := by
  have hZ := lp_WZ_wr (o := 246 + 34 * e + b) (n := 1) v hl (lp_WZ_of_WC h) (by omega) (by omega)
  obtain ⟨h0, hP, hH, hS, hB, hZz⟩ := hZ
  refine ⟨h0, ?_, hP, hH, hS, hB, hZz⟩
  intro e' he' b' hb' hne
  rw [i8_wr c _ 1 _ v (by omega) (by omega)]
  exact h.1.2.2.1 e' he' b' hb'

omit [CodeEnv] in
/-- `WCx` at `o` with the byte at `o` in range is `WC`. -/
theorem le_WC_of_WCx {c f : List UInt8} {o : Nat} (h : WCx c f o) (h0 : 0 ≤ i8 c o)
    (h7 : i8 c o ≤ 7) : WC c f := by
  obtain ⟨⟨r1, r2⟩, hX, hP, hH, hS, hB, hZ⟩ := h
  refine ⟨⟨r1, r2, ?_, hP⟩, hH, hS, hB, hZ⟩
  intro e he b hb
  by_cases hq : 246 + 34 * e + b = o
  · rw [hq]; exact ⟨h0, h7⟩
  · exact hX e he b hb hq

omit [CodeEnv] in
theorem le_i32 {c : List UInt8} {o : Nat} (v : Int) (hl : c.length = 764) (ho : 48 ≤ o)
    (hn : o + 1 ≤ 764) (o' : Nat) (h' : o' + 4 ≤ 48) : i32 (wr c o 1 v) o' = i32 c o' :=
  i32_wr c o 1 o' v (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- The end of the walk: `r8 += len` (clamped), `icc_par[e][b] = r15b` stored. -/
theorem blk_Lc3a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc3a" := by
  cfg_block
  simp only [tab_Lc3a, var_Lc3a, tab_Lc5f, var_Lc5f]
  measure_hb "Lc3a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, hpos, h11, hb, hTb, hj⟩, hW,
      hlen⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hcl := LB_cl hLB
    have hP := hLB.1.2.1.2.2.2.1
    have h28' : i32 c 28 ≤ 34 := hP.2.2.2.1
    have hne4 : ne c ≤ 4 := hLB.2.2.2.1.2.1
    have hb' : (b : Int) < i32 c 28 := hb
    have he' : (e : Int) < ne c := he
    have hb34 : b < 34 := by omega
    have he5 : e < 5 := by omega
    have hC := hLB.1.1
    have hp31 : x.p8.toNat < 2 ^ 31 := hC.2.2.2.1
    have hR12 : s₀.regs.get64 .r12 = x.p8.setWidth 64 := hLB.2.1.2
    have hfl := LB_fl hLB
    have hbp := hLB.1.2.1.2.1
    have e32 := fun v => le_i32 (o := 246 + 34 * e + b) v hcl (by omega) (by omega)
    have e3 : s₀.regs.get64 .rbp - BitVec.ofNat 64 0x58
        = rsp0 t₀ - 0xa8#64 + BitVec.ofNat 64 0x48 := slot_addr_sub hbp 0x58 0x48 rfl
    have l3 := Fr_f_load hm hfl 0x48 8 (by omega)
    rw [← e3] at l3
    have l3' := fun v => Fr_f_load (Fr_c_store hm hcl (246 + 34 * e + b) 1 (by omega) v) hfl 0x48 8 (by omega)
    simp only [← e3] at l3'
    vcgen
    case vc1 =>
      rename_i hz
      subst_vars
      dsimp only at hz
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h11] at hz
      rw [z_sub34 b hb34] at hz
      exact absurd hz Bool.false_ne_true
    case vc3 =>
      rename_i hz hc
      subst_vars
      dsimp only at hc
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h9] at hc
      rw [nc_sub5 e he5] at hc
      exact absurd hc Bool.false_ne_true
    case vc2 =>
      rename_i hz
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale1,
        add_i64z, hbx, h11, addr3]
      rw [Fr_c_load hm hcl _ 1 (by omega)]; rfl
    case vc4 =>
      rename_i hz hc
      subst_vars
      dsimp only
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, AddrIndex.offset64_scale1,
        add_i64z, hbx, h11, addr3, hR12, BitVec.setWidth_32_64_32]
      refine ⟨⟨_, f, e, b, j, ⟨⟨le_LB_wrc _ (o := 246 + 34 * e + b) (n := 1) hLB (by omega)
        (by omega) (by rs) (by rs) (by rs; exact hLB.2.1) ?ix rfl, ?h1c, ?h48, h50, ?he,
        by rs; exact h9, by rs; exact hbx, ?hsi⟩, ?h28, by rs; exact h11, ?hb, by rs; exact hTb, hj⟩,
        fun hw => le_WCx_wr _ hcl (hW hw) he5 hb34, i8_wr1 _ _ _ (by omega)⟩, ?lex⟩
      case ix =>
        rs
        exact (lix_clampW x _ _ (lenP_lt _ hlen) hLB.2.2.1 hp31 hC.2.2.1 _ _).1
      case h1c => rw [show i32 (wr c (246 + 34 * e + b) 1 _) 20 = i32 c 20 from e32 _ 20 (by omega)]; exact h1c
      case h48 => rw [show ne (wr c (246 + 34 * e + b) 1 _) = ne c from e32 _ 44 (by omega)]; exact h48
      case he => rw [show ne (wr c (246 + 34 * e + b) 1 _) = ne c from e32 _ 44 (by omega)]; exact he
      case hsi => rs; rw [show i32 (wr c (246 + 34 * e + b) 1 _) 28 = i32 c 28 from e32 _ 28 (by omega)]; exact hsi
      case h28 => rw [show i32 (wr c (246 + 34 * e + b) 1 _) 28 = i32 c 28 from e32 _ 28 (by omega)]; exact hpos
      case hb => rw [show i32 (wr c (246 + 34 * e + b) 1 _) 28 = i32 c 28 from e32 _ 28 (by omega)]; exact hb
      case lex =>
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, l3, l3']
        exact Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
          (Kraken.lex_cons_le_cons (by rfl) (Kraken.lex_cons_le_cons (by rfl)
            (Kraken.lex_cons_le_of_lt (by rfl) (by decide)))))

omit [CodeEnv] in
theorem le_nc8 (y : BitVec 8) (af of : Bool)
    (h : CondCode.nc.interp (StatusFlags.from_result (y - BitVec.setWidth 8 (Int64.toBitVec 8))
      { cf := (y - BitVec.setWidth 8 (Int64.toBitVec 8)).unsigned !=
          y.unsigned - (BitVec.setWidth 8 (Int64.toBitVec 8)).unsigned, af := af, of := of }) = false) :
    0 ≤ y.toInt ∧ y.toInt ≤ 7 := by
  revert h; revert y af of; decide +kernel

omit [CodeEnv] in
theorem le_rsi (q : Int) (h0 : 0 < q) (h1 : q ≤ 34) :
    (BitVec.ofInt 32 q).setWidth 64 = BitVec.ofNat 64 q.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 20000 in
/-- The range check `icc_par[e][b] < 8`, the band count, the back edge. -/
theorem blk_Lc5f (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc5f" := by
  cfg_block
  simp only [tab_Lc5f, var_Lc5f, tab_Lbe0, var_Lbe0]
  measure_hb "Lc5f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, e, b, j, ⟨⟨hLB, h1c, h48, h50, he, h9, hbx, hsi⟩, h28, h11, hb, hTb, hj⟩,
      hW, hi8⟩, hn⟩ := hs₀
    subst hn
    have hP := hLB.1.2.1.2.2.2.1
    have h28' : i32 c 28 ≤ 34 := hP.2.2.2.1
    have hb' : (b : Int) < i32 c 28 := hb
    have h28'' : 0 < i32 c 28 := h28
    have hbn : b < (i32 c 28).toNat := by omega
    have hn63 : (i32 c 28).toNat < 2 ^ 63 := by omega
    have hsi' : s₀.regs.get64 .rsi = BitVec.ofNat 64 (i32 c 28).toNat := by
      rw [hsi]; exact le_rsi _ h28'' h28'
    have hm := hLB.1.2.2
    vcgen
    all_goals subst_vars
    case vc1 =>
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.L10cf") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_L10cf _ _ _ _ _ _).mpr ?_
        obtain ⟨hC, -, -, hS⟩ := hLB
        obtain ⟨hP0, ⟨hsp, hbp, hB⟩, hM⟩ := hC
        exact ⟨c, f, ⟨hP0, ⟨hsp, hbp, hB⟩, hM⟩, hS.2.2.1, fun hw => (hW hw).1⟩
      · rw [var_L10cf]
        exact Kraken.lex_cons_lt_of_lt rfl (by decide)
    case vc2 =>
      rename_i hc hz
      dsimp only at hc hz
      have hr := le_nc8 _ _ _ hc
      rw [← hi8] at hr
      simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, CondCode.interp_nz,
        StatusFlags.zf_from_result, h11, hsi'] at hz
      rw [cnt_beq2 _ _ hbn hn63] at hz
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hz
      have hz' : b + 1 ≠ (i32 c 28).toNat := hz
      have h3 : b + 1 < (i32 c 28).toNat := Nat.lt_of_le_of_ne hbn hz'
      have hb2 : ((b + 1 : Nat) : Int) < i32 c 28 := by
        have := Int.toNat_of_nonneg (Int.le_of_lt h28''); omega
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.Lbe0") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_Lbe0 _ _ _ _ _ _).mpr ?_
        refine ⟨c, f, e, b + 1, j, ⟨⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx,
          by rs; exact hsi⟩, h28, ?_, hb2, by rs; exact hTb, hj⟩, fun hw => le_WC_of_WCx (hW hw) hr.1 hr.2⟩
        simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h11]
        exact ofNat64_add b 1
      · rw [var_Lbe0]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true, h11, hsi']
        refine Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_of_lt (by rfl) ?_)))
        rw [Nat.mod_eq_of_lt (BitVec.isLt _), Nat.mod_eq_of_lt (BitVec.isLt _)]
        exact meas_b _ _ hbn hn63
    case vc3 =>
      rename_i hc hz
      dsimp only at hc hz
      have hr := le_nc8 _ _ _ hc
      rw [← hi8] at hr
      left
      refine Table.ofLabels_at (l := "ff_ps_read_data.La90") ⟨rfl, ?_, Or.inl ?_⟩
      · refine (tab_La90 _ _ _ _ _ _).mpr ?_
        exact ⟨c, f, e, ⟨LB_mv hLB (by rs) (by rs) (by rs; exact hLB.2.1)
          (by rs; exact hLB.2.2.1) hm, h1c, h48, h50, he, by rs; exact h9, by rs; exact hbx,
          by rs; exact hsi⟩, fun hw => le_WC_of_WCx (hW hw) hr.1 hr.2⟩
      · rw [var_La90]
        simp only [slot64, Reg64s.get64_set64, reduceCtorEq, ite_false, ite_true]
        exact Kraken.lex_cons_lt_cons (by rfl) (Kraken.lex_cons_lt_cons (by rfl)
          (Kraken.lex_cons_lt_of_lt (by rfl) (by decide)))

end Kraken.Examples.Sbr.Ps
