import Kraken.X64.Examples.Sbr.Parse.PsBlkLLib
import Kraken.Rules.PackedSse

/-!
# `ff_ps_read_data`, shard L: the `iid_par` clearing (`enable_iid = 0`)

`vmovdqu %ymm, m256` (a copy of `PsBlkT1Lib`'s rule, which this chain does not import), the
zero stores into `iid_par` (`*ps` bytes `[76, 246)`), and the blocks `0xa1e`, `0xa32`, `0xa42`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP Lean.Order
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

section Specs

variable [CodeEnv] {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}
  {p : Program}

local macro "l5_wp_step" : tactic =>
  `(tactic| simp only [Executable.stepAt, Directive.interp, Instr.interp,
      Operation.interp, AvxOperation.interp, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpLow, RelRegOrMem.interp, ConstExpr.interp,
      MachineData.set, MachineData.setReg, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
      MachineData.setAvx, MachineData.setAvxReg,
      Reg64s.get_low64, Reg64s.set_low64, Effects.All, or_false, false_or])

local macro "l5_mem_access" hal:ident hv:ident : tactic =>
  `(tactic| simp only [MachineData.loadAvx, MachineData.storeAvx, MachineData.load,
      MachineData.store, AddrExpr.zeroExtend_interp_base_idx_disp,
      AddrExpr.zeroExtend_interp_rip_label, AddrExpr.zeroExtend_interp_rip_label_add,
      $hal:ident, $hv:ident, AvxWidth.bytes, Width.bytes,
      Bool.not_true, Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false,
      Effects.All])

/-- `vmovdqu %ymm, m256`: 32 owned bytes, at any alignment. -/
@[spec low] theorem MachineWP.l5_vmovdqu256_store_mem_spec (y : AvxReg .W256) (b : Reg64)
    (idx : Option AddrIndex) (d : Int64) :
    ⦃ fun s =>
        let a := s.regs.get64 b + AddrIndex.offset64 idx s.regs + d.toBitVec
        ((Mem.loadInt s.dmem a 32).isSome = true)
          ⊓ WP.wp p Q E { s with dmem := Mem.storeInt s.dmem a 32 (s.zmms.get y).toInt } ⦄
      (Directive.instr (.avx .W64 .W256 (.vmovdqu (.mem ⟨some (.reg b), idx, .int64 d⟩) (.avx y))) :: p)
    ⦃ Q; E ⦄ := by
  refine Triple.intro fun s h => ?_
  simp only [meet_prop_eq_and] at h
  obtain ⟨hsome, hk⟩ := h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  intro pc hpl
  obtain ⟨z, rest, hseg, hpl'⟩ := hpl
  rw [after_instr hseg]
  refine step_here hseg (Or.inl ?_)
  l5_wp_step
  l5_mem_access hv hv
  exact hk _ hpl'

end Specs

namespace Kraken.Examples.Sbr.Ps

/-! ## Zero stores into `iid_par` -/

theorem l5_toBytes_zero_getD : ∀ n j : Nat, (Int.toBytes n 0).getD j 0 = 0
  | 0, j => by simp [Int.toBytes]
  | n + 1, 0 => by simp [Int.toBytes, Int.take]
  | n + 1, j + 1 => by
    simp only [Int.toBytes, Int.zero_ediv, List.getD_cons_succ]
    exact l5_toBytes_zero_getD n j

theorem l5_getD_wr (c : List UInt8) (o n j : Nat) (v : Int) (h : o + n ≤ c.length) :
    (wr c o n v).getD j 0
      = if o ≤ j ∧ j < o + n then (Int.toBytes n v).getD (j - o) 0 else c.getD j 0 := by
  simp only [wr, List.append_assoc, List.getD_eq_getElem?_getD]
  have h1 : (c.take o).length = o := by simp only [List.length_take]; omega
  have h2 : (Int.toBytes n v).length = n := Int.toBytes_length n v
  split
  · rename_i hj
    rw [List.getElem?_append_right (by omega), List.getElem?_append_left (by omega), h1]
  · rename_i hj
    by_cases hlt : j < o
    · rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hlt]
    · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
        List.getElem?_drop, h1, h2]
      congr 2
      omega

/-- `vpxor %xmm0, %xmm0, %xmm0` clears the whole `ymm0`. -/
theorem l5_vpxor_ymm (s : RegZmms) (x : RegMm) (a : BitVec 128) :
    (s.set (.xmm x) (a ^^^ a)).get (.ymm x) = 0#256 := by
  simp only [RegZmms.get, RegZmms.set, AvxReg.base, BitVec.xor_self]
  rw [RegZmms.get512_set512_same]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.take, AvxWidth.bits]

theorem l5_set0_ymm (s : RegZmms) (x : RegMm) :
    (s.set (.xmm x) 0#128).get (.ymm x) = 0#256 := by
  have := l5_vpxor_ymm s x 0
  rwa [BitVec.xor_self] at this

/-- A zero store `[o, o + n)` reaching the cleared range `[lo, hi)` extends it down to `o`. -/
theorem Zr_wr0 {c : List UInt8} {lo hi o n : Nat} (h : Zr c lo hi) (hlo : o ≤ lo)
    (hhi : lo ≤ o + n) (hn : o + n ≤ c.length) : Zr (wr c o n 0) o hi := by
  intro j h1 h2
  rw [l5_getD_wr c o n j 0 hn]
  split
  · exact l5_toBytes_zero_getD n (j - o)
  · exact h j (by omega) h2

theorem Zr_nil (c : List UInt8) (a : Nat) : Zr c a a := fun _ h1 h2 => absurd h2 (by omega)

theorem PsInv_wrz {c : List UInt8} {o n : Nat} (v : Int) (h : PsInv c) (ho : 48 ≤ o)
    (hn : o + n ≤ 764) : PsInv (wr c o n v) := by
  obtain ⟨hl, h1, h2, h3, h4, h5, h6⟩ := h
  have hL : o + n ≤ c.length := by omega
  refine ⟨by rw [wr_length _ _ _ _ hL, hl], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := omega) only [i32_wr] <;> assumption

/-- A store into `iid_par` keeps the header clauses of `PsWFb`. -/
theorem ZW_wr {c : List UInt8} {o n : Nat} {hd : Int} (v : Int) (hl : c.length = 764)
    (ho : 76 ≤ o) (hn : o + n ≤ 246) (h : Rng c ∧ Hdr c ∧ IidS c hd) :
    Rng (wr c o n v) ∧ Hdr (wr c o n v) ∧ IidS (wr c o n v) hd := by
  have e32 : ∀ o', o' + 4 ≤ 76 ∨ 246 ≤ o' → i32 (wr c o n v) o' = i32 c o' :=
    fun o' h' => i32_wr c o n o' v (by omega) (by omega)
  have e8 : ∀ j, 246 ≤ j → i8 (wr c o n v) j = i8 c j :=
    fun j h' => i8_wr c o n j v (by omega) (by omega)
  obtain ⟨⟨r756, r8, ricc, rpar⟩, ⟨d0, d4, db0, dmono, d31⟩, hs⟩ := h
  simp only [IidS] at hs
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals try simp only [ne, bord, IidS, e32 756 (by omega), e32 8 (by omega),
    e32 44 (by omega), e32 52 (by omega), e32 0 (by omega), e32 4 (by omega), e32 12 (by omega)]
  all_goals try assumption
  · intro e he b hb'
    rw [e8 _ (by omega)]; exact ricc e he b hb'
  · intro e he b hb'
    rw [e8 _ (by omega), e8 _ (by omega)]; exact rpar e he b hb'
  · intro e he
    have : e < 4 := by simp only [ne] at d4; omega
    rw [e32 _ (by omega), e32 _ (by omega)]; exact dmono e he
  · intro e he
    have : e ≤ 4 := by simp only [ne] at d4; omega
    rw [e32 _ (by omega)]; exact d31 e he

/-- A cleared `iid_par` is in range. -/
theorem Zr_IidB {c : List UInt8} (h : Zr c 76 246) (h8 : i32 c 8 = 0 ∨ i32 c 8 = 1) (n : Int)
    (hn : n ≤ 5) : IidB c n := by
  intro e he b hb _
  have h0 := h (76 + 34 * e + b) (by omega) (by omega)
  simp only [i8, h0]
  rcases h8 with h8 | h8 <;> rw [h8] <;> decide

section
variable [CodeEnv]

/-- A store into `iid_par` keeps `LB`. -/
theorem LB_wrc {k : Nat} {Ext : Mem 64 → Prop} {x : PArgs} {ra : Int64} {t₀ s s' : MachineData}
    {c f : List UInt8} {o n : Nat} (v : Int) (h : LB k Ext x ra t₀ s c f)
    (ho : 76 ≤ o) (hn : o + n ≤ 246)
    (hsp : s'.regs.get64 .rsp = s.regs.get64 .rsp) (hbp : s'.regs.get64 .rbp = s.regs.get64 .rbp)
    (hR : Rdr x s') (hI : Ix x (s'.regs.get64 .r8))
    (hm : s'.dmem = s.dmem.storeInt (arg2 t₀ + BitVec.ofNat 64 o) n v) :
    LB k Ext x ra t₀ s' (wr c o n v) f := by
  obtain ⟨⟨hC, ⟨hsp0, hbp0, hfl, hP, hb⟩, hM⟩, _, _, ⟨⟨h0, h4, h58, h38⟩, h34, h68, h40⟩⟩ := h
  have hl : c.length = 764 := hP.1
  have e32 : ∀ o', o' + 4 ≤ 76 → i32 (wr c o n v) o' = i32 c o' :=
    fun o' h' => i32_wr c o n o' v (by omega) (by omega)
  refine ⟨⟨hC, ⟨by rw [hsp, hsp0], by rw [hbp, hbp0], hfl, PsInv_wrz v hP (by omega) (by omega),
    hb⟩, by rw [hm]; exact Fr_c_store hM hl o n (by omega) v⟩, hR, hI, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, h68, ?_⟩⟩
  all_goals simp only [ne, e32 44 (by omega), e32 40 (by omega), e32 4 (by omega)]
  all_goals assumption

end

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
theorem blk_a1e (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.La1e" := by
  cfg_block
  simp only [tab_La1e, var_La1e, tab_La32, var_La32]
  measure_hb "La1e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hLB, hbx, h10, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hcl := LB_cl hLB
    have ad : ∀ (d : Int64) (dn : Nat), d.toBitVec = BitVec.ofNat 64 dn →
        s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs + d.toBitVec
          = arg2 t₀ + BitVec.ofNat 64 dn := by
      intro d dn h; rw [hbx, AddrIndex.offset64_none, h]
      exact congrArg (· + BitVec.ofNat 64 dn) (BitVec.add_zero _)
    have hl1 : (wr c 214 32 0).length = 764 := by rw [wr_length _ _ _ _ (by omega)]; exact hcl
    have hl2 : (wr (wr c 214 32 0) 204 32 0).length = 764 := by
      rw [wr_length _ _ _ _ (by omega)]; exact hl1
    have hm1 := Fr_c_store hm hcl 214 32 (by omega) 0
    have hne : ne (wr (wr c 214 32 0) 204 32 0) = ne c := by
      simp only [ne]
      rw [i32_wr _ _ _ _ _ (by omega) (by omega), i32_wr _ _ _ _ _ (by omega) (by omega)]
    vcgen
    case vc1 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 214 214 rfl, Fr_c_load hm hcl 214 32 (by omega)]; rfl
    case vc2 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 214 214 rfl, ad 204 204 rfl, l5_vpxor_ymm, BitVec.toInt_zero,
        Fr_c_load hm1 hl1 204 32 (by omega)]; rfl
    case vc3 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 214 214 rfl, ad 204 204 rfl, l5_vpxor_ymm, BitVec.toInt_zero]
      refine ⟨⟨_, f, ⟨LB_wrc 0 (s := { s with dmem := storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 214) 32 0 })
        (LB_wrc 0 hLB (by omega) (by omega) rfl rfl hLB.2.1 hLB.2.2.1 rfl) (by omega) (by omega)
        rfl rfl hLB.2.1 hLB.2.2.1 rfl, hbx, by rw [show ne (wr (wr c 214 32 0) 204 32 0) = ne c from hne]; exact h10,
        fun hw => ZW_wr 0 hl1 (by omega) (by omega) (ZW_wr 0 hcl (by omega) (by omega) (hW hw))⟩,
        by simp only [BitVec.xor_self, l5_set0_ymm, BitVec.ofNat_eq_ofNat],
        Zr_wr0 (Zr_wr0 (Zr_nil c 246) (by omega) (by omega) (by omega)) (by omega) (by omega)
          (by omega)⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩


set_option maxRecDepth 20000 in
theorem blk_a32 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.La32" := by
  cfg_block
  simp only [tab_La32, var_La32, tab_La42, var_La42]
  measure_hb "La32"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hLB, hbx, h10, hW⟩, hy, hZ⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hcl := LB_cl hLB
    have ad : ∀ (d : Int64) (dn : Nat), d.toBitVec = BitVec.ofNat 64 dn →
        s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs + d.toBitVec
          = arg2 t₀ + BitVec.ofNat 64 dn := by
      intro d dn h; rw [hbx, AddrIndex.offset64_none, h]
      exact congrArg (· + BitVec.ofNat 64 dn) (BitVec.add_zero _)
    have hl1 : (wr c 172 32 0).length = 764 := by rw [wr_length _ _ _ _ (by omega)]; exact hcl
    have hm1 := Fr_c_store hm hcl 172 32 (by omega) 0
    have hne : ne (wr (wr c 172 32 0) 140 32 0) = ne c := by
      simp only [ne]
      rw [i32_wr _ _ _ _ _ (by omega) (by omega), i32_wr _ _ _ _ _ (by omega) (by omega)]
    have hy0 : (s₀.zmms.get (AvxReg.ymm RegMm.mm0)).toInt = 0 := by rw [hy]; rfl
    vcgen
    case vc1 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 172 172 rfl, Fr_c_load hm hcl 172 32 (by omega)]; rfl
    case vc2 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 172 172 rfl, ad 140 140 rfl, hy0, Fr_c_load hm1 hl1 140 32 (by omega)]; rfl
    case vc3 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 172 172 rfl, ad 140 140 rfl, hy0]
      refine ⟨⟨_, f, ⟨LB_wrc 0 (s := { s with dmem := storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 172) 32 0 })
        (LB_wrc 0 hLB (by omega) (by omega) rfl rfl hLB.2.1 hLB.2.2.1 rfl) (by omega) (by omega)
        rfl rfl hLB.2.1 hLB.2.2.1 rfl, hbx, by rw [show ne (wr (wr c 172 32 0) 140 32 0) = ne c from hne]; exact h10,
        fun hw => ZW_wr 0 hl1 (by omega) (by omega) (ZW_wr 0 hcl (by omega) (by omega) (hW hw))⟩,
        hy, Zr_wr0 (Zr_wr0 hZ (by omega) (by omega) (by omega)) (by omega) (by omega)
          (by omega)⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩

set_option maxRecDepth 20000 in
theorem blk_a42 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "ff_ps_read_data.La42" := by
  cfg_block
  simp only [tab_La42, var_La42, tab_La4c, var_La4c]
  measure_hb "La42"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, ⟨hLB, hbx, h10, hW⟩, hy, hZ⟩, hn⟩ := hs₀
    subst hn
    have hm := hLB.1.2.2
    have hcl := LB_cl hLB
    have ad : ∀ (d : Int64) (dn : Nat), d.toBitVec = BitVec.ofNat 64 dn →
        s₀.regs.get64 .rbx + AddrIndex.offset64 none s₀.regs + d.toBitVec
          = arg2 t₀ + BitVec.ofNat 64 dn := by
      intro d dn h; rw [hbx, AddrIndex.offset64_none, h]
      exact congrArg (· + BitVec.ofNat 64 dn) (BitVec.add_zero _)
    have hl1 : (wr c 108 32 0).length = 764 := by rw [wr_length _ _ _ _ (by omega)]; exact hcl
    have hm1 := Fr_c_store hm hcl 108 32 (by omega) 0
    have hne : ne (wr (wr c 108 32 0) 76 32 0) = ne c := by
      simp only [ne]
      rw [i32_wr _ _ _ _ _ (by omega) (by omega), i32_wr _ _ _ _ _ (by omega) (by omega)]
    have hy0 : (s₀.zmms.get (AvxReg.ymm RegMm.mm0)).toInt = 0 := by rw [hy]; rfl
    vcgen
    case vc1 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 108 108 rfl, Fr_c_load hm hcl 108 32 (by omega)]; rfl
    case vc2 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 108 108 rfl, ad 76 76 rfl, hy0, Fr_c_load hm1 hl1 76 32 (by omega)]; rfl
    case vc3 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 108 108 rfl, ad 76 76 rfl, hy0]
      have hL2 := LB_wrc 0 (o := 76) (n := 32) (s := { s with dmem := storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 108) 32 0 })
        (LB_wrc 0 (o := 108) (n := 32) hLB (by omega) (by omega) rfl rfl hLB.2.1 hLB.2.2.1 rfl) (by omega) (by omega)
        rfl rfl hLB.2.1 hLB.2.2.1 rfl (s' := { s with dmem := (storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 108) 32 0).storeInt (arg2 t₀ + BitVec.ofNat 64 76) 32 0, zmms := s.zmms })
      have hZ2 : Zr (wr (wr c 108 32 0) 76 32 0) 76 246 :=
        Zr_wr0 (Zr_wr0 hZ (by omega) (by omega) (by omega)) (by omega) (by omega) (by omega)
      have h8 : i32 (wr (wr c 108 32 0) 76 32 0) 8 = 0 ∨ i32 (wr (wr c 108 32 0) 76 32 0) 8 = 1 := hL2.1.2.1.2.2.2.1.2.2.2.2.2.2
      refine ⟨⟨_, f, hL2.1, hL2.2.1, hL2.2.2.1, hL2.2.2.2,
        by rw [show ne (wr (wr c 108 32 0) 76 32 0) = ne c from hne]; exact h10, fun hw => ?_⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      obtain ⟨r1, r2, r3⟩ := ZW_wr 0 (o := 76) (n := 32) hl1 (by omega) (by omega)
        (ZW_wr 0 (o := 108) (n := 32) hcl (by omega) (by omega) (hW hw))
      have h4 : ne (wr (wr c 108 32 0) 76 32 0) ≤ 5 := by have := r2.2.1; omega
      exact ⟨r1, r2, r3, Zr_IidB hZ2 h8 _ h4, fun _ => Zr_IidB hZ2 h8 5 (by omega)⟩

end Kraken.Examples.Sbr.Ps
