import Kraken.X64.Examples.Sbr.Parse.GridShB1

/-!
# `read_sbr_grid`: `VARVAR` (class 3), `bs_num_env` and the first `t_env` loop

The check `bs_num_rel_0 + bs_num_rel_1 + 1 ≤ 5`, `bs_num_env`, `t_env[bs_num_env]`, and the
unrolled `t_env[i + 1] = t_env[i] + 2 * get_bits(gb, 2) + 2` for `i < bs_num_rel_0`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Grid

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

section
variable {p : Program} {Q : Unit → MachineData → Prop} {E : Int64 → MachineData → Prop}

/-- `incl %r`: the 32-bit sum, zero-extended into the register; the carry flag is kept
(as `dec_reg_w32_spec`). -/
@[spec low] theorem shB_inc_reg_w32_spec (asz : Width) (r : Reg64) :
    ⦃ fun s =>
        let a := (s.regs.get64 r).setWidth 32
        let v := a + 1
        WP.wp p Q E
          { s with
              regs := s.regs.set64 r (v.setWidth 64),
              status := StatusFlags.from_result v
                  { cf := s.status.cf,
                    af := (v.take 4).unsigned != (a.take 4).unsigned + 1,
                    of := v.signed != a.signed + 1 } } ⦄
      (Directive.instr (.regular asz .W32 (.inc (.reg (.low r .W32)))) :: p)
    ⦃ Q; E ⦄ :=
  fallthrough_spec (fun s rng P hP => by
    simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp,
      MachineData.set, MachineData.setReg, Reg64s.get_low32, Reg64s.set_low32, Effects.All]
    exact hP)

end

omit [CodeEnv] in
/-- `cmp $5, %r9d; jl`: the sum of two 2-bit values is below 5. -/
theorem shB_l_lt5 (c : BitVec 64) (hc : c.toNat < 8)
    (h : CondCode.l.interp
      (StatusFlags.from_result
        (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c)) - BitVec.setWidth 32 5#64)
        { cf := (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c))
                - BitVec.setWidth 32 5#64).unsigned !=
              (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c))).unsigned
                - (BitVec.setWidth 32 5#64).unsigned,
          af := ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c))
                - BitVec.setWidth 32 5#64).take 4).unsigned !=
              ((BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c))).take 4).unsigned
                - ((BitVec.setWidth 32 5#64).take 4).unsigned,
          of := (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c))
                - BitVec.setWidth 32 5#64).signed !=
              (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 c))).signed
                - (BitVec.setWidth 32 5#64).signed }) = true) :
    c.toNat < 5 := by
  have : c = 0#64 ∨ c = 1#64 ∨ c = 2#64 ∨ c = 3#64 ∨ c = 4#64 ∨ c = 5#64 ∨ c = 6#64 ∨ c = 7#64 := by
    bv_omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | (revert h; decide)

omit [CodeEnv] in
theorem shB_add_lt8 (a b : BitVec 64) (ha : a.toNat < 4) (hb : b.toNat < 4) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add]; omega

omit [CodeEnv] in
theorem shB_inc_ecx (a b : BitVec 64) (ha : a.toNat < 4) (hb : b.toNat < 4) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (a + b))) + 1)
      = a + b + 1#64 := by
  rcases lt4_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases lt4_cases b hb with rfl | rfl | rfl | rfl <;> rfl

/-- `bs_num_env = bs_num_rel_0 + bs_num_rel_1 + 1`, checked against `5`. -/
theorem blk_L474b (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L474b" := by
  cfg_block
  measure_hb "L474b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hS, hax, hsi, h8⟩, hm⟩, hn⟩ := hs₀
    have hav := T_load_avctx hm
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have hmT : Hide _ := hm
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hdi] at *
    all_goals try simp only [hav, Option.isSome_some]
    · have hl := shB_l_lt5 _ (by rw [shB_add_lt8 _ _ hax hsi]; omega) ‹CondCode.l.interp _ = true›
      rw [shB_add_lt8 _ _ hax hsi] at hl
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, ?_, ?_, st, ⟨hS, ?_, ?_, ?_, ?_, ?_⟩, hmT⟩, by edge_lt⟩
      all_goals simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      · exact pR.down
      · exact hdx
      · exact pdi.down
      · exact hax
      · exact hsi
      · exact h8
      · omega
      · exact shB_inc_ecx _ _ hax hsi
    · simp only [hav, Option.some.injEq] at *
      subst_vars
      left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨⟨hC, ?_, ?_, st, hS, hmT⟩, ?_⟩, by edge_lt⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt]
      · exact pR.down.1
      · exact pR.down.2.2.1


omit [CodeEnv] in
/-- After `bs_num_env = N` and `t_env[N] = w ≤ 19`: the body invariant (the analogue of
`sinvF_n`). -/
theorem shB_sinv_frpre {x : GArgs} {st : GSt} {N : BitVec 32} {w : BitVec 8} (hS : SInv x st)
    (h1 : 1 ≤ N.toNat) (h5 : N.toNat ≤ 5) (hw : w.toNat ≤ 19) :
    FrPre x ((st.withN N).setTe N.toNat w) := by
  obtain ⟨⟨hfl, hil, htl, hql, hn8, hfr, hnn, hinv, hy, hte9, htq, -⟩, -, hi⟩ := hS
  simp only [GSt.dv] at *
  refine ⟨⟨hfl, ?_, hql, ?_, hnn, ?_, htq, hi, hfr 0 (Nat.zero_le _)⟩, h1, ?_⟩
  · simp only [List.length_set]; exact htl
  · show N.toNat ≤ 8; omega
  · simp only [u8] at *
    rw [getD_set_ne _ _ _ _ (by omega)]; exact hte9
  · simp only [u8]
    rw [getD_set_eq _ _ _ (by omega), UInt8.toNat_ofBitVec]; exact hw

omit [CodeEnv] in
/-- `cmp $9, %ecx; jae` with `ecx = a + b + 1 ≤ 5`: not taken. -/
theorem shB_nc9 (a b : BitVec 64) (ha : a.toNat < 4) (hb : b.toNat < 4) (hab : a.toNat + b.toNat ≤ 4) :
    CondCode.nc.interp
      (StatusFlags.from_result
        (BitVec.setWidth 32 (a + b + 1#64) - BitVec.setWidth 32 9#64)
        { cf := (BitVec.setWidth 32 (a + b + 1#64) - BitVec.setWidth 32 9#64).unsigned !=
              (BitVec.setWidth 32 (a + b + 1#64)).unsigned - (BitVec.setWidth 32 9#64).unsigned,
          af := ((BitVec.setWidth 32 (a + b + 1#64) - BitVec.setWidth 32 9#64).take 4).unsigned !=
              ((BitVec.setWidth 32 (a + b + 1#64)).take 4).unsigned - ((BitVec.setWidth 32 9#64).take 4).unsigned,
          of := (BitVec.setWidth 32 (a + b + 1#64) - BitVec.setWidth 32 9#64).signed !=
              (BitVec.setWidth 32 (a + b + 1#64)).signed - (BitVec.setWidth 32 9#64).signed }) = false := by
  rcases lt4_cases a ha with rfl | rfl | rfl | rfl <;>
    rcases lt4_cases b hb with rfl | rfl | rfl | rfl <;> first | decide | (simp at hab)

omit [CodeEnv] in
/-- `test %esi, %esi; jle` for `esi < 4`: taken iff `esi = 0`. -/
theorem shB_le_test (v : BitVec 64) (hv : v.toNat < 4) (af : Bool) :
    CondCode.le.interp (StatusFlags.from_result
        (BitVec.setWidth 32 v &&& BitVec.setWidth 32 v) { cf := false, af := af, of := false })
      = decide (v.toNat = 0) := by
  rcases lt4_cases v hv with rfl | rfl | rfl | rfl <;> cases af <;> decide

omit [CodeEnv] in
theorem shB_n32 (a b : BitVec 64) (ha : a.toNat < 4) (hb : b.toNat < 4) :
    (BitVec.setWidth 32 (a + b + 1#64)).toNat = a.toNat + b.toNat + 1 := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

omit [CodeEnv] in
theorem shB_w16 (r : BitVec 64) (h : r.toNat < 4) :
    (BitVec.setWidth 8 (r.replaceLow (BitVec.setWidth 8 16#64 + BitVec.setWidth 8 r))).toNat ≤ 19 := by
  rcases lt4_cases r h with rfl | rfl | rfl | rfl <;> decide

/-- `bs_num_env` and `t_env[bs_num_env] = bs_var_bord_1 + 16`. -/
theorem blk_L4925 (k : Nat) (hk : k ≤ 2 ^ 32) (Ext : Mem 64 → Prop)
    (x : GArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k Ext x ra t₀ "read_sbr_grid.L4925" := by
  cfg_block
  measure_hb "L4925"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dsimp only [reduceTable, reduceVar] at hs₀
    obtain ⟨⟨hC, hR, hdx, hdi, st, ⟨hS, hax, hsi, h8, has, hcx⟩, hm⟩, hn⟩ := hs₀
    have htl : st.te.length = 10 := hS.1.2.2.1
    have hst : ∀ (N : BitVec 32) (w : BitVec 8), N.toNat < 10 →
        (s₀.dmem.storeInt (arg3 t₀ + 8#64) 4 N.toInt).storeInt
          (arg3 t₀ + N.setWidth 64 + 0x15a9c#64) 1 w.toInt
          =⋆ T k Ext x ra t₀ (Saved t₀) ((st.withN N).setTe N.toNat w) := fun N w h => by
      have := T_storeTe (T_storeN hm N) htl N.toNat h w
      rwa [BitVec.ofNat_toNat] at this
    have hln := T_loadN hm
    have hlt : ∀ N : BitVec 32, N.toNat < 10 → ((s₀.dmem.storeInt (arg3 t₀ + 8#64) 4 N.toInt).loadInt
        (arg3 t₀ + N.setWidth 64 + 0x15a9c#64) 1).isSome := fun N h => by
      have := T_loadTe (T_storeN hm N) N.toNat h
      rw [BitVec.ofNat_toNat] at this
      rw [this]; rfl
    have pR : PLift (RB t₀ s₀) := ⟨hR⟩
    have pdi : PLift (s₀.regs.get64 .rdi = arg0 t₀) := ⟨hdi⟩
    have pdx : PLift (s₀.regs.get64 .rdx = arg2 t₀) := ⟨hdx⟩
    have hrbx : s₀.regs.get64 .rbx = arg3 t₀ := hR.2.2.2
    have hNv := shB_n32 _ _ hax hsi
    have hnc := shB_nc9 _ _ hax hsi has
    have hw := shB_w16 _ h8
    have hM := hst (BitVec.setWidth 32 (s₀.regs.get64 .rax + s₀.regs.get64 .rsi + 1#64))
      (BitVec.setWidth 8 ((s₀.regs.get64 .r8).replaceLow
        (BitVec.setWidth 8 16#64 + BitVec.setWidth 8 (s₀.regs.get64 .r8)))) (by rw [hNv]; omega)
    have hF := shB_sinv_frpre (N := BitVec.setWidth 32 (s₀.regs.get64 .rax + s₀.regs.get64 .rsi + 1#64))
      hS (by rw [hNv]; omega) (by rw [hNv]; omega) hw
    have pcx : PLift (s₀.regs.get64 .rcx = s₀.regs.get64 .rax + s₀.regs.get64 .rsi + 1#64) := ⟨hcx⟩
    have pM : PLift _ := ⟨hM⟩
    have pF : PLift _ := ⟨hF⟩
    clear hM hF
    clear hm
    vcgen
    all_goals try dsimp only [reduceTable, reduceVar] at *
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      hrbx, hcx] at *
    all_goals try simp only [hnc, Bool.false_eq_true] at *
    all_goals try simp only [shB_le_test _ hsi, decide_eq_true_eq, decide_eq_false_iff_not] at *
    · rw [hln]; rfl
    · exact hlt _ (by rw [hNv]; omega)
    · left; apply Table.ofLabels_at; dsimp only [reduceTable, reduceVar]
      refine ⟨by decide, ⟨hC, ?_, pdx.down, pdi.down, ?_⟩, by edge_lt⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      · refine ⟨_, ⟨pF.down, ?_, hax, ?_, ?_⟩, pM.down⟩
        · show (BitVec.setWidth 32 _).toNat ≤ 5; rw [hNv]; omega
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
          show _ ≤ (BitVec.setWidth 32 _).toNat; rw [hNv]; omega
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, pcx.down]
    · refine ⟨⟨hC, ?_, pdx.down, pdi.down, ?_⟩, Nat.le_refl _⟩
      · simp only [RB, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        exact pR.down
      · refine ⟨_, ⟨pF.down, ?_, ?_, hsi, hax, ?_⟩, pM.down⟩
        · show (BitVec.setWidth 32 _).toNat ≤ 5; rw [hNv]; omega
        · omega
        · show (BitVec.setWidth 32 _).toNat = _; rw [hNv]

end Kraken.Examples.Sbr.Grid
