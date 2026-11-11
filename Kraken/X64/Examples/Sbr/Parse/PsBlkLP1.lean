import Kraken.X64.Examples.Sbr.Parse.PsBlkLPLib

/-!
# `ff_ps_read_data`: `enable_icc = 0`, the `icc` rows cleared

`memset(icc_par, 0, 170)` as six 32-byte stores of `ymm0 = 0` (`[0xf6, 0x1a0)`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Ps

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option maxRecDepth 20000 in
/-- `vpxor`, then the stores at `0x180`, `0x176`. -/
theorem blk_Lc86 (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc86" := by
  cfg_block
  simp only [tab_Lc86, var_Lc86, tab_Lc9a, var_Lc9a]
  measure_hb "Lc86"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hAI, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hAI.1.1.2.2
    have hcl := LB_cl hAI.1
    have hax := hAI.2.2.2
    have ad : ∀ (d : Int64) (dn : Nat), d.toBitVec = BitVec.ofNat 64 dn →
        s₀.regs.get64 .rax + AddrIndex.offset64 none s₀.regs + d.toBitVec
          = arg2 t₀ + BitVec.ofNat 64 dn := by
      intro d dn h; rw [hax, AddrIndex.offset64_none, h]
      exact congrArg (· + BitVec.ofNat 64 dn) (BitVec.add_zero _)
    have hl1 : (wr c 384 32 0).length = 764 := by rw [wr_length _ _ _ _ (by omega)]; exact hcl
    have hm1 := Fr_c_store hm hcl 384 32 (by omega) 0
    have hm2 := Fr_c_store hm1 hl1 374 32 (by omega) 0
    vcgen
    case vc1 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 384 384 rfl, Fr_c_load hm hcl 384 32 (by omega)]; rfl
    case vc2 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 384 384 rfl, ad 374 374 rfl, l5_vpxor_ymm, BitVec.toInt_zero,
        Fr_c_load hm1 hl1 374 32 (by omega)]; rfl
    case vc3 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 384 384 rfl, ad 374 374 rfl, l5_vpxor_ymm, BitVec.toInt_zero]
      refine ⟨⟨_, f, lp_AI_wrc (s := { s with dmem := storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 384) 32 0 })
        (lp_AI_wrc hAI rfl hm1 (by omega) (by omega)) rfl hm2 (by omega) (by omega),
        by simp only [BitVec.xor_self, l5_set0_ymm, BitVec.ofNat_eq_ofNat],
        Zr_wr0 (Zr_wr0 (Zr_nil c 416) (by omega) (by omega) (by omega)) (by omega) (by omega) (by omega),
        fun hw => lp_WZ_wr 0 hl1 (lp_WZ_wr 0 hcl (lp_WZ_of_WC (hW hw)) (by omega) (by omega))
          (by omega) (by omega)⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩

set_option maxRecDepth 20000 in
/-- The stores at `0x156`, `0x136`. -/
theorem blk_Lc9a (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Lc9a" := by
  cfg_block
  simp only [tab_Lc9a, var_Lc9a, tab_Lcaa, var_Lcaa]
  measure_hb "Lc9a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hAI, hy, hZ, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hAI.1.1.2.2
    have hcl := LB_cl hAI.1
    have hax := hAI.2.2.2
    have ad : ∀ (d : Int64) (dn : Nat), d.toBitVec = BitVec.ofNat 64 dn →
        s₀.regs.get64 .rax + AddrIndex.offset64 none s₀.regs + d.toBitVec
          = arg2 t₀ + BitVec.ofNat 64 dn := by
      intro d dn h; rw [hax, AddrIndex.offset64_none, h]
      exact congrArg (· + BitVec.ofNat 64 dn) (BitVec.add_zero _)
    have hl1 : (wr c 342 32 0).length = 764 := by rw [wr_length _ _ _ _ (by omega)]; exact hcl
    have hm1 := Fr_c_store hm hcl 342 32 (by omega) 0
    have hm2 := Fr_c_store hm1 hl1 310 32 (by omega) 0
    have hy0 : (s₀.zmms.get (AvxReg.ymm RegMm.mm0)).toInt = 0 := by rw [hy]; rfl
    vcgen
    case vc1 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 342 342 rfl, Fr_c_load hm hcl 342 32 (by omega)]; rfl
    case vc2 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 342 342 rfl, ad 310 310 rfl, hy0, Fr_c_load hm1 hl1 310 32 (by omega)]; rfl
    case vc3 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 342 342 rfl, ad 310 310 rfl, hy0]
      refine ⟨⟨_, f, lp_AI_wrc (s := { s with dmem := storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 342) 32 0 })
        (lp_AI_wrc hAI rfl hm1 (by omega) (by omega)) rfl hm2 (by omega) (by omega),
        hy,
        Zr_wr0 (Zr_wr0 hZ (by omega) (by omega) (by omega)) (by omega) (by omega) (by omega),
        fun hw => lp_WZ_wr 0 hl1 (lp_WZ_wr 0 hcl (hW hw) (by omega) (by omega))
          (by omega) (by omega)⟩, Kraken.lex_cons_le_of_lt rfl (by decide)⟩

set_option maxRecDepth 20000 in
/-- The stores at `0x116`, `0xf6`: `icc_par` is clear, so in range. -/
theorem blk_Lcaa (k : Nat) (Ext : Mem 64 → Prop) (x : PArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k Ext x ra t₀ "ff_ps_read_data.Lcaa" := by
  cfg_block
  simp only [tab_Lcaa, var_Lcaa, tab_Lcba, var_Lcba]
  measure_hb "Lcaa"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨c, f, hAI, hy, hZ, hW⟩, hn⟩ := hs₀
    subst hn
    have hm := hAI.1.1.2.2
    have hcl := LB_cl hAI.1
    have hax := hAI.2.2.2
    have ad : ∀ (d : Int64) (dn : Nat), d.toBitVec = BitVec.ofNat 64 dn →
        s₀.regs.get64 .rax + AddrIndex.offset64 none s₀.regs + d.toBitVec
          = arg2 t₀ + BitVec.ofNat 64 dn := by
      intro d dn h; rw [hax, AddrIndex.offset64_none, h]
      exact congrArg (· + BitVec.ofNat 64 dn) (BitVec.add_zero _)
    have hl1 : (wr c 278 32 0).length = 764 := by rw [wr_length _ _ _ _ (by omega)]; exact hcl
    have hm1 := Fr_c_store hm hcl 278 32 (by omega) 0
    have hm2 := Fr_c_store hm1 hl1 246 32 (by omega) 0
    have hy0 : (s₀.zmms.get (AvxReg.ymm RegMm.mm0)).toInt = 0 := by rw [hy]; rfl
    have hZ2 : Zr (wr (wr c 278 32 0) 246 32 0) 246 416 :=
      Zr_wr0 (Zr_wr0 hZ (by omega) (by omega) (by omega)) (by omega) (by omega) (by omega)
    vcgen
    case vc1 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 278 278 rfl, Fr_c_load hm hcl 278 32 (by omega)]; rfl
    case vc2 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 278 278 rfl, ad 246 246 rfl, hy0, Fr_c_load hm1 hl1 246 32 (by omega)]; rfl
    case vc3 =>
      rename_i s hs; subst hs; try dsimp only
      rw [ad 278 278 rfl, ad 246 246 rfl, hy0]
      obtain ⟨⟨hCm, hR, hI, hLS⟩, h10, h1c, -⟩ :=
        lp_AI_wrc (s := { s with dmem := storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 278) 32 0 })
          (lp_AI_wrc hAI rfl hm1 (by omega) (by omega)) (s' := { s with
            dmem := storeInt (storeInt s.dmem (arg2 t₀ + BitVec.ofNat 64 278) 32 0)
              (arg2 t₀ + BitVec.ofNat 64 246) 32 0 }) rfl hm2 (by omega) (by omega)
      refine ⟨⟨_, f, hCm, hR, hI, hLS, h1c, h10, fun hw => ?_⟩,
        Kraken.lex_cons_le_of_lt rfl (by decide)⟩
      obtain ⟨h0, hP, hH, hS, hB, hZz⟩ :=
        lp_WZ_wr (o := 246) (n := 32) 0 hl1 (lp_WZ_wr (o := 278) (n := 32) 0 hcl (hW hw) (by omega) (by omega)) (by omega) (by omega)
      exact ⟨lp_Rng_of h0 hP hZ2, hH, hS, hB, hZz⟩

end Kraken.Examples.Sbr.Ps
