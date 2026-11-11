import Kraken.X64.Examples.Sbr.Parse.TlimMc

/-!
# `sbr_make_f_tablelim`: after the sort (`L429d`, `L42b6`, `L42bc`)

`n_lim = n[0] + num_patches - 1` is stored and checked against the array size; the compaction
loop starts with `out` at `f_tablelim`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

theorem nl_val (a b : Nat) (h1 : 1 ≤ a + b) (h : a + b < 2 ^ 31) :
    BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 a) + BitVec.setWidth 32 (BitVec.ofNat 64 b))) - 1#32))
      = BitVec.ofNat 32 (a + b - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem nl_val64 (a b : Nat) (h1 : 1 ≤ a + b) (h : a + b < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64
      (BitVec.setWidth 32 (BitVec.ofNat 64 a) + BitVec.setWidth 32 (BitVec.ofNat 64 b))) - 1#32)
      = BitVec.ofNat 64 (a + b - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem toInt32_small (n : Nat) (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).toInt = (n : Int) := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp only [BitVec.toNat_ofNat]; omega
  · simp [BitVec.msb_eq_decide]; omega

theorem a_cmp30 (n : Nat) (h : n ≤ 30) (f : StatusFlags.from_result.Remaining)
    (hf : f.cf = ((BitVec.ofNat 32 n - BitVec.setWidth 32 30#64).unsigned
      != (BitVec.ofNat 32 n).unsigned - (BitVec.setWidth 32 30#64).unsigned)) :
    CondCode.a.interp (StatusFlags.from_result (BitVec.ofNat 32 n - BitVec.setWidth 32 30#64) f)
      = false := by
  rw [CondCode.interp_a_sub _ _ f hf]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, decide_eq_false_iff_not]
  omega

variable [CodeEnv]

theorem blk_L429d (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L429d" := by
  cfg_block
  measure_hb "L429d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hax, hNN, hlb⟩, fl, stk, pb, hL, hP, hS, hm⟩, hn⟩ := hs₀
    rw [var_L429d] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hl0 := RO_n0 (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    have hl1 := RO_np (focus (T_ro k x ra t₀ (Saved t₀) _) hm)
    rw [show sA t₀ = s₀.regs.get64 .rbx from hbx.symm] at hl0 hl1
    have hb' : s₀.regs.get64 .rbx + 311788#64 = sA t₀ + 0x4c1ec#64 := by rw [hbx]
    have hb' : s₀.regs.get64 .rbx + 311788#64 = sA t₀ + 0x4c1ec#64 := by rw [hbx]
    have hs4 : Hide (∀ v, s₀.dmem.storeInt (s₀.regs.get64 .rbx + 311788#64) 4 v =⋆
        Int.toBytes 4 v =@ (sA t₀ + 0x4c1ec#64) ⋆ Tnl k x ra t₀ (Saved t₀) fl stk pb) := by
      intro v
      rw [hb']
      exact storeInt_sep _ 4 _ _ _ ⟨focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm,
        Int.toBytes_length 4 _⟩ v
    have hl4 : (s₀.dmem.loadInt (s₀.regs.get64 .rbx + 311788#64) 4).isSome = true := by
      rw [hb', loadInt_sep _ _ 4 _ _ (focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, x.a.nlim, stk, pb⟩) hm)
        (Int.toBytes_length 4 _) (by omega)]; rfl
    have hNN31 : x.a.n0 + x.a.npatch < 2 ^ 31 := by omega
    have e1 := nl_val x.a.n0 x.a.npatch hNN hNN31
    have e2 := nl_val64 x.a.n0 x.a.npatch hNN hNN31
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, hl0, hl1, hl4,
      Option.isSome_some, Option.some.injEq, AddrIndex.offset64_none, BitVec.add_zero] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt_ofBytes_toBytes_eq 32 4 rfl, BitVec.ofInt_natCast,
      zx_small _ (show x.a.n0 < 2 ^ 31 by omega), zx_small _ (show x.a.npatch < 2 ^ 31 by omega)] at *
    rw [tab_L42b6, var_L42b6]
    rw [e1, e2]
    refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_, hNN, hlb, ?_, a_cmp30 _ (by omega) _ (by rfl),
      fl, stk, pb, ⟨hL.1, hL.2.1, hL.2.2⟩, hP, hS, ?mem⟩, Nat.le_refl _⟩
    case mem =>
      unfold Hide at hs4
      have h5 := hs4 (BitVec.ofNat 32 (x.a.n0 + x.a.npatch - 1)).toInt
      rw [toInt32_small _ (by omega)] at h5
      rw [toInt32_small _ (by omega)]
      exact focus (T_nl k x ra t₀ (Saved t₀) ⟨fl, _, stk, pb⟩).symm h5
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, h14, hax]
    all_goals try rfl

theorem ld4_nl {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {st : TSt}
    (hm : s.dmem =⋆ T k x ra t₀ FR st) (hbx : s.regs.get64 .rbx = sA t₀) (hnl : st.nl < 2 ^ 31) :
    ld4 s (s.regs.get64 .rbx + 0x4c1ec#64) = st.nl := by
  rw [ld4, hbx, loadInt_sep _ _ 4 _ _ (focus (T_nl k x ra t₀ FR st) hm) (Int.toBytes_length 4 _)
    (by omega), Int.ofBytes_toBytes_of_lt 4 _ (by omega) (by omega)]
  rfl

theorem blk_L42b6 (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L42b6" := by
  cfg_block
  measure_hb "L42b6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, hR, h14, hax, hNN, hlb, hdx, hfl, hrest⟩, hn⟩ := hs₀
    rw [var_L42b6] at hn
    subst hn
    have hH : Hide _ := hrest
    clear hrest
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    · exfalso
      have := hfl
      rw [‹CondCode.a.interp _ = true›] at this
      exact Bool.noConfusion this
    · rw [tab_L42bc, var_L42bc]
      exact ⟨⟨hC, hR, h14, hax, hNN, hlb, hdx, hH⟩, Nat.le_refl _⟩

theorem blk_L42bc (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L42bc" := by
  cfg_block
  measure_hb "L42bc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hax, hNN, hlb, hdx, fl, stk, pb, hL, hP, hS, hm⟩, hn⟩ := hs₀
    rw [var_L42bc] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    have hld := ld4_nl hm hbx (show NN x - 1 < 2 ^ 31 by simp only [NN]; omega)
    simp only [ld4] at hld
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    left; apply Table.ofLabels_at
    refine ⟨by decide, ?_, Or.inl ?_⟩
    · rw [tab_L42eb]
      unfold Hide at hmT
      refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, AV fl, fl, stk, pb, 1, 0, NN x - 1, hL, hP,
        ⟨hS, by simp only [NN]; omega, by omega, by simp only [NN]; omega, ?_, ?_, fun r R h => h⟩,
        ?_, hmT⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx, h14,
        hax, hdx]
      all_goals try (simp; done)
    · rw [var_L42eb]
      simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbx, h14] at hld ⊢
      rw [hld]
      try simp only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_div, Nat.sub_zero, NN]
      omega

end Kraken.Examples.Sbr.Tlim
