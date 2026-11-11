import Kraken.X64.Examples.Sbr.Parse.TlimFin
import Kraken.X64.Examples.Sbr.Parse.TlimBlkD

/-!
# `sbr_make_f_tablelim`: the compaction loop (`L42eb` … `L4370`, `L42d0`)

`in`/`out` are `rax`/`rcx`, `n_lim` is in memory; each pass takes one of the `Compact` steps
(`adv` at `L42d0`, `drop` at `L4370`, `repl` at `L4363`). The variant is `64 (n_lim - out)`
plus a per-block offset.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Tlim

theorem zx32 (n : Nat) (h : n < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 64 n)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]; omega

theorem rsi_eq (p : BitVec 64) (L : Nat) (h : L < 2 ^ 31) :
    p + BitVec.ofNat 64 L * 2#64 = p + BitVec.ofNat 64 (2 * L) := by
  bv_omega

theorem addr_toNat (p : BitVec 64) (n : Nat) (h : p.toNat + n < 2 ^ 64) :
    (p + BitVec.ofNat 64 n).toNat = p.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem lb_pos {lb : BitVec 32} (h : lb ≠ 0#32) : 0 < lb.toNat :=
  Nat.pos_of_ne_zero fun e => h (BitVec.eq_of_toNat_eq (by simp [e]))

theorem zx16u (l : List UInt8) (q : Nat) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofInt 16 (u16 l q : Int)))
      = BitVec.ofNat 64 (u16 l q) := zx16 _ (u16_lt l q)

variable [CodeEnv]

theorem pA_toNat {x : TArgs} {t₀ : MachineData} (hC : TlimC x.lb x.a t₀) :
    (pA t₀).toNat = (arg0 t₀).toNat + 0x4c2f2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hw⟩ := hC
  simp only [pA]
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem mu_val {k : Nat} {x : TArgs} {ra : Int64} {t₀ s : MachineData}
    {FR : (Mem 64 → Prop) → Mem 64 → Prop} {fl stk pb : List UInt8} {L o : Nat}
    (hm : s.dmem =⋆ T k x ra t₀ FR ⟨fl, L, stk, pb⟩) (hbx : s.regs.get64 .rbx = sA t₀)
    (h14 : s.regs.get64 .r14 = pA t₀) (hcx : s.regs.get64 .rcx = pA t₀ + v64 (2 * o))
    (hL : L < 2 ^ 31) (hw : (pA t₀).toNat + 2 * o < 2 ^ 64) : mu s = L - o := by
  simp only [mu, rN]
  rw [ld4_nl hm hbx hL, hcx, h14, addr_toNat _ _ hw]
  show L - _ = _
  omega

/-- The model's array after the loop. -/
theorem fl_mk16 (fl : List UInt8) (h : fl.length = 60) : mk16 30 (AV fl) = fl :=
  (mk16_ext h fun i _ => (Nat.mod_eq_of_lt (u16_lt fl i)).symm).symm

theorem blk_L42eb (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L42eb" := by
  cfg_block
  measure_hb "L42eb"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, hdx, hm⟩, hn⟩ := hs₀
    rw [var_L42eb] at hn
    subst hn
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -, -, -, -, -, -, -, -, hw⟩ := hC'
    have hpA := pA_toNat hC
    have hL31 : L < 2 ^ 31 := by simp only [NN] at hL1; omega
    have hmu := mu_val hm hbx h14 hcx hL31 (by simp only [NN] at hL1; omega)
    subst hi
    have hmT : Hide _ := hm
    clear hm
    vcgen
    all_goals try call_simp
    all_goals rename_i hs hc
    all_goals subst hs
    all_goals simp only [AddrIndex.offset64_scale2, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte,
      Int64.toBitVec_ofNat_norm, BitVec.ofNat_eq_ofNat, BitVec.add_zero, hdx, zx32 L (by omega), h14,
      hcx, rsi_eq _ _ hL31] at hc
    · rw [cc_nc_sub _ _ _ (by rfl), decide_eq_true_eq, addr_toNat (t₀.regs.get64 .rdi + 312050#64) (2 * L) (by omega),
        addr_toNat (t₀.regs.get64 .rdi + 312050#64) (2 * o) (by omega)] at hc
      left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L43bd]
        unfold Hide at hmT
        have hfl : fl.length = 60 := by obtain ⟨h1, -, -⟩ := hL; exact h1
        refine ⟨hC, ⟨?_, ?_, ?_⟩, { x.a with ftLim := mk16 30 (AV fl), nlim := L }, stk, pb,
          Tablelim.pos (lb_pos hlb) hNN hS (hCm _ _ (Compact.done _ _ _ _ (by omega))), rfl, ?_, ?_⟩
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp]
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hbp]
        · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, h13]
        · show Lens ⟨mk16 30 (AV fl), L, stk, pb⟩
          rw [fl_mk16 fl hfl]; exact hL
        · show T k x ra t₀ (Saved t₀) ⟨mk16 30 (AV fl), L, stk, pb⟩ _
          rw [fl_mk16 fl hfl]; exact hmT
      · rw [var_L43bd]; omega
    · rw [cc_nc_sub _ _ _ (by rfl), decide_eq_false_iff_not, addr_toNat (t₀.regs.get64 .rdi + 312050#64) (2 * L) (by omega),
        addr_toNat (t₀.regs.get64 .rdi + 312050#64) (2 * o) (by omega)] at hc
      rw [tab_L42fa, var_L42fa]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨by omega, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx]

theorem blk_L42fa (k : Nat) (_hk : k ≤ 2 ^ 32) (_hMc : MemcpyValSpec k) (x : TArgs) (ra : Int64)
    (t₀ : MachineData) : BlockOb k x ra t₀ "sbr_make_f_tablelim.L42fa" := by
  cfg_block
  measure_hb "L42fa"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h13⟩, hbx⟩, h14, hNN, hlb, sa, fl, stk, pb, i, o, L, hL, hP,
      ⟨hS, hL1, hoL, hi, hcx, hax, hCm⟩, ⟨hol, hdx⟩, hm⟩, hn⟩ := hs₀
    rw [var_L42fa] at hn
    subst hn
    have hfl : fl.length = 60 := by obtain ⟨h1, -, -⟩ := hL; exact h1
    have hL1' : L + 1 ≤ x.a.n0 + x.a.npatch := hL1
    have hC' := hC
    obtain ⟨-, hn0, hnp6, -⟩ := hC'
    subst hi
    have hFl := focus (T_fl k x ra t₀ (Saved t₀) _) hm
    have hli := ld16 hFl _ (addr := s₀.regs.get64 .rax) hax (by simp only [NN]; omega)
      (by simp only; omega)
    have hlo := ld16 hFl o (addr := s₀.regs.get64 .rcx) hcx (by simp only; omega) (by simp only; omega)
    have hmT : Hide _ := hm
    clear hm hFl
    vcgen
    all_goals try call_simp
    all_goals try subst_vars
    all_goals simp only [AddrIndex.offset64_none, BitVec.add_zero, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, hli, hlo, Option.isSome_some, Option.some.injEq] at *
    all_goals try subst_vars
    · left; apply Table.ofLabels_at
      refine ⟨by decide, ?_, Or.inl ?_⟩
      · rw [tab_L42d0]
        refine ⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
          ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_⟩, hmT⟩
        all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
          h14, hcx, hax, hdx, zx16u]
      · rw [var_L42d0]
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
    · rw [tab_L4312, var_L4312]
      refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, hNN, hlb, sa, fl, stk, pb, _, o, L, hL, hP,
        ⟨hS, hL1, hoL, rfl, ?_, ?_, hCm⟩, ⟨hol, ?_, ?_, ?_⟩, hmT⟩, ?var⟩
      case var =>
        simp only [mu, rN, ld4, Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp, h13, hbx,
        h14, hcx, hax, hdx, zx16u]

end Kraken.Examples.Sbr.Tlim
