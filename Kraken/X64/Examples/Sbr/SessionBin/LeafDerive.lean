import Kraken.X64.Examples.Sbr.SessionBin.Defs

/-!
# Session hypotheses that follow from others

* `sbrA_aligned`: `sbr = che + 0x28920` is 32-aligned when `che` is (`0x28920 = 32 · 5193`).
* `memcpy_of_val`, `memset_of_val`: apply's `memcpy`/`memset` contracts (raw footprints,
  `MemcpySpec`, `MemsetSpec`) follow from the parser's value contracts (`MemcpyValSpec`,
  `MemsetValSpec`): the source bytes of a raw block are some bytes, and written cells are
  raw blocks of their length.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.SessionBin

/-! ## The element's alignment -/

/-- `sbr` is 32-aligned when `che` is. -/
theorem sbrA_aligned {t : MachineData} (h : isAligned 32 (arg1 t) = true) :
    isAligned 32 (sbrA t) = true := by
  simp only [isAligned, beq_iff_eq] at h ⊢
  simp only [sbrA, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## `memcpy` and `memset` -/

theorem lf_imp_r2 {A B P Q : Mem 64 → Prop} (h : ∀ m, P m → Q m) {m : Mem 64}
    (hm : (A ⋆ (B ⋆ P)) m) : (A ⋆ (B ⋆ Q)) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, hd⟩ := hm
  exact ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, h d hd⟩

theorem lf_ex_r2 {α : Type} {A B : Mem 64 → Prop} {P : α → Mem 64 → Prop} {m : Mem 64}
    (hm : (A ⋆ (B ⋆ fun m => ∃ u, P u m)) m) : ∃ u, (A ⋆ (B ⋆ P u)) m := by
  obtain ⟨a, b, hu, hi, ha, c, d, hu2, hi2, hc, u, hd⟩ := hm
  exact ⟨u, a, b, hu, hi, ha, c, d, hu2, hi2, hc, hd⟩

/-- Known bytes are a raw block of their length. -/
theorem lf_blk {a : BitVec 64} {bs : List UInt8} {n : Nat} {m : Mem 64} (hl : bs.length = n)
    (hn : n ≤ 2 ^ 64) (h : (bs =@ a) m) : (n ?@ a) m :=
  ⟨hn, bs, hl, h⟩

theorem lf_n (t : MachineData) : (arg2 t).toNat ≤ 2 ^ 64 := by
  have := (arg2 t).isLt
  omega

/-- `memcpy`'s raw footprint as the source's bytes and the raw destination. -/
theorem lf_mc_pre (a b : BitVec 64) (n : Nat) (R : Mem 64 → Prop) (m : Mem 64)
    (h : (Blocks [(a, n), (b, n)] ⋆ R) m) :
    ∃ s : {l : List UInt8 // l.length = n}, ((s.1 =@ b ⋆ n ?@ a) ⋆ R) m := by
  simp only [Blocks] at h
  obtain ⟨m1, m2, hu, hi, ⟨m3, m4, hu2, hi2, hA, ⟨-, bs, hl, hbs⟩⟩, hR⟩ := h
  refine ⟨⟨bs, hl⟩, m1, m2, hu, hi, ?_, hR⟩
  rw [Std.ExtHashMap.sep_comm]
  exact ⟨m3, m4, hu2, hi2, hA, hbs⟩

/-- `memcpy`'s value footprint afterwards as the raw one. -/
theorem lf_mc_post {a b : BitVec 64} {src : List UInt8} {n : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} (hl : src.length = n) (hn : n ≤ 2 ^ 64) (h : ((src =@ b ⋆ src =@ a) ⋆ R) m) :
    (Blocks [(a, n), (b, n)] ⋆ R) m := by
  simp only [Blocks]
  obtain ⟨m1, m2, hu, hi, ⟨m3, m4, hu2, hi2, hB, hA⟩, hR⟩ := h
  refine ⟨m1, m2, hu, hi, ?_, hR⟩
  rw [Std.ExtHashMap.sep_comm]
  exact ⟨m3, m4, hu2, hi2, lf_blk hl hn hB, lf_blk hl hn hA⟩

variable [CodeEnv]

/-- Apply's `memcpy` contract from the value contract. -/
theorem memcpy_of_val {k : Nat} (h : MemcpyValSpec k) : MemcpySpec k := by
  rintro R ra t ⟨hcall, -⟩
  obtain ⟨⟨src, hl⟩, hc⟩ := lf_ex_r2 (lf_imp_r2 (P := MemcpyF t ⋆ R)
    (fun m hm => lf_mc_pre (arg0 t) (arg1 t) (arg2 t).toNat R m hm) hcall)
  refine eventually_weaken _ _ _ _ (fun s hs => ⟨hs.1, ?_⟩) (h ⟨R, src⟩ ra t ⟨hc, hl⟩)
  obtain ⟨h1, h2, h3, hm⟩ := hs.2
  exact ⟨h1, h2, h3, lf_imp_r2 (fun m hm' => lf_mc_post hl (lf_n t) hm') hm⟩

/-- Apply's `memset` contract from the value contract. -/
theorem memset_of_val {k : Nat} (h : MemsetValSpec k) : MemsetSpec k := by
  rintro R ra t ⟨hcall, -⟩
  refine eventually_weaken _ _ _ _ (fun s hs => ⟨hs.1, ?_⟩) (h ⟨R⟩ ra t hcall)
  obtain ⟨-, h1, h2, h3, hm⟩ := hs.2
  refine ⟨h1, h2, h3, lf_imp_r2 (fun m hm' => ?_) hm⟩
  obtain ⟨m1, m2, hu, hi, hA, hR⟩ := hm'
  exact ⟨m1, m2, hu, hi, lf_blk (List.length_replicate ..) (lf_n t) hA, hR⟩

end Kraken.Examples.Sbr.SessionBin
