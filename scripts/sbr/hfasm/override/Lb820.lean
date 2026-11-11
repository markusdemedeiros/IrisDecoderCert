set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem blk_Lb820 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb820" := by
  clear hc
  cfg_block
  measure_hb "Lb820"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h8, hxb, hm⟩, hn⟩ := hs₀
    -- G1: the stored low half of xmm4 is in range; `done` takes the cell as `HfIdxOut`
    have hv := hf_xb64 hxb
    simp only [T, FZ, Saved, Rest] at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp only [Rest, T, FZ, Saved, AddrIndex.offset64, BitVec.add_zero] at *
    all_goals try call_simp
    all_goals try (first | omega | with_reducible assumption | grind_cells')
    all_goals try refine ⟨⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try refine hf_idx_intro _ hv.1 hv.2 ?_
    all_goals try (first | omega | with_reducible assumption | grind_cells')
