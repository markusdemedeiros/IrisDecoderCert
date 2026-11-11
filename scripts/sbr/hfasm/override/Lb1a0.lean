set_option maxRecDepth 100000 in
set_option maxHeartbeats 2600000 in
theorem blk_Lb1a0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb1a0" := by
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  clear hG hMc
  cfg_block
  measure_hb "Lb1a0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hm⟩, hn⟩ := hs₀
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    rw [show var "sbr_hf_assemble.Lb1a0" s₀ = 1900000 - 100000 * (s₀.regs.get64 .r10).toNat - 2000 * (BitVec.ofInt 64 ((s₀.dmem.loadInt (s₀.regs.get64 .rsp + 0x248#64) 8).getD 0)).toNat + 200 from rfl] at hn
    rw [show s₀.regs.get64 .rsp + 0x248#64 = t₀.regs.get64 .rsp - 0x40#64 by rw [hrsp]; exact hf_rsp_648_584 _] at hn
    generalize hI : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    generalize hE : (s₀.regs.get64 .r10).toNat = e at *
    have hE2 := And.intro hE trivial
    have h13v := And.intro h13 trivial
    clear hI hV hE h13
    have hi37 : i ≤ 37 := by omega
    have he8 : e < 8 := by omega
    rw [Lb1a0_pre] at hm
    obtain ⟨q, hq, hq4⟩ : ∃ q, (s₀.regs.get64 .rcx).toNat % 2 ^ 32 = q ∧ q < 4 := ⟨_, rfl, by omega⟩
    have hq32 : (s₀.regs.get64 .rcx).setWidth 32 = BitVec.ofNat 32 q := by apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    clear hq
    have hNq := hf_noise_spec q hq4 hN0 hN1 hN2 hN3
    clear hN0 hN1 hN2 hN3
    vcgen [MachineWP.call_mem_proc_spec_at
      (DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x1c8#64),
        ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀ ⋆ (IdxC x t₀
          ⋆ FL2q x t₀ e i v (Rest x.R ra t₀)))))) (hfNoiseFn fs q)
      (Kraken.Executable.ProcSpec.widen (k := k) hNq (Nat.zero_le k) (by omega))]
    all_goals try clear hNq
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280,
      hrsp, hrbp, hq32, BitVec.xor_self, BitVec.setWidth_32_64_32,
      BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    case vc6 =>
         refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · simp only [Option.map_eq_some_iff]
           refine ⟨Int.ofBytes (Int.toBytes 8 (hfNoiseFn fs q).toBitVec.toInt), ?_, hf_fn_load _⟩
           rename_i v8 v7 v6 v5 hcnd l8 l7 l6 l5
           have e5 : BitVec.ofInt 64 v5 = arg2 t₀ := by
             grind_cells'
           rw [e5]
           rcases hf_noise_cases q hq4 with rfl | rfl | rfl | rfl <;> simp only [hfNoiseFn_0, hfNoiseFn_1, hfNoiseFn_2, hfNoiseFn_3] <;> grind_cells'
         · refine Mem.push_slot_res (b := t₀.regs.get64 .rsp - 0x290#64) ?_ ?_ _
           · rw [← T_FL2_callq, Lb1a0_pre]
             first | exact hm | grind_cells'
           · first | rfl | exact hf_rsp_648_8 _ | exact hf_rsp_656_648 _
         · rename_i v8 v7 v6 v5 hcnd l8 l7 l6 l5
           have e8 : BitVec.ofInt 64 v8 = arg2 t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (192 * e) := by
             grind_cells'
           have e6 : BitVec.ofInt 64 v6 = BitVec.ofNat 64 x.m := by
             grind_cells'
           refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hf_noiseK_align h0 q hq4⟩
           · rw [e8]; exact hf_align_row _ _ _ h0.2.1 (by omega) (by omega) (by omega)
           · rcases h9 with h | h <;> rw [h]; exact hf_align_row _ _ _ h0.2.2.1 (by omega) (by omega) (by omega); exact hf_align_qtab _ h0.1
           · rw [e6, BitVec.toNat_ofNat]; omega
           · rw [e6, BitVec.toNat_ofNat]; omega
           · rw [h13v.1]; simp only [BitVec.toNat_setWidth]; omega
         · rename_i v8 v7 v6 v5 hcnd l8 l7 l6 l5
           refine Lb1a0_carve x t₀ x.kx x.m i e _ _ _ _ (BitVec.ofInt 64 v6) _ (hfc_ypos h0) (hfc_y1 h0) hkm hm48 hi37 he8 ?hr9 ?hIt ?e0 ?e1 ?hQ (hf_noiseK_cases q hq4)
           case hIt => rfl
           case e0 => exact h7
           case hQ => exact h9
           case hr9 => grind_cells'
           case e1 => grind_cells'
         · obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
           rw [← T_FL2_callq] at hm'
           have hI' := FL2_read_i hm' (by omega)
           have hra : s'.regs.get64 .rsp + 0x248#64 = t₀.regs.get64 .rsp - 0x40#64 := by
             rw [hrsp']; first | exact hf_rsp_656_8_584 _ | exact hf_rsp_648_584 _
           vcgen
           refine ⟨a1_tbl_rb _ _ _ _ _ s' e i v ⟨h0, ⟨?_, hrbp'⟩, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, ?_, hm'⟩, ?_⟩
           all_goals first
             | (rw [hrsp']; first | exact hf_rsp_656_8 _ | rfl)
             | (rw [hbx']; exact h7)
             | (rw [h12']; exact h8)
             | (rw [h13']; exact h9)
             | (rw [h14']; exact h10)
             | (rw [h15', h12, ← hE2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
             | (rw [hra, hI', h15', h12, hE2.1]; omega)
             | fail
         · grind_cells'
    all_goals first
      | close_cell
      | (exfalso; rename_i hcnd; simp only [CondCode.interp_nc, StatusFlags.cf_from_result, BitVec.unsigned_eq, hf_sub_cf32, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hcnd; omega)
      | fail
