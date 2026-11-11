set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_Lb01d (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb01d" := by
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  clear hN0 hN1 hN2 hN3 hMc
  cfg_block
  measure_hb "Lb01d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hi32 : (s₀.regs.get64 .r15).toNat < 38 := by omega
    have hi37 : (s₀.regs.get64 .r15).toNat ≤ 37 := by omega
    have hsh := hf_shl9 (s₀.regs.get64 .r15) (by omega)
    have hkx4 := hfc_load_lo4 (by rw [FL_kx] at hm; exact hm) (Mem.Split.here _ _)
    have hkx32 := hf_kx32 x.kx (by omega)
    rw [Lb01d_pre] at hm
    vcgen [MachineWP.call_mem_proc_spec_at
      (DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x288#64),
        ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀ ⋆ (IdxC x t₀
          ⋆ FL2g x t₀ (s₀.regs.get64 .r10).toNat (s₀.regs.get64 .r15).toNat (s₀.zmms.get (.xmm .mm4))
            (Rest x.R ra t₀)))))) fs.gfilt
      (Kraken.Executable.ProcSpec.widen (k := k) hG (Nat.zero_le k) (by omega))]
    all_goals try clear hG
    case' vc2 => exfalso
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280,
      hrsp, hrbp, BitVec.xor_self, BitVec.setWidth_32_64_32,
      BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    case vc1 => simp only [hkx4, Option.isSome_some]
    case vc2 =>
      exfalso
      rename_i xv hcond hld
      rw [hkx4, Option.some.injEq] at hld
      subst hld
      rw [hkx32] at hcond
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, BitVec.unsigned_eq,
        hf_sub_cf32, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
        decide_eq_false_iff_not] at hcond
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hcond
      omega
    case vc8 => exact hf_align_xv _ h0.1
    case vc10 =>
      refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
      · simp only [Option.map_eq_some_iff]
        exact ⟨Int.ofBytes (Int.toBytes 8 fs.gfilt.toBitVec.toInt), by grind_cells', hf_fn_load _⟩
      · refine Mem.push_slot_res (b := t₀.regs.get64 .rsp - 0x290#64) ?_ ?_ _
        · rw [← T_FL2_call, Lb01d_post_g1]
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          grind_cells'
        · first | rfl | exact hf_rsp_648_8 _ | exact hf_rsp_656_648 _
      · refine ⟨hf_add2_lt _ hi32, ?_, ?_⟩ <;> simp only [h4, BitVec.toNat_ofNat] <;> omega
      · refine Lb01d_carve' x t₀ x.kx x.m _ _ _ _ _ hkm hi37 ?hD ?e0 ?e1 ?eM
        case e0 => refine hf_add_congr ?_ rfl; grind_cells'
        case hD =>
          rcases h11 with ⟨h11, -⟩ | ⟨h11, -⟩
          · left; refine ⟨hSL x + _, ?_, h11⟩; simp only [hSL]; split <;> omega
          · right; exact ⟨h11, hm48⟩
        case e1 => grind_cells'
        case eM => simp only [h4, BitVec.toNat_ofNat]; omega
      · obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        rw [← T_FL2_call] at hm'
        have hI := FL2_read_i hm' (by omega)
        have hra : s'.regs.get64 .rsp + 0x248#64 = t₀.regs.get64 .rsp - 0x40#64 := by
          rw [hrsp']; first | exact hf_rsp_656_8_584 _ | exact hf_rsp_648_584 _
        vcgen
        refine ⟨g1_tbl_rb _ _ _ _ _ s' _ _ _ ⟨h0, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm'⟩, ?_⟩
        · rw [hrsp']; first | exact hf_rsp_656_8 _ | rfl
        · exact hrbp'
        · exact h5
        · exact h3.1
        · exact h3.2
        · exact h6
        · exact h7
        · rw [hbx', hsh]
          refine hf_add_congr ?_ rfl
          grind_cells'
        · rw [h12']; exact h8
        · rw [h13']
          rcases h11 with h | h
          · exact Or.inl h.2
          · exact Or.inr h.2
        · rw [h14']; exact h10
        · rw [h15', BitVec.ofNat_toNat, BitVec.setWidth_eq]
        · simp only [hra, hI, h15'] at *; omega
      · grind_cells'
    all_goals close_cell
