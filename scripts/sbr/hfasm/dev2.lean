/-- The noise entry `hf_apply_noise[q]` of `sbr->dsp`, by index. -/
def hfNoiseFn (fs : HfFns) (q : Nat) : Int64 :=
  if q = 0 then fs.noise0 else if q = 1 then fs.noise1 else if q = 2 then fs.noise2 else fs.noise3

/-- Its `phi_sign` constant. -/
def hfNoiseK (q : Nat) : BitVec 64 × Nat :=
  if q = 0 then HfApplyNoiseK0 else if q = 1 then HfApplyNoiseK1 else if q = 2 then HfApplyNoiseK2
  else HfApplyNoiseK3

theorem hfNoiseFn_0 (fs : HfFns) : hfNoiseFn fs 0 = fs.noise0 := rfl
theorem hfNoiseFn_1 (fs : HfFns) : hfNoiseFn fs 1 = fs.noise1 := rfl
theorem hfNoiseFn_2 (fs : HfFns) : hfNoiseFn fs 2 = fs.noise2 := rfl
theorem hfNoiseFn_3 (fs : HfFns) : hfNoiseFn fs 3 = fs.noise3 := rfl

theorem hf_noise_cases (q : Nat) (hq : q < 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega

theorem hf_noise_spec {fs : HfFns} (q : Nat) (hq : q < 4)
    (h0 : LeafSpecAt fs.noise0 0 (HfApplyNoiseF HfApplyNoiseK0) (HfApplyNoiseC HfApplyNoiseK0.1))
    (h1 : LeafSpecAt fs.noise1 0 (HfApplyNoiseF HfApplyNoiseK1) (HfApplyNoiseC HfApplyNoiseK1.1))
    (h2 : LeafSpecAt fs.noise2 0 (HfApplyNoiseF HfApplyNoiseK2) (HfApplyNoiseC HfApplyNoiseK2.1))
    (h3 : LeafSpecAt fs.noise3 0 (HfApplyNoiseF HfApplyNoiseK3) (HfApplyNoiseC HfApplyNoiseK3.1)) :
    LeafSpecAt (hfNoiseFn fs q) 0 (HfApplyNoiseF (hfNoiseK q)) (HfApplyNoiseC (hfNoiseK q).1) := by
  rcases hf_noise_cases q hq with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem hf_noiseK_cases (q : Nat) (hq : q < 4) :
    hfNoiseK q = HfApplyNoiseK0 ∨ hfNoiseK q = HfApplyNoiseK1 ∨ hfNoiseK q = HfApplyNoiseK2
      ∨ hfNoiseK q = HfApplyNoiseK3 := by
  rcases hf_noise_cases q hq with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem hf_noiseK_align {x : HfArgs} {t : MachineData} (h : HfC x t) (q : Nat) (hq : q < 4) :
    isAligned 16 (hfNoiseK q).1 = true := by
  rcases hf_noise_cases q hq with rfl | rfl | rfl | rfl
  · exact h.2.2.2.1
  · exact h.2.2.2.2.1
  · exact h.2.2.2.2.2.1
  · exact isAligned_add (by decide) h.2.2.2.2.1 rfl
