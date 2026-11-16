import HarmonicBalls.Proofs.Potential.BrownianOccupationWeightedPair

/-! # Weighted spatial Brownian occupation

A bounded weighted near-diagonal estimate for the spatial occupation measure.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The weighted spatial pair integral is bounded simultaneously for all bounded weights. -/
theorem planarBrownianMotion_ae_unit_weighted_occupation_measure_le (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 < C ∧
      ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
      (∀ z, |g z| ≤ M) → ∀ r : ℝ, 0 < r →
        let μ := Measure.map (fun t => b t) ν
        Integrable (fun p : ℂ × ℂ =>
          if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
        (∫ p : ℂ × ℂ, if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) = (∫ p : ℝ≥0 × ℝ≥0,
            if ‖b p.1 - b p.2‖ < r then |g (b p.1)| * |g (b p.2)| else 0
              ∂(ν.prod ν)) ∧
        (∫ p : ℂ × ℂ, if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) ≤ M ^ 2 * (C * r ^ β) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_pair_occupation_le x hβ0 hβ2] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro g hg M hM hgM r hr
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hbm : Measurable b := b.continuous.measurable
  let : IsProbabilityMeasure μ := inferInstance
  let f : ℂ × ℂ → ℝ := fun p =>
    if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
  have hs : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < r} :=
    measurableSet_lt ((measurable_fst.sub measurable_snd).norm) measurable_const
  have hf : Measurable f := by
    exact ((hg.comp measurable_fst).abs.mul (hg.comp measurable_snd).abs).ite hs measurable_const
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs <;> positivity
  have hfbound : ∀ p, f p ≤ M ^ 2 := by
    intro p
    dsimp [f]
    split_ifs
    · calc
        |g p.1| * |g p.2| ≤ M * M := mul_le_mul (hgM _) (hgM _) (abs_nonneg _) hM
        _ = M ^ 2 := by ring
    · positivity
  have hfi : Integrable f (μ.prod μ) := by
    refine (integrable_const (M ^ 2)).mono' hf.aestronglyMeasurable ?_
    filter_upwards with p
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 p)] using hfbound p
  have hmap : μ.prod μ = Measure.map (Prod.map b b) (ν.prod ν) :=
    Measure.map_prod_map ν ν hbm hbm
  refine ⟨hfi, ?_, ?_⟩
  · rw [hmap, integral_map (hbm.prodMap hbm).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hle := hb (fun z => ENNReal.ofReal |g z|) hg.abs.ennreal_ofReal
    (ENNReal.ofReal M) ENNReal.ofReal_lt_top (fun z => ENNReal.ofReal_le_ofReal (hgM z)) r hr
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod μ)) ≤
      ENNReal.ofReal (M ^ 2 * (C * r ^ β)) := by
    rw [hmap, lintegral_map hf.ennreal_ofReal (hbm.prodMap hbm)]
    convert hle using 1
    · apply lintegral_congr
      intro p
      dsimp [f]
      split_ifs <;> simp [ENNReal.ofReal_mul]
    · rw [pow_two, ENNReal.ofReal_mul (mul_nonneg hM hM), ENNReal.ofReal_mul hM, pow_two]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_ofReal (by positivity)] at this
  exact this

end HarmonicBalls
