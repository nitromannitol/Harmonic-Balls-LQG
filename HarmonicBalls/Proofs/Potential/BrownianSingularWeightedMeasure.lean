import HarmonicBalls.Proofs.Potential.BrownianSingularWeightedPairGeneral

/-! # Singularly weighted spatial Brownian occupation

Near-diagonal estimates for weights dominated by a subcritical inverse power.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The spatial occupation pair integral is controlled for singularly dominated weights. -/
theorem planarBrownianMotion_ae_unit_singular_weighted_occupation_measure_le (x z : ℂ)
    {q β : ℝ} (hq0 : 0 < q) (hq2 : q < 2) (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
      (∀ w, ENNReal.ofReal |g w| ≤ ENNReal.ofReal M *
        (ENNReal.ofReal ‖w-z‖) ^ (-q)) → ∀ r : ℝ, 0 < r →
        let μ := Measure.map (fun t => b t) ν
        Integrable (fun p : ℂ × ℂ =>
          if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
        (∫ p : ℂ × ℂ, if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) = (∫ p : ℝ≥0 × ℝ≥0,
            if ‖b p.1 - b p.2‖ < r then |g (b p.1)| * |g (b p.2)| else 0
              ∂(ν.prod ν)) ∧
        (∫ p : ℂ × ℂ, if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) ≤ M ^ 2 * (C * r ^ (β * (2-q)/(2+q))) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_singular_weighted_pair_subcritical_le
    x z hq0 hq2 hβ0 hβ2] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro g hg M hM hgM r hr
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hbm : Measurable b := b.continuous.measurable
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
  have hmap : μ.prod μ = Measure.map (Prod.map b b) (ν.prod ν) :=
    Measure.map_prod_map ν ν hbm hbm
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod μ)) ≤
      ENNReal.ofReal (M ^ 2 * (C * r ^ (β * (2-q)/(2+q)))) := by
    rw [hmap, lintegral_map hf.ennreal_ofReal (hbm.prodMap hbm)]
    calc
      _ ≤ (ENNReal.ofReal M * ENNReal.ofReal M) *
          (∫⁻ p : ℝ≥0 × ℝ≥0,
            if ‖b p.1 - b p.2‖ < r then
              (ENNReal.ofReal ‖b p.1-z‖)^(-q) * (ENNReal.ofReal ‖b p.2-z‖)^(-q)
            else 0 ∂(ν.prod ν)) := by
        rw [← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
        apply lintegral_mono
        intro p
        dsimp [f]
        split_ifs with hp
        · rw [ENNReal.ofReal_mul (abs_nonneg _)]
          calc
            _ ≤ (ENNReal.ofReal M * (ENNReal.ofReal ‖b p.1-z‖)^(-q)) *
                (ENNReal.ofReal M * (ENNReal.ofReal ‖b p.2-z‖)^(-q)) :=
              mul_le_mul' (hgM _) (hgM _)
            _ = _ := by ac_rfl
        · simp
      _ ≤ (ENNReal.ofReal M * ENNReal.ofReal M) *
          ENNReal.ofReal (C * r ^ (β * (2-q)/(2+q))) :=
        mul_le_mul' le_rfl (hb r hr)
      _ = _ := by rw [pow_two, ENNReal.ofReal_mul (mul_nonneg hM hM), ENNReal.ofReal_mul hM]
  have hfi : Integrable f (μ.prod μ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (b := ENNReal.ofReal (M ^ 2 * (C * r ^ (β * (2-q)/(2+q))))) ?_ ENNReal.ofReal_lt_top
    exact (le_of_eq (by apply lintegral_congr; intro p; exact Real.enorm_eq_ofReal (hf0 p))).trans hlin
  refine ⟨hfi, ?_, ?_⟩
  · rw [hmap, integral_map (hbm.prodMap hbm).aemeasurable hf.aestronglyMeasurable]
    rfl
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_ofReal (by positivity)] at this
  exact this

end HarmonicBalls
