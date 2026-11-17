import HarmonicBalls.Proofs.Potential.BrownianSingularPairAllRadius
import HarmonicBalls.Proofs.Potential.BrownianOccupationWeightedMeasure

/-! # Singularly weighted Brownian occupation pairs

Singularly dominated spatial weights inherit an integrable pair bound.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- An all-radius pair bound holds simultaneously for singularly dominated weights. -/
theorem planarBrownianMotion_ae_unit_singular_weighted_occupation_le
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd0 : 0 < d)
    (hd : d < β * (1 - q/q₂)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g →
      (∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q)) →
      ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun t => b t) ν
      Integrable (fun p : ℂ × ℂ =>
        if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
      (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0 ∂(μ.prod μ)) ≤
        unitSingularPairAllRadiusEnvelope z q d b * r ^ d := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_singular_pair_all_radius_le
    x z hq hqq hq₂ hβ hβ₂ hd0 hd] with b hb
  intro g hg hgq r hr
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hbm : Measurable b := b.continuous.measurable
  let f : ℂ × ℂ → ℝ := fun p =>
    if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0
  have hs : MeasurableSet {p : ℂ × ℂ | ‖p.1-p.2‖ < r} :=
    measurableSet_lt ((measurable_fst.sub measurable_snd).norm) measurable_const
  have hf : Measurable f :=
    ((hg.comp measurable_fst).abs.mul (hg.comp measurable_snd).abs).ite hs measurable_const
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs <;> positivity
  have hmap : μ.prod μ = Measure.map (Prod.map b b) (ν.prod ν) :=
    Measure.map_prod_map ν ν hbm hbm
  have hE : 0 ≤ unitSingularPairAllRadiusEnvelope z q d b := by
    dsimp [unitSingularPairAllRadiusEnvelope, unitSingularPairDyadicEnvelopeReal,
      unitSingularPairOccupationReal]
    positivity
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod μ)) ≤
      ENNReal.ofReal (unitSingularPairAllRadiusEnvelope z q d b * r ^ d) := by
    rw [hmap, lintegral_map hf.ennreal_ofReal (hbm.prodMap hbm)]
    calc
      _ ≤ unitSingularPairNear z q r b := by
        unfold unitSingularPairNear
        apply lintegral_mono
        intro p
        dsimp [f]
        split_ifs
        · rw [ENNReal.ofReal_mul (abs_nonneg _)]
          exact mul_le_mul' (hgq _) (hgq _)
        · simp
      _ ≤ ENNReal.ofReal (unitSingularPairAllRadiusEnvelope z q d b) *
          ENNReal.ofReal (r ^ d) := hb r hr
      _ = _ := (ENNReal.ofReal_mul hE).symm
  have hfi : Integrable f (μ.prod μ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ p, ‖f p‖ₑ ∂(μ.prod μ)) =
        (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod μ)) := by
      apply lintegral_congr
      intro p
      rw [Real.enorm_of_nonneg (hf0 p)]
    rw [heq]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  refine ⟨hfi, ?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_ofReal (by positivity)] at h
  exact h

/-- The singular pair bound also holds for every submeasure of the occupation measure. -/
theorem planarBrownianMotion_ae_unit_singular_weighted_submeasure_le
    (x z : ℂ) {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd0 : 0 < d)
    (hd : d < β * (1 - q/q₂)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g →
      (∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q)) →
      ∀ (μ : Measure ℂ), μ ≤ Measure.map (fun t => b t) ν → ∀ r : ℝ, 0 < r →
      Integrable (fun p : ℂ × ℂ =>
        if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
      (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0 ∂(μ.prod μ)) ≤
        unitSingularPairAllRadiusEnvelope z q d b * r ^ d := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_singular_weighted_occupation_le
    x z hq hqq hq₂ hβ hβ₂ hd0 hd] with b hb
  intro g hg hgq μ hμ r hr
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  obtain ⟨hint, hbound⟩ := hb g hg hgq r hr
  refine ⟨hint.mono_measure (Measure.prod_mono hμ hμ), ?_⟩
  refine (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hint).trans hbound
  filter_upwards with p
  split_ifs <;> positivity

end HarmonicBalls
