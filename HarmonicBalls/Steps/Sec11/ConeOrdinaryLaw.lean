import HarmonicBalls.Steps.Sec11.ConeTranslation
import HarmonicBalls.Proofs.GFF.ConeMassLocalRepresentation
import HarmonicBalls.Proofs.Sec6.DyadicMeasureScalingLaw
import HarmonicBalls.Proofs.Sec6.LQGTranslationCovariance

/-! # Translation and dyadic-scale laws for ordinary cone events -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

/-- An ordinary whole-plane LQG cone event has the same probability at every
centre, under affine invariance of the field. -/
theorem cone_event_probability_translate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (Q : Set ℂ) (hQ : IsCone Q) (M r : ℝ) (z : ℂ) :
    P {ω | coneMassEvent (μ ω) Q M r z} = P {ω | coneMassEvent (μ ω) Q M r 0} := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  have hqm : MeasurableSet (annulus (0 : ℂ) r (2 * r) ∩ coneAt Q 0) :=
    (measurableSet_ball.diff measurableSet_closedBall).inter
      ((Homeomorph.addRight 0).measurableEmbedding.measurableSet_image.mpr hQm)
  have hlaw := (Section6.identDistrib_translateMeasure hG hμ hAff z).measure_mem_eq
    (measurableSet_coneMassEvent Q M r 0 hqm)
  have heq : {ω | coneMassEvent (affineMeasure γ hcirc μ 1 z ω) Q M r 0} =
      {ω | coneMassEvent (μ ω) Q M r z} := by
    ext ω
    simp only [mem_ofPred_eq, affineMeasure, norm_one, Real.log_one, mul_zero, add_zero, div_one]
    rw [coneMassEvent_smul_iff _ _ _ _ _
      (by positivity : ENNReal.ofReal (Real.exp (γ * -hcirc ω 1 z)) ≠ 0)
      ENNReal.ofReal_ne_top, coneMassEvent_map_sub_iff _ _ hQ]
  change P {ω | coneMassEvent (μ ω) Q M r 0} =
    P {ω | coneMassEvent (affineMeasure γ hcirc μ 1 z ω) Q M r 0} at hlaw
  rw [heq] at hlaw
  exact hlaw.symm

/-- An ordinary cone event at any inverse-dyadic radius has its unit-scale
probability. -/
theorem cone_event_probability_dyadic
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (Q : Set ℂ) (hQ : IsCone Q) (M : ℝ) (n : ℕ) :
    P {ω | coneMassEvent (μ ω) Q M (dyadicScale n) 0} =
      P {ω | coneMassEvent (μ ω) Q M 1 0} := by
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by dsimp [k]; positivity
  have hkr : k * dyadicScale n = 1 := by
    change (2 : ℝ) ^ n * (2⁻¹ : ℝ) ^ n = 1
    rw [← mul_pow]
    norm_num
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  have hqm : MeasurableSet (annulus (0 : ℂ) (dyadicScale n) (2 * dyadicScale n) ∩ coneAt Q 0) :=
    (measurableSet_ball.diff measurableSet_closedBall).inter
      ((Homeomorph.addRight 0).measurableEmbedding.measurableSet_image.mpr hQm)
  have hlaw := (Section6.identDistrib_normalizedPullback_dyadic hγ hG hμ hAff n).measure_mem_eq
    (measurableSet_coneMassEvent Q M (dyadicScale n) 0 hqm)
  change P {ω | coneMassEvent (μ ω) Q M (dyadicScale n) 0} =
    P {ω | coneMassEvent (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) Q M (dyadicScale n) 0} at hlaw
  have heq : {ω | coneMassEvent (normalizedPullbackMeasure γ 0 k (hcirc ω) (μ ω)) Q M (dyadicScale n) 0} =
      {ω | coneMassEvent (μ ω) Q M 1 0} := by
    ext ω
    simp only [mem_ofPred_eq, normalizedPullbackMeasure]
    rw [coneMassEvent_smul_iff _ _ _ _ _
      (by positivity : ENNReal.ofReal ((Real.exp
        (γ * (lqgQ γ * Real.log k + fieldCircleAverage 0 (hcirc ω) k 0)))⁻¹) ≠ 0)
      ENNReal.ofReal_ne_top,
      coneMassEvent_map_inv_smul_iff _ _ hQ _ _ hk, hkr]
  rw [heq] at hlaw
  exact hlaw

end HarmonicBalls

#print axioms HarmonicBalls.cone_event_probability_translate

#print axioms HarmonicBalls.cone_event_probability_dyadic
