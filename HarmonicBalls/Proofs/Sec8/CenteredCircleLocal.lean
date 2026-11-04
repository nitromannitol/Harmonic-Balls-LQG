import HarmonicBalls.Proofs.Sec8.CircleDensityDifferenceCovariance
import HarmonicBalls.Proofs.Sec8.CircleDensityDoubleLog

/-! # Local centered circle averages

The covariance of the signed annular approximation converges to the
covariance of the centered circle average. The imported Section 8 argument
uses Leonardo Bonanno's LatticeProb formalization of the ergodic theorem.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter Real
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- The self-covariance of the signed annular approximation converges to that
of the corresponding difference of circle averages. -/
theorem IsWholePlaneGFF.circleDensityDifference_self_covariance_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {r η : ℝ}
    (hr : 0 < r) (hη : 0 < η) (z : ℂ) :
    Tendsto (fun n => wholePlaneGFFCov
      (.pairing (circleDensityDifference r η hr hη z n))
      (.pairing (circleDensityDifference r η hr hη z n))) atTop
      (𝓝 (wholePlaneGFFCov (.circle r z) (.circle r z) +
        wholePlaneGFFCov (.circle r 0) (.circle r 0) -
        2 * wholePlaneGFFCov (.circle r z) (.circle r 0))) := by
  have hsym : wholePlaneGFFCov (.circle r 0) (.circle r z) =
      wholePlaneGFFCov (.circle r z) (.circle r 0) := by
    have h₁ := hGFF.covariance_eq (.circle r 0) (.circle r z) hr hr
    have h₂ := hGFF.covariance_eq (.circle r z) (.circle r 0) hr hr
    simp only [GFFObservable.eval] at h₁ h₂
    rw [← h₁, ← h₂, covariance_comm]
  have hlim := (((circleDensity_pairing_covariance_tendsto hr hη z z).sub
    (circleDensity_pairing_covariance_tendsto hr hη 0 z)).sub
    (circleDensity_pairing_covariance_tendsto hr hη z 0)).add
    (circleDensity_pairing_covariance_tendsto hr hη 0 0)
  have heq : wholePlaneGFFCov (.circle r z) (.circle r z) -
      wholePlaneGFFCov (.circle r z) (.circle r 0) -
      wholePlaneGFFCov (.circle r 0) (.circle r z) +
      wholePlaneGFFCov (.circle r 0) (.circle r 0) =
      wholePlaneGFFCov (.circle r z) (.circle r z) +
      wholePlaneGFFCov (.circle r 0) (.circle r 0) -
      2 * wholePlaneGFFCov (.circle r z) (.circle r 0) := by
    rw [hsym]
    ring
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards with n
  let δ := circleDensityWidth r η n
  let hδ := circleDensityWidth_pos hr hη n
  let g (v : ℂ) : ℂ → ℝ := fun x => (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ v x
  have hg (v : ℂ) : Continuous (g v) :=
    continuous_const.mul (circleDensity_contDiff r δ hδ v).continuous
  have hgc (v : ℂ) : HasCompactSupport (g v) :=
    (circleDensity_hasCompactSupport hr.le hδ v).mul_left
  have hgm (v : ℂ) : ∫ x, g v x = 1 := circleDensity_normalized_integral hr.le hδ v
  exact (wholePlaneGFFCov_pairing_sub_self (hg z) (hgc z) (hgm z)
    (hg 0) (hgc 0) (hgm 0)).symm

/-- Centered circle averages have jointly measurable local versions in the
field sigma algebra modulo additive constants. -/
theorem IsWholePlaneGFF.exists_joint_centered_circle_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hr : 0 < r) :
    ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) r z -
          fieldCircleAverage α₀ (hcirc ω) r 0 := by
  apply hGFF.exists_joint_centered_circle_version_of_circleDensity_limit hr
  intro z _ η hη
  exact hGFF.circleDensityDifference_error_tendsto_of_self hr hη z
    (hGFF.circleDensityDifference_self_covariance_tendsto hr hη z)

end HarmonicBalls
