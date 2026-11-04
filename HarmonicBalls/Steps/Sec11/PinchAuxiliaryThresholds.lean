import HarmonicBalls.Steps.Sec11.PinchDistancePositivity
import HarmonicBalls.Steps.Sec11.PinchThresholdSelection

/-! # Thresholds for the second auxiliary pinch event

The metric separation is derived from the length-metric property. Finiteness
of the annular Green potential remains an explicit almost-sure hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- On any positive-mass event, the distance between the two small spheres is
uniformly positive and the annular Green-potential term is uniformly finite
on a positive-mass subevent, provided the metric and finiteness properties hold
almost surely. -/
theorem exists_positive_measure_pinch_auxiliary_thresholds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set Ω)
    (D : Ω → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ) {δ M : ℝ} (hδ : 0 < δ)
    (hA : 0 < P A) (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞) :
    ∃ n m : ℕ, 0 < n ∧ 0 < P {ω | ω ∈ A ∧
      (n : ℝ≥0∞)⁻¹ < ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))) ∧
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 < (m : ℝ≥0∞)} := by
  let G : Set Ω := {ω | IsEuclideanLengthMetric (D ω) ∧
    annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞}
  have hG : ∀ᵐ ω ∂P, ω ∈ G := hmetric.and hgreen
  have heq : A =ᵐ[P] A ∩ G := by
    filter_upwards [hG] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  have hAG : 0 < P (A ∩ G) := by rwa [← measure_congr heq]
  let f : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)))
  let g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6
  have hfg : ∀ ω ∈ A ∩ G, f ω ≠ 0 ∧ g ω ≠ ∞ := by
    intro ω hω
    have hpos := (hω.2.1.pinch_sphere_distances_pos hδ).1
    exact ⟨(ENNReal.ofReal_pos.mpr hpos).ne', ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω.2.2⟩
  obtain ⟨n, m, hn, hp⟩ := exists_positive_measure_uniform_thresholds P (A ∩ G) f g hAG hfg
  refine ⟨n, m, hn, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  exact ⟨hω.1.1, hω.2.1, hω.2.2⟩

end HarmonicBalls
