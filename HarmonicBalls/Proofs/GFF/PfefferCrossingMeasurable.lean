import HarmonicBalls.Proofs.Metric.CompactDistanceMeasurable

/-! # Measurability of annular crossing distances

For a random Euclidean-compatible length metric, annular across distances
are almost-everywhere measurable when the point evaluations are.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Across distances at arbitrary fixed radii are almost-everywhere measurable
for an almost surely Euclidean-compatible length metric with almost-everywhere
measurable point evaluations. -/
theorem aemeasurable_pfefferAcross_of_ae_euclideanLengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Ω → ℂ → ℂ → ℝ} (z : ℂ) (a b : ℝ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P) :
    AEMeasurable (fun ω => pfefferAcross (D ω) z a b) P := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · obtain ⟨u, hu⟩ := exists_dense_seq_of_nonempty (sphere z a)
        (NormedSpace.sphere_nonempty.mpr ha)
      obtain ⟨v, hv⟩ := exists_dense_seq_of_nonempty (sphere z b)
        (NormedSpace.sphere_nonempty.mpr hb)
      exact aemeasurable_pfefferAcross_of_dense_seq z ha hb u v hu hv hD
        (fun n m => hpoint _ _)
    · have hs : sphere z b = ∅ := sphere_eq_empty_of_neg (lt_of_not_ge hb)
      simp [pfefferAcross, hs]
  · have hs : sphere z a = ∅ := sphere_eq_empty_of_neg (lt_of_not_ge ha)
    simp [pfefferAcross, hs]

end HarmonicBalls
