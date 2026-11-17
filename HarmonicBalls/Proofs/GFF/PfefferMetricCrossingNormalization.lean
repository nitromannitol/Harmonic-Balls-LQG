import HarmonicBalls.Proofs.GFF.PfefferAroundRepresentation
import HarmonicBalls.Proofs.GFF.PfefferCrossingMeasurable
import HarmonicBalls.Proofs.GFF.PfefferSourceDistanceMeasurable

/-! # Measurability of normalized LQG crossings

For a whole-plane GFF plus a random continuous shift with measurable point
values, the normalized distances across and around a fixed annulus are almost
everywhere measurable for an LQG metric.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- The normalized across and around distances of a shifted LQG metric are
almost everywhere measurable at every fixed positive normalization scale. -/
theorem IsLQGMetric.aemeasurable_normalized_pfefferCrossings
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable (fun ω => f ω z))
    (c : ℝ → ℝ) (z : ℂ) (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => pfefferNormalization ξ hcirc f c r ω *
      pfefferAcross (𝔇 (pfefferField hC f ω)) z a b) P ∧
    AEMeasurable (fun ω => pfefferNormalization ξ hcirc f c r ω *
      pfefferAround (𝔇 (pfefferField hC f ω)) z a b) P := by
  have hpoint : ∀ x y, Measurable fun ω => 𝔇 (pfefferField hC f ω) x y :=
    fun x y => hgff.measurable_pfefferField_distance hfcont hfmeas h𝔇.measurable_apply x y
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (pfefferField hC f ω)) :=
    (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc f hgff hfcont hfmeas).ae_isEuclideanLengthMetric
  have hn := hgff.aemeasurable_pfefferNormalization_continuous_shift ξ f hfcont hfmeas c hr
  exact ⟨hn.mul (aemeasurable_pfefferAcross_of_ae_euclideanLengthMetric z a b hmetric
      (fun x y => (hpoint x y).aemeasurable)),
    hn.mul (hgff.aemeasurable_pfefferAround_of_ae_euclideanLengthMetric z a b hpoint hmetric)⟩

/-- The scaled annular observables appearing in the normalization are almost
everywhere measurable for each positive scale. -/
theorem IsLQGMetric.aemeasurable_scaled_normalized_pfefferCrossings
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {f : Ω → ℂ → ℝ}
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable (fun ω => f ω z))
    (c : ℝ → ℝ) (z : ℂ) (a b : ℝ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω => pfefferNormalization ξ hcirc f c r ω *
      pfefferAcross (𝔇 (pfefferField hC f ω)) ((r : ℂ) * z) (r * a) (r * b)) P ∧
    AEMeasurable (fun ω => pfefferNormalization ξ hcirc f c r ω *
      pfefferAround (𝔇 (pfefferField hC f ω)) ((r : ℂ) * z) (r * a) (r * b)) P :=
  h𝔇.aemeasurable_normalized_pfefferCrossings hgff hfcont hfmeas c _ _ _ hr

end HarmonicBalls
