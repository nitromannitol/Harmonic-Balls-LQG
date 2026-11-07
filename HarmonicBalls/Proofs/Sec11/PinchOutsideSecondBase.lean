import HarmonicBalls.Proofs.Sec11.PinchOutsideBaseMetric
import HarmonicBalls.Proofs.Sec11.PinchOutsideAnnulusMass

/-! # Conditional second pinch for the base metric

The outside metric separation and Green threshold are supplied by their
outside-field representatives. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- Conditional second-pinch positivity for a whole-plane GFF base metric. -/
theorem IsCorrectedPinchConfiguration.positive_second_base_of_outside_green_annulus
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6))
    (hm : MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance ≤ m₀) (A : Set Ω) (M : ℝ)
    (hA : MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance] A) (hAp : 0 < P A)
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance]) ω) :
    0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  obtain ⟨a, ha, hae⟩ := h.exists_outside_baseMetric_sphere_distance hgff 𝔇 h𝔇
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    have hh := ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (fun _ => continuous_const) (fun _ => measurable_const)
    exact hh.mono fun _ hh => hh.1
  exact h.positive_second_of_outside_green_annulus hgff hμ hfront hfinite hpositive hm A
    (fun ω => 𝔇 (hC ω)) h.δ₀_mem.1 M a hA hAp ha hae hmetric hgreen hinside

#print axioms IsCorrectedPinchConfiguration.positive_second_base_of_outside_green_annulus
end HarmonicBalls
