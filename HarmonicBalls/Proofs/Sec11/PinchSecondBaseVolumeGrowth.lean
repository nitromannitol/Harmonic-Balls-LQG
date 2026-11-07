import HarmonicBalls.Proofs.Sec11.PinchOutsideSecondBase
import HarmonicBalls.Steps.Sec11.PinchGreenFinite
import HarmonicBalls.Proofs.Sec6.LocalizedSingularRootNormalization
import HarmonicBalls.Proofs.Sec6.TranslatedCircleNull

/-! # Second pinch under LQG volume growth

The imported Section 6 annulus-mass theorem uses the iteration formalized by
Leonardo Bonanno in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- Volume growth and whole-plane affine invariance supply the annular
regularity hypotheses in the conditional second-pinch assembly. -/
theorem IsCorrectedPinchConfiguration.positive_second_base_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hm : MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance ≤ m₀) (A : Set Ω) (M : ℝ)
    (hA : MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance] A) (hAp : 0 < P A)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance]) ω) :
    0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hmass := Section6.ae_singular_lqg_middle_annulus_pos_finite
    hgrowth hγ hγ2 hQ hgff hμ (0 : ℂ) (ρ := 6) (by norm_num)
  have hmass' : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6) ∧
      μ ω (annulus 0 3 6) ≠ ∞ := by
    simpa only [show (6 : ℝ) / 2 = 3 by norm_num] using hmass
  have hfront := Section6.ae_lqg_annulus_frontier_eq_zero_of_translation
    hgff hμ hAff (0 : ℂ) 3 6
  have hgreen := ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth
    hgrowth hγ hγ2 hQ hgff hμ 3 (b := 6) (by norm_num)
  exact h.positive_second_base_of_outside_green_annulus hgff hμ 𝔇 h𝔇 hfront
    (hmass'.mono fun _ hh => hh.2) (hmass'.mono fun _ hh => hh.1) hm A M hA hAp hgreen hinside

#print axioms IsCorrectedPinchConfiguration.positive_second_base_of_volumeGrowth
end HarmonicBalls
