import HarmonicBalls.Proofs.Sec11.PinchGreenRatioRepresentatives
import HarmonicBalls.Proofs.Sec6.AnnularNormalizedRestriction

/-! # Annular locality of the pinch Green threshold

The annular normalized-restriction construction uses Leonardo Bonanno's
LatticeProb formalization of the ergodic theorem.
-/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- The normalized restriction to the Green annulus has an outside-field
measurable version for a zero-insertion LQG measure. -/
theorem IsCorrectedPinchConfiguration.exists_outside_normalized_green_annulus
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6)) :
    ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (annulus 0 3 6) := by
  obtain ⟨ν, hν, hνeq⟩ := Section6.IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction
    hgff hμ 0 (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) < 6)
    hfront hfinite hpositive
  refine ⟨ν, ?_, hνeq⟩
  rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
  exact hν.mono (fieldSigmaAlgebraModConst_mono 0 hC h.green_annulus_subset_outside) le_rfl

/-- Once the absolute mass of the Green annulus has an outside version, its
Green-potential threshold has one too. -/
theorem IsCorrectedPinchConfiguration.exists_outside_green_of_annulus_mass
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6))
    (M : ℝ) (c : Ω → ℝ≥0∞)
    (hc : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ c)
    (hce : c =ᵐ[P] fun ω => μ ω (annulus 0 3 6)) :
    ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ b ∧
      b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  obtain ⟨ν, hν, hνe⟩ := h.exists_outside_normalized_green_annulus hgff hμ hfront hfinite hpositive
  refine ⟨fun ω => ENNReal.ofReal M * (c ω * annulusGreenPotentialSup (ν ω) 0 3 6), ?_, ?_⟩
  · exact measurable_const.mul (hc.mul ((measurable_annulusGreenPotentialSup 0 3 6).comp hν))
  · filter_upwards [hνe, hce, hpositive, hfinite] with ω hνeq hceq hp hf
    rw [hνeq, hceq, (normalizedRestriction_mass_green (μ ω) (annulus 0 3 6)
      (annulus 0 3 6) (isOpen_ball.sdiff isClosed_closedBall).measurableSet
      (subset_refl _) 0 3 6 (subset_refl _)).2]
    simp only [← mul_assoc ((μ ω) (annulus 0 3 6)),
      ENNReal.mul_inv_cancel hp.ne' hf, one_mul]

#print axioms IsCorrectedPinchConfiguration.exists_outside_normalized_green_annulus
#print axioms IsCorrectedPinchConfiguration.exists_outside_green_of_annulus_mass
end HarmonicBalls
