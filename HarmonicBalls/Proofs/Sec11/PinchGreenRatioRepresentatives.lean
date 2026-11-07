import HarmonicBalls.Proofs.Sec11.CorrectedPinchOutsideGreenRepresentative
import HarmonicBalls.Proofs.Sec8.AEPiSystemRatioRepresentatives

/-! # Green-potential representatives from local mass ratios -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- A local representative of the annulus mass and countably many normalized
mass ratios determine a local version of the Green threshold. -/
theorem exists_pinchGreen_representative_of_ae_mass_ratios
    {Ω : Type*} [m₀ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (M : ℝ)
    (hpositive : ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ 0 ∧ μ ω (annulus 0 3 6) ≠ ∞)
    (c : Ω → ℝ≥0∞) (hc : @Measurable Ω ℝ≥0∞ m _ c)
    (hce : c =ᵐ[P] fun ω => μ ω (annulus 0 3 6))
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (hversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ m _ Y ∧
      (fun ω => μ ω (V ∩ annulus 0 3 6) / μ ω (annulus 0 3 6)) =ᵐ[P] Y) :
    ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ m _ b ∧
      b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  obtain ⟨ν, hν, hνe⟩ := @exists_normalizedRestriction_version_of_ae_piSystem_ratios
    Ω m₀ P _ m hm μ hμ (annulus 0 3 6) (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    hpositive S hcount hgen hpi hsets hversion
  refine ⟨fun ω => ENNReal.ofReal M * (c ω * annulusGreenPotentialSup (ν ω) 0 3 6), ?_, ?_⟩
  · exact measurable_const.mul (hc.mul ((measurable_annulusGreenPotentialSup 0 3 6).comp hν))
  · filter_upwards [hνe, hce, hpositive] with ω hνeq hceq hp
    rw [hνeq, hceq, (normalizedRestriction_mass_green (μ ω) (annulus 0 3 6)
      (annulus 0 3 6) (isOpen_ball.sdiff isClosed_closedBall).measurableSet
      (subset_refl _) 0 3 6 (subset_refl _)).2]
    simp only [← mul_assoc ((μ ω) (annulus 0 3 6)),
      ENNReal.mul_inv_cancel hp.1 hp.2, one_mul]

#print axioms exists_pinchGreen_representative_of_ae_mass_ratios
end HarmonicBalls
