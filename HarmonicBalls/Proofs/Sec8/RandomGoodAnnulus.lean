import HarmonicBalls.Proofs.Sec8.CountableCompactObstacles
import HarmonicBalls.Proofs.Sec8.PointPolarityApproximation

/-! # Measurable good-annulus representatives for random measures

The Borel representative on finite atomless measures transfers to an almost
surely measurable random measure. Point avoidance is an explicit hypothesis.
-/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

open MarkovProcess in
/-- A random finite atomless measure has a measurable good-annulus event up to
null sets, provided the mass threshold is positive and the Brownian point
avoidance condition holds. -/
theorem exists_measurable_random_isGoodAnnulus_of_ae_point_avoidance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hthreshold : ∀ᵐ ω ∂P,
      0 < ENNReal.ofReal a * μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) r z a b) := by
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_on_atomless
    r hr z a b (annulus_smallBallHitting_of_ae_point_avoidance r hr z hpolar)
  refine ⟨(hμ.mk μ) ⁻¹' G, hμ.measurable_mk hG, ?_⟩
  filter_upwards [hμ.ae_eq_mk, hatom, hfinite, hthreshold] with ω heq ha hf ht
  change (hμ.mk μ) ω ∈ G ↔ _
  rw [← heq]
  exact hrep (μ ω) ⟨ha⟩ hf ht

end HarmonicBalls
