import HarmonicBalls.Proofs.Sec11.AnnulusComparison

/-! # Cone mass and annulus comparison in Lemma 11.5 -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- If the cone is inside `Λ` near its vertex, the cone mass event at level
`2C` and the annulus comparison force the outer annulus to lie in `Λ`. The
Green-potential supremum is required to be positive and finite. -/
theorem annulus_subset_of_coneMassEvent
    (μ : Measure ℂ) (Λ Q : Set ℂ) (z : ℂ) (C r R : ℝ)
    (hC : 0 < C) (hR : 2 * r ≤ R)
    (hcone : coneAt Q z ∩ ball z R ⊆ Λ)
    (hSGpos : 0 < annulusGreenPotentialSup μ z (3 * r) (6 * r))
    (hSGfin : annulusGreenPotentialSup μ z (3 * r) (6 * r) ≠ ⊤)
    (hbound : (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r))
    (hevent : coneMassEvent μ Q (2 * C) r z) :
    annulus z (4 * r) (5 * r) ⊆ Λ := by
  apply annulus_subset_of_large_mass μ Λ (annulus z r (2 * r) ∩ coneAt Q z) z r _
  · intro x hx
    refine ⟨hx.1, hcone ⟨hx.2, ?_⟩⟩
    exact ball_subset_ball hR hx.1.1
  · exact hbound
  · have hcoeff : ENNReal.ofReal C < ENNReal.ofReal (2 * C) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hC.le).2 (by linarith)
    have hmul := ENNReal.mul_lt_mul_right hSGpos.ne' hSGfin hcoeff
    exact lt_of_lt_of_le (by simpa only [mul_comm] using hmul) hevent

end HarmonicBalls
