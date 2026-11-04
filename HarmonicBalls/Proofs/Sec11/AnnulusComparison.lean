import HarmonicBalls.Draft.Section11

/-!
# The large-mass consequence of the annulus comparison

The contrapositive of Lemma 11.6 is used in the proof of Proposition 11.11
(paper, lines 3229–3232).  This file proves the deterministic measure-theoretic
part of that implication, retaining the strict inequality of the pinch event.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- If every point of the outer annulus outside `Λ` implies an upper mass
bound, then a strict lower bound on a subset of the inner annulus inside `Λ`
forces the entire outer annulus to lie in `Λ`. -/
theorem annulus_subset_of_large_mass
    (μ : Measure ℂ) (Λ U : Set ℂ) (z : ℂ) (r : ℝ) (a : ℝ≥0∞)
    (hU : U ⊆ annulus z r (2 * r) ∩ Λ)
    (hbound : (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤ a)
    (hlarge : a < μ U) :
    annulus z (4 * r) (5 * r) ⊆ Λ := by
  intro x hx
  by_contra hxΛ
  have hle : μ U ≤ μ (annulus z r (2 * r) ∩ Λ) := measure_mono hU
  exact (not_lt_of_ge (le_trans hle (hbound ⟨x, hx, hxΛ⟩))) hlarge

/-- The mass part of the pinch event, together with Lemma 11.6's annulus
bound, gives the inclusion used in Proposition 11.11. -/
theorem annulus_subset_of_pinchPointEvent
    (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U T Q' Q Λ : Set ℂ)
    (C r : ℝ) (z : ℂ)
    (hU : rescaledSet U r z ⊆ annulus z r (2 * r) ∩ Λ)
    (hbound : (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty →
      μ (annulus z r (2 * r) ∩ Λ) ≤
        ENNReal.ofReal C * annulusGreenPotentialSup μ z (3 * r) (6 * r))
    (hpinch : pinchPointEvent μ D U T Q' Q C r z) :
    annulus z (4 * r) (5 * r) ⊆ Λ :=
  annulus_subset_of_large_mass μ Λ (rescaledSet U r z) z r _ hU hbound hpinch.2.2

end HarmonicBalls
