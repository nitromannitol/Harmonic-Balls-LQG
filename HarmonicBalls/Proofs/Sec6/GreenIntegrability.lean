import HarmonicBalls.Proofs.Sec6.GreenMono
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole

/-!
# Integrability of Green kernels on subdomains

Domain monotonicity and measurability transfer Green-kernel integrability from a bounded
ambient domain to an open subdomain, including points outside the subdomain and the
convention that the diagonal has value zero. This is useful for annuli inside balls.
-/

namespace HarmonicBalls.Section6

open MeasureTheory

/-- Domain monotonicity for Green functions holds for all pairs, including the diagonal
and points outside the smaller domain. -/
theorem greenFunction_le_of_subset {O O' : Set ℂ} (hsub : O ⊆ O')
    (hbounded : Bornology.IsBounded O') (x y : ℂ) :
    greenFunction O x y ≤ greenFunction O' x y := by
  by_cases hx : x ∈ O
  · by_cases hy : y ∈ O
    · by_cases hxy : x = y
      · subst y
        simp only [greenFunction_self, le_refl]
      · exact greenFunction_mono hsub hbounded hx hy hxy
    · rw [greenFunction_of_notMem_right hy]
      exact greenFunction_nonneg hbounded x y
  · rw [greenFunction_of_notMem_left hx]
    exact greenFunction_nonneg hbounded x y

/-- Integrability of a Green kernel on a bounded ambient domain implies integrability
on each open subdomain. -/
theorem integrable_greenFunction_of_subset {O O' : Set ℂ} (hopen : IsOpen O)
    (hsub : O ⊆ O') (hbounded : Bornology.IsBounded O') (μ : Measure ℂ) (x : ℂ)
    (hint : Integrable (greenFunction O' x) μ) :
    Integrable (greenFunction O x) μ := by
  have hO : Bornology.IsBounded O := hbounded.subset hsub
  refine hint.mono_nonneg (measurable_greenFunction hopen x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => greenFunction_nonneg hO x y) ?_
  exact Filter.Eventually.of_forall (greenFunction_le_of_subset hsub hbounded x)

end HarmonicBalls.Section6
