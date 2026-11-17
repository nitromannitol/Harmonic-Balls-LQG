import HarmonicBalls.Proposed.PfefferMetricScaling
import HarmonicBalls.Steps.Sec11.PathLengthMeasurable

/-! # Measurability of countable families of separating loops

Lengths of countable families of closed paths give an almost-everywhere
measurable upper bound for the distance around an annulus.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- The infimum of the lengths of a countable family of fixed closed paths is
almost-everywhere measurable. -/
theorem aemeasurable_iInf_pathLength_of_ae_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (z : ℕ → ℂ) (p : ∀ n, Path (z n) (z n)) :
    AEMeasurable (fun ω => ⨅ n, pathLength (D ω) (p n)) P := by
  exact AEMeasurable.iInf fun n =>
    aemeasurable_pathLength_of_ae_lengthMetric hD hmetric (p n)

/-- The infimum over a family of separating loops bounds the unrestricted
around distance. -/
theorem pfefferAround_le_iInf_pathLength
    (D : ℂ → ℂ → ℝ) (center : ℂ) (a b : ℝ)
    (z : ℕ → ℂ) (p : ∀ n, Path (z n) (z n))
    (hsep : ∀ n, PfefferSeparates (p n) center a b) :
    pfefferAround D center a b ≤ ⨅ n, pathLength D (p n) := by
  refine le_iInf fun n => ?_
  exact iInf_le_of_le (z n) (iInf_le_of_le (p n) (iInf_le _ (hsep n)))

/-- A countable representation of the unrestricted around distance transfers
almost-everywhere measurability from the lengths of its fixed loops. -/
theorem aemeasurable_pfefferAround_of_countable_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (center : ℂ) (a b : ℝ)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (z : ℕ → ℂ) (p : ∀ n, Path (z n) (z n))
    (hrep : ∀ᵐ ω ∂P,
      pfefferAround (D ω) center a b = ⨅ n, pathLength (D ω) (p n)) :
    AEMeasurable (fun ω => pfefferAround (D ω) center a b) P := by
  exact (aemeasurable_iInf_pathLength_of_ae_lengthMetric hD hmetric z p).congr
    (hrep.mono fun _ h => h.symm)

end HarmonicBalls
