import Mathlib
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Proposed.LQG

/-!
# Length-metric property of the physical metric `Dα` (Step 8, fp-S11i-11-13f, n3)

`IsEuclideanLengthMetric (Dα ω)` is the hypothesis `hLen` of `ae_fitting_eventually_of_decoders`
(`FirstPass/S11i/Step8Fitting.lean`). It is not part of `SatisfiesLQGMetricAxioms` (`Defs/LQGMetric.lean`): axioms I-IV
are stated for `h^ℂ + f` with `f` continuous, not for the log-singular field `h^ℂ - α₀ log|·|`. So it is obtained from
the Proposed input `LQGMetricFieldAxioms` (`Proposed/LQG.lean`), item I (Fact 2.2 I for the field of the paper,
Gwynne-Miller 2021, Theorem 1.2 and Remark 1.5; Dubédat-Falconet-Gwynne-Pfeffer-Sun 2020, Theorem 1.10).
That input is pending operator source-check and is used here only as an explicit hypothesis.
-/

namespace HarmonicBalls.FirstPassS11iStep8LengthMetric

open MeasureTheory

/-- **Fact 2.2 I for the physical metric.** Let `D` be the physical metric `D_α` of the field
`h^ℂ - α₀ log|·|` (`IsLQGMetricOfField`), with `hC` the pairings of a whole-plane GFF. Under the Proposed input
`LQGMetricFieldAxioms` (item I), almost surely `D_α` is a Euclidean length metric. -/
theorem ae_isEuclideanLengthMetric_of_fieldAxioms {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hFact : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, hL, hDa⟩ := hD
  filter_upwards [(hFact hGFF hγ0 hγ2 hα 𝔇 hL).1, hDa] with ω hI hDω
  have hfun : (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal) = D ω := by
    funext u v
    rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
  have hlen := hI.2
  rw [hfun] at hlen
  exact hlen

end HarmonicBalls.FirstPassS11iStep8LengthMetric

#print axioms HarmonicBalls.FirstPassS11iStep8LengthMetric.ae_isEuclideanLengthMetric_of_fieldAxioms
