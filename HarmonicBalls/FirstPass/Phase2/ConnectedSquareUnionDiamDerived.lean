import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Finite internal diameters of connected unions of rectangles for the singular LQG metric

For a γ-LQG metric `𝔇` (`IsLQGMetric`), the metric of `h - α₀ log |·|` is `D_h = e^{-ξ α₀ log |·|} · 𝔇(h)`
(`IsLQGMetricOfField`). This file collects the deterministic and almost sure facts about `D_h` that reduce the finite
internal diameter of a compact connected finite union of closed rectangles to the finite internal diameter of a single
closed square.

* `ae_isEuclideanLengthMetric_of_isLQGMetricOfField`: under the field axioms of the LQG metric
  (`LQGMetricFieldAxiomsUnivFrozen`, axiom I), almost surely `D_h` is a Euclidean length metric.
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Filter

open scoped ENNReal

/-- The singular LQG metric is almost surely a Euclidean length metric. If `D` is the LQG metric of
`h^ℂ - α₀ log |·|` for a whole-plane GFF `h^ℂ` (`IsLQGMetricOfField`), then under the field axioms
(`LQGMetricFieldAxiomsUnivFrozen`), almost surely `D ω` is a Euclidean length metric. Route: almost surely
`D ω = (e^{-ξ α₀ log |·|} · 𝔇(h^ℂ)).toReal` (the defining identity of `IsLQGMetricOfField`, with `D ω ≥ 0`), and the
right side is a Euclidean length metric by axiom I. -/
theorem ae_isEuclideanLengthMetric_of_isLQGMetricOfField (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    {γ ξ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {D : Ω → ℂ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (hD : IsLQGMetricOfField P γ ξ α₀ hC D) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) := by
  obtain ⟨𝔇, h𝔇, hDeq⟩ := hD
  have hAxω := hAx Ω P γ ξ α₀ hC hcirc hW hγ0 hγ2 hα 𝔇 h𝔇
  filter_upwards [hAxω.1, hDeq] with ω hI hω
  have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hω u v).2, ENNReal.toReal_ofReal (hω u v).1]
  rw [hfun]
  exact hI.2

end HarmonicBalls
