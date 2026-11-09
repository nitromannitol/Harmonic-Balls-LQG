import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.Proposed.LQG

/-!
# Proposition 11.10, the Euclidean length property of the shifted metric (fp-S11c, owner n1)

FIRST-PASS NEW (bookkeeping, using the operator ruling of 21:25 UTC). The shift of the Cameron-Martin step is the Weyl
scaling `weylScaling (D ω) ξ f` of the LQG metric `D ω` by a continuous compactly supported `f`. Its Euclidean length
property `hEl` of `Shifted.shifted_sup_le_of_good` is the frozen Prop `LQGMetricContinuousShiftFactI`
(`FirstPass/Frozen/S11d.lean`, owner n3), applied to the weight `f - α₀ log|·|`. The identification uses item III (Weyl
scaling) of the field-level axioms `LQGMetricFieldAxioms` (`Proposed/LQG.lean`) and the representation of `D` in
`IsLQGMetricOfField`. No new frozen Prop is introduced.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The shifted metric `weylScaling (D ω) ξ f` of a continuous `f` is almost surely a Euclidean length metric. -/
theorem ae_isEuclideanLengthMetric_weylShift {γ ξ α₀ : ℝ} (hFactI : LQGMetricContinuousShiftFactI.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hD : IsLQGMetricOfField P γ ξ α₀ hC D) {f : ℂ → ℝ} (hf : Continuous f) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun u v => (weylScaling (D ω) ξ f u v).toReal) := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hI := hFactI γ ξ α₀ Ω P hC hcirc hgff hγ hγ₂ hα 𝔇 h𝔇 f hf
  have hIII := (haxioms hgff hγ hγ₂ hα 𝔇 h𝔇).2.2.1
  filter_upwards [hI, hIII, hrepr] with ω hωI hωIII hωrep
  have hDfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    rw [← (hωrep u v).2, ENNReal.toReal_ofReal (hωrep u v).1]
  have hE : (fun u v => (weylScaling (D ω) ξ f u v).toReal) =
      fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => f x - α₀ * Real.log ‖x‖) u v).toReal := by
    funext u v
    have key := hωIII f hf u v
    rw [hDfun]
    exact congrArg ENNReal.toReal key.symm
  rw [hE]
  exact hωI.2

end HarmonicBalls
