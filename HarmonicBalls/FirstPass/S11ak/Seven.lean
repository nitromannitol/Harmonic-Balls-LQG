import HarmonicBalls.FirstPass.S11ac
import HarmonicBalls.FirstPass.S11ak.Dilation

/-! # The punctured-ball metric decoder on the ball of radius 7

Corollary of `S11ac.metricDecoder_punctured_ball` with `R = 7`. Its local metric replacement hypothesis `hLoc` on the disks
of `ball 0 7` is discharged by the dilation `S11ak.localMetricReplacement_dilate` (`Dilation.lean`) from the
`LocalMetricReplacementStmt` (FirstPass/S11r/LocalMetricReplacement.lean), which is stated on the disks of `ball 0 1`.
Same shape as `S11ac/Unit.lean` (the unit ball).
-/

namespace HarmonicBalls.S11ak

universe u

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Punctured-ball metric decoder, ball of radius 7.** The statement of `S11ac.metricDecoder_punctured_ball` with `R = 7`,
the local metric replacement being the dilation of `LocalMetricReplacementStmt`. -/
theorem metricDecoder_punctured_ball_seven (hAx : HarmonicBalls.LQGMetricFieldAxiomsUnivFrozen.{u}) (γ ξ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    (hN2 : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂) :
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ∃ Ψ : ModConstTestPairings (ball (0 : ℂ) 7) → ℂ × ℂ → ℝ, (∀ p : ℂ × ℂ, Measurable fun ℓ => Ψ ℓ p) ∧
        ∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p ∈ (ball (0 : ℂ) 7 \ {0}) ×ˢ (ball (0 : ℂ) 7 \ {0}),
            ENNReal.ofReal (Ψ (localModConstField α₀ hC (ball (0 : ℂ) 7) ω) p) =
              ENNReal.ofReal b * internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun z => -α₀ * Real.log ‖z‖) u v).toReal) (ball (0 : ℂ) 7 \ {0}) p.1 p.2 :=
  HarmonicBalls.S11ac.metricDecoder_punctured_ball hAx γ ξ hγ hγ2 hξ 7 (by norm_num)
    (fun 𝔇 h𝔇 c₁ c₂ r₁ r₂ h1 h2 h3 h4 h5 =>
      localMetricReplacement_dilate (R := 7) hγ hγ2 (by norm_num) hN2 𝔇 h𝔇 c₁ c₂ r₁ r₂ h1 h2 h3 h4 h5)

end HarmonicBalls.S11ak

#print axioms HarmonicBalls.S11ak.metricDecoder_punctured_ball_seven
