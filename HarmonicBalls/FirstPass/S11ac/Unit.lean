import HarmonicBalls.FirstPass.S11ac
import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement

/-! # The punctured-ball metric decoder on the unit ball (fp-S11ac, owner z6)

Corollary of `S11ac.metricDecoder_punctured_ball` with `R = 1`: the local metric replacement hypothesis is discharged by
n2's `LocalMetricReplacementStmt` (FirstPass/S11r/LocalMetricReplacement.lean), which is stated on disks of `ball 0 1`.
-/

namespace HarmonicBalls.S11ac

universe u

open MeasureTheory Set Metric
open scoped ENNReal

/-- **Punctured-ball metric decoder, unit ball.** The statement of `metricDecoder_punctured_ball` with `R = 1`. -/
theorem metricDecoder_punctured_ball_unit (hAx : HarmonicBalls.LQGMetricFieldAxiomsUnivFrozen.{u}) (γ ξ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    (hN2 : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂) :
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ∃ Ψ : ModConstTestPairings (ball (0 : ℂ) 1) → ℂ × ℂ → ℝ, (∀ p : ℂ × ℂ, Measurable fun ℓ => Ψ ℓ p) ∧
        ∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p ∈ (ball (0 : ℂ) 1 \ {0}) ×ˢ (ball (0 : ℂ) 1 \ {0}),
            ENNReal.ofReal (Ψ (localModConstField α₀ hC (ball (0 : ℂ) 1) ω) p) =
              ENNReal.ofReal b * internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun z => -α₀ * Real.log ‖z‖) u v).toReal) (ball (0 : ℂ) 1 \ {0}) p.1 p.2 :=
  metricDecoder_punctured_ball hAx γ ξ hγ hγ2 hξ 1 one_pos (fun 𝔇 h𝔇 c₁ c₂ r₁ r₂ h1 h2 h3 h4 h5 => by
    have hS := hN2 c₁ c₂ r₁ r₂
    unfold HarmonicBalls.LocalMetricReplacementStmt at hS
    obtain ⟨m, hm, h18, -⟩ := hS hγ hγ2 h1 h2 h3 h4 h5 𝔇 h𝔇
    exact ⟨m, hm, h18⟩)

end HarmonicBalls.S11ac
