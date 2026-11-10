import HarmonicBalls.FirstPass.S11i.CampbellGlue
import HarmonicBalls.FirstPass.S11w.BallFinite
import HarmonicBalls.FirstPass.S11w.MarkedKernel

/-!
# Campbell glue with the side conditions discharged (fp-S11w; items (6) of the first-pass task fp-S11w-11-13-hcert-hfin)

`HarmonicBalls.CampbellGlue.ae_marked_null_of_reference_null` (`FirstPass/S11i/CampbellGlue.lean`) takes two side
conditions as hypotheses: `hfin` (the ball mass is almost surely finite) and `hmeas` (the mu-weighted mark integral is
almost surely measurable). Both are discharged here:
* `hfin` is `S11w.ae_measure_ball_ne_top` (`S11w/BallFinite.lean`): local finiteness of the LQG measure, no input;
* `hmeas` is `S11w.aemeasurable_campbellMarked_mass` (`S11w/MarkedKernel.lean`), which uses the named existence input
  `LQGMeasureExistence` (`HarmonicBalls/Proposed/LQG.lean`, pending operator source-check) at the subcritical insertions
  `Q - 1/(n+1)`, and nothing else.
The frozen input `LocalCampbellMarkedRestrictionFrozen` and the reference-null hypothesis `href` are unchanged.
-/

namespace HarmonicBalls.S11w

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- The Campbell glue of `CampbellGlue.ae_marked_null_of_reference_null` with `hfin` and `hmeas` discharged. The only
additional hypothesis is the Proposed existence input `hE` (`LQGMeasureExistence` at the subcritical insertions). -/
theorem ae_marked_null_of_reference_null_discharged (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < HarmonicBalls.lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, HarmonicBalls.LQGMeasureExistence P γ (HarmonicBalls.lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    {S : Set (ℂ × ({φ : ℂ → ℝ // HarmonicBalls.IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (href : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁, S.indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 :=
  HarmonicBalls.CampbellGlue.ae_marked_null_of_reference_null hCamp hγ0 hγ2 hα hh hμ hr₁ hr₂ hsub h0 hS href
    (ae_measure_ball_ne_top hμ c₁ r₁)
    (aemeasurable_campbellMarked_mass P hγ0 hγ2 hα hC hcirc hh hE hμ (ball c₂ r₂) (B := ball c₁ r₁)
      measurableSet_ball isBounded_ball hS)

end HarmonicBalls.S11w
