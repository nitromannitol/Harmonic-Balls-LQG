import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Campbell glue: from the reference null set to the marked null set (fp-S11i-11-13, step hP; write-up Step 11)

Write-up eqs (31)-(32) (`CHATGPT-n3-B1-B2.md` sec. 5.2): if, for Lebesgue-almost every root `z` in a ball `B₁`, the
reference observation of the event `S` is `P`-null, then the Campbell integral of `1_S` against the LQG measure is
`P`-null for almost every field. This file derives that from the one-sided frozen Campbell input
`LocalCampbellMarkedRestrictionFrozen` (`Frozen/S11c.lean`), with no further input.

Two side conditions are explicit hypotheses (not frozen, not assumed in any statement that is proved):
* `hfin`: the ball mass `μ_ω(B₁)` is finite almost surely (local finiteness of the LQG measure);
* `hmeas`: the `μ`-weighted mark integral is `P`-AE-measurable in `ω` (needed to pass from a `lintegral` to a.e. zero).
-/

namespace HarmonicBalls.CampbellGlue

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

universe u

/-- Glue from the reference null set (eq. (31)) to the mark-null conclusion (eq. (32)) of the frozen Campbell input. -/
theorem ae_marked_null_of_reference_null (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < HarmonicBalls.lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (href : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0)
    (hfin : ∀ᵐ ω ∂P, μ ω (ball c₁ r₁) ≠ ∞)
    (hmeas : AEMeasurable (fun ω => (μ ω (ball c₁ r₁))⁻¹ *
      ∫⁻ z in ball c₁ r₁, S.indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω)) P) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁, S.indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
  have href0 : ∫⁻ z in ball c₁ r₁, (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
      (HarmonicBalls.campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P) ∂volume = 0 :=
    (lintegral_congr_ae href).trans lintegral_zero
  have hcamp := hCamp γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hh hμ
    c₁ c₂ r₁ r₂ hr₁ hr₂ hsub h0 S hS href0
  have hae := (lintegral_eq_zero_iff' hmeas).1 hcamp
  filter_upwards [hae, hfin] with ω hω hfω
  have hω' : (μ ω (ball c₁ r₁))⁻¹ * ∫⁻ z in ball c₁ r₁, S.indicator (fun _ => (1 : ℝ≥0∞))
      (HarmonicBalls.campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := hω
  by_cases hB : μ ω (ball c₁ r₁) = 0
  · have hres : (μ ω).restrict (ball c₁ r₁) = 0 := Measure.restrict_eq_zero.2 hB
    rw [hres, lintegral_zero_measure]
  · exact (mul_eq_zero.1 hω').resolve_left (ENNReal.inv_ne_zero.2 hfω)

end HarmonicBalls.CampbellGlue
