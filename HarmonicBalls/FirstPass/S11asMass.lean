import HarmonicBalls.FirstPass.S11asMeasure

/-!
# Almost-sure Block 2 for the mass clause (fp-S11as, round 7)

Applies `FirstPassS11asMeasure.rootedMeasure_restrict_proportional` with the rooted centre `z` and the disc `ball z b`
(`0 ∉ closedBall z b` since `2b < ‖z‖`), to the physical rooted mass at background `α₀` and the Cameron–Martin shifted
rooted mass at background `0`. The observation identity comes from `rootedMeanZeroObs_eq_addFun` with the shift `f`
equal to `-α₀ log‖·‖` on `ball z b`.
Input not supplied by the frozen statements: `[IsProbabilityMeasure P']` (see `CameronMartinGFFReweighting`, which does not
state it; `LocalLQGDecoderCommonFrozen` needs it).
-/

namespace FirstPassS11asMass

open MeasureTheory Metric Set Filter
open scoped ENNReal
open HarmonicBalls

/-- **Block 2 almost surely, on the disc `ball z b`.** Given the physical rooted mass `μR` at background `α₀` and a
shifted rooted mass `μ₁` at background `0` (on a probability space `P'` equivalent to `P` from above), the two are
almost surely proportional on `ball z b`. -/
theorem ae_rootedMass_proportional_ball
    (hK : LocalLQGDecoderCommonFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P P' : Measure Ω} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {γ α₀ b : ℝ} {z : ℂ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {f : ℂ → ℝ}
    {μR μ₁ : Ω → Measure ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hb : 0 < b) (hz : 2 * b < ‖z‖)
    (hα₀ : α₀ < lqgQ γ) (hα₁ : (0 : ℝ) < lqgQ γ) (hPP : P ≪ P')
    (hf : ∀ x ∈ ball z b, f x = -α₀ * Real.log ‖x‖)
    (hW₀ : IsWholePlaneGFF P hC hcirc)
    (hW₁ : IsWholePlaneGFF P' (fun ω => addFunPairing (hC ω) f)
      (fun ω r x => hcirc ω r x + Real.circleAverage f x r))
    (hμR : IsLQGMeasure P γ (fun ω => rootedCircleAverage α₀ γ z (hcirc ω)) μR)
    (hμ₁ : IsLQGMeasure P' γ
      (fun ω => rootedCircleAverage 0 γ z (fun r x => hcirc ω r x + Real.circleAverage f x r)) μ₁) :
    ∀ᵐ ω ∂P, ∃ c₀ c₁ : ℝ≥0∞, 0 < c₀ ∧ c₀ < ⊤ ∧ 0 < c₁ ∧ c₁ < ⊤ ∧
      c₀ • (μR ω).restrict (ball z b) = c₁ • (μ₁ ω).restrict (ball z b) := by
  have h0 : (0 : ℂ) ∉ closedBall z b := by
    intro h
    have h' := mem_closedBall.1 h
    rw [dist_zero_left] at h'
    linarith
  have hobs : ∀ ω, rootedMeanZeroObs α₀ γ (ball z b) z (hC ω) =
      rootedMeanZeroObs 0 γ (ball z b) z (addFunPairing (hC ω) f) :=
    fun ω => funext fun φ => FirstPassS11asMeasure.rootedMeanZeroObs_eq_addFun hf φ
  exact FirstPassS11asMeasure.rootedMeasure_restrict_proportional hK hγ0 hγ2 hb h0 hα₀ hα₁ hW₀ hW₁ hμR hμ₁ hPP hobs

end FirstPassS11asMass
