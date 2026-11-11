import HarmonicBalls.FirstPass.S8d.ShiftLimit
import HarmonicBalls.FirstPass.S8d.VeryGoodScale
import HarmonicBalls.Proposed.LQG

/-! # helper: the very-good event of the regular field at a translated centre

For the regular field (`α₀ = 0`) and a deterministic translation `q` with `‖q‖ ≤ 1/5`, the very-good annulus event of the
translated regular LQG measure, centred at `-q`, has probability at most `1 - p`. This is the regular-field input of
the phase failure bound (route d1): Draft Lemma 6.7 (`VeryGoodAnnulusProbabilityStmt`,
Draft/Section6.lean:331) applied to the affinely transformed field.

The transformed field is `WholePlaneGFFAffineInvariance` (Proposed/LQG.lean:51) with `a = 1`, `b = q`; its LQG measure is
`e^{γ·(-hcirc ω 1 q)} · (lam ω).map (· - q)`, by `LQGMeasureCoordChange` (Proposed/LQG.lean:114) at `α₀ = 0`,
the constant shift `isLQGLimit_add_const` (ShiftLimit.lean) for the normalization, and `fieldCircleAverage 0 = id`.
The scalar drops out of the very-good event (`isVeryGoodAnnulus_smul_iff`, VeryGoodScale.lean).

Lemma 6.7 enters as the hypothesis `h67` (its conclusion at the fixed constants), so no statement of the paper is
restated here. Source of the inputs: Proposed/LQG.lean (pending source-check), Draft Lemma 6.7. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The distance from the origin to the annulus `𝔸_{1/4,2}(-q)` is at least `1/100` when `‖q‖ ≤ 1/5`. -/
theorem infDist_annulus_lower_bound (q : ℂ) (hq : ‖q‖ ≤ 1 / 5) :
    (1 : ℝ) / 100 ≤ infDist (0 : ℂ) (annulus (-q) (1 / 4) (2 * 1)) := by
  have hne : (annulus (-q) (1 / 4) (2 * 1)).Nonempty := by
    refine ⟨-q + 1, ?_⟩
    simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le]
    norm_num
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  simp only [annulus, Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, not_le] at hy
  obtain ⟨hy1, hy2⟩ := hy
  have hd : dist (0 : ℂ) (-q) ≤ 1 / 5 := by
    rw [dist_eq_norm]
    simpa using hq
  have t := dist_triangle y 0 (-q)
  rw [dist_comm (0 : ℂ) y]
  linarith

/-- The regular-field very-good probability at a translated centre. -/
theorem regular_phase_probability {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : (0 : ℝ) < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (lam : Ω → Measure ℂ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (βminus : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ p : ℝ)
    (h67 : ∀ (Ω' : Type u) [MeasurableSpace Ω'] (P' : Measure Ω') (hC' : Ω' → (ℂ → ℝ) → ℝ)
      (hcirc' : Ω' → ℝ → ℂ → ℝ) (μ : Ω' → Measure ℂ),
      IsWholePlaneGFF P' hC' hcirc' → IsLQGMeasureOfField P' γ 0 hcirc' μ →
      ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, ρ / 100 ≤ infDist (0 : ℂ) (annulus x₀ (ρ / 4) (2 * ρ)) →
        P' {ω | ¬ IsVeryGoodAnnulus (μ ω) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃} ≤ ENNReal.ofReal (1 - p))
    (q : ℂ) (hq : ‖q‖ ≤ 1 / 5) :
    P {ω | ¬ IsVeryGoodAnnulus ((lam ω).map (fun w => w - q)) βminus 1 (-q) N₀ a b C₁m C₁p C₂m C₂p C₃} ≤
      ENNReal.ofReal (1 - p) := by
  -- the LQG measure of the affinely transformed field (a = 1, b = q), up to the constant `e^{γ(-c)}`
  let μ' : Ω → Measure ℂ := fun ω =>
    ENNReal.ofReal (Real.exp (γ * (-hcirc ω ‖(1 : ℂ)‖ q))) • (lam ω).map (fun w => w - q)
  have hG' := hAff hGFF 1 one_ne_zero q
  have hae := hCC hGFF hγ0 hγ2 hα lam hlam
  have hμ' : IsLQGMeasureOfField P γ 0
      (fun ω r z => hcirc ω (‖(1 : ℂ)‖ * r) ((1 : ℂ) * z + q) - hcirc ω ‖(1 : ℂ)‖ q) μ' := by
    unfold IsLQGMeasureOfField IsLQGMeasure
    filter_upwards [hae] with ω hω
    have h1 := hω 1 one_ne_zero q
    have h2 := isLQGLimit_add_const γ (fun e z => hcirc ω e (z + q)) _ (-hcirc ω ‖(1 : ℂ)‖ q)
      (by simpa [fieldCircleAverage] using h1)
    have hfun : fieldCircleAverage 0
        (fun r z => hcirc ω (‖(1 : ℂ)‖ * r) ((1 : ℂ) * z + q) - hcirc ω ‖(1 : ℂ)‖ q) =
        fun e z => hcirc ω e (z + q) + -hcirc ω ‖(1 : ℂ)‖ q := by
      funext e z
      simp [fieldCircleAverage, sub_eq_add_neg]
    rw [hfun]
    exact h2
  have hmain := h67 Ω P _ _ μ' hG' hμ' 1 one_pos (-q) (infDist_annulus_lower_bound q hq)
  have hc0 : ∀ ω, ENNReal.ofReal (Real.exp (γ * (-hcirc ω ‖(1 : ℂ)‖ q))) ≠ 0 := fun ω =>
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hcT : ∀ ω, ENNReal.ofReal (Real.exp (γ * (-hcirc ω ‖(1 : ℂ)‖ q))) ≠ ∞ := fun ω =>
    ENNReal.ofReal_ne_top
  have hset : {ω | ¬ IsVeryGoodAnnulus (μ' ω) βminus 1 (-q) N₀ a b C₁m C₁p C₂m C₂p C₃} =
      {ω | ¬ IsVeryGoodAnnulus ((lam ω).map (fun w => w - q)) βminus 1 (-q) N₀ a b C₁m C₁p C₂m C₂p C₃} := by
    ext ω
    simp only [Set.mem_ofPred_eq, μ']
    rw [isVeryGoodAnnulus_smul_iff _ (hc0 ω) (hcT ω)]
  rw [← hset]
  exact hmain


end HarmonicBalls
