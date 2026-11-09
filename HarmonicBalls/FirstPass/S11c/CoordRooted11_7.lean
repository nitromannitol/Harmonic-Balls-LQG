import HarmonicBalls.FirstPass.S11c.Translate11_7
import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.Proposed.LQG

/-!
# Lemma 11.7, the rooted LQG measure is a translate of the origin measure (B2 sec 5.1, coordinate change)

Let `hcirc' r x = hcirc r (x + z) - hcirc 1 z` be the translate of the whole-plane GFF by `z`, normalized on the unit
circle (the field of `WholePlaneGFFAffineInvariance` with `a = 1`, `b = z`). The rooted circle averages
`rootedCircleAverage 0 γ z hcirc` (Frozen/S11c.lean) equal the `γ`-profile of `hcirc'` at `w - z`, shifted by
`hcirc 1 z` (`rootedCircleAverage_zero_eq`). The LQG measure `μ_z` of the rooted profile is therefore the translate by
`z` of the LQG measure `ν` of `hcirc'` at parameter `γ`, times `exp(γ hcirc(1,z))` (`ae_rootedMeasure_eq_translate`).
The proof combines the coordinate change `LQGMeasureCoordChange` (Proposed/LQG.lean:114, a = 1, b = -z), the constant
shift `isLQGLimit_sub_const` (Translate11_7.lean:42) and the uniqueness of vague limits `IsLQGLimit.unique`
(Defs/LQG.lean:107). Here the coordinate change is a hypothesis (Proposed input, first pass).
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- `γ < Q = 2/γ + γ/2` for `0 < γ < 2` (so `α₀ = γ` is an admissible insertion in `LQGMeasureCoordChange`). -/
lemma gamma_lt_lqgQ {γ : ℝ} (h0 : 0 < γ) (h2 : γ < 2) : γ < lqgQ γ := by
  unfold lqgQ
  have h : γ / 2 < 2 / γ := by
    rw [lt_div_iff₀ h0]
    nlinarith
  linarith

/-- The rooted profile at `z` (insertion `0`) is the `γ`-profile of the translated field `hcirc'` at `w - z`, shifted by
`hcirc 1 z`: `rootedCircleAverage 0 γ z hcirc ε w = fieldCircleAverage γ hcirc' ε (w - z) + hcirc 1 z`. Uses
`circleAverage_sub_const` (Translate11_7.lean:18). -/
lemma rootedCircleAverage_zero_eq (γ : ℝ) (hcirc hcirc' : ℝ → ℂ → ℝ) (z : ℂ)
    (hcirc'_eq : ∀ r x, hcirc' r x = hcirc r (x + z) - hcirc 1 z) (ε : ℝ) (w : ℂ) :
    rootedCircleAverage 0 γ z hcirc ε w = fieldCircleAverage γ hcirc' ε (w - z) - -(hcirc 1 z) := by
  have hA := circleAverage_sub_const (fun x => Real.log ‖x‖) w z ε
  unfold rootedCircleAverage fieldCircleAverage
  rw [hcirc'_eq, sub_add_cancel, hA]
  ring

/-- **Coordinate change for the rooted measure (deterministic form, almost surely).** Let `hcirc'` be the translate of
`hcirc` by `z` (normalized at the unit circle) and assume `hcirc'` is a whole-plane GFF with the coordinate change
`LQGMeasureCoordChange` at parameter `α₀ = γ`. If `ν` is the `γ`-LQG measure of `hcirc'` and `μ_z` the LQG measure of the
rooted profile at `z` (insertion `0`), then almost surely `μ_z = exp(γ hcirc(1,z)) · (ν.map (· + z))`. -/
theorem ae_rootedMeasure_eq_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} (z : ℂ)
    (hcirc'_eq : ∀ ω r x, hcirc' ω r x = hcirc ω r (x + z) - hcirc ω 1 z)
    (hW' : IsWholePlaneGFF P hC' hcirc')
    (hCC : LQGMeasureCoordChange P γ γ hC' hcirc')
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ hcirc' ν)
    {μz : Ω → Measure ℂ} (hμz : IsLQGMeasure P γ (fun ω => rootedCircleAverage 0 γ z (hcirc ω)) μz) :
    ∀ᵐ ω ∂P, μz ω = ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z) := by
  filter_upwards [hCC hW' hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2) ν hν, hμz] with ω hcc hμ
  have hlim := hcc 1 one_ne_zero (-z)
  have hfun : (fun ε w => fieldCircleAverage γ (hcirc' ω) (‖(1 : ℂ)‖ * ε) (1 * w + -z) +
      lqgQ γ * Real.log ‖(1 : ℂ)‖) = fun ε w => fieldCircleAverage γ (hcirc' ω) ε (w - z) := by
    funext ε w
    simp [sub_eq_add_neg]
  have hmeas : (ν ω).map (fun x => (x - -z) / 1) = (ν ω).map (fun x => x + z) := by
    simp only [div_one, sub_neg_eq_add]
  rw [hfun, hmeas] at hlim
  have shifted := isLQGLimit_sub_const hlim (-(hcirc ω 1 z))
  have hfun2 : (fun e w => fieldCircleAverage γ (hcirc' ω) e (w - z) - -(hcirc ω 1 z)) =
      rootedCircleAverage 0 γ z (hcirc ω) := by
    funext e w
    exact (rootedCircleAverage_zero_eq γ (hcirc ω) (hcirc' ω) z (fun r x => hcirc'_eq ω r x) e w).symm
  have hexp : -(γ * -(hcirc ω 1 z)) = γ * hcirc ω 1 z := by ring
  rw [hfun2, hexp] at shifted
  exact hμ.unique shifted

/-- Existence of the rooted LQG measure (the `μ_z` of Lemma 11.7): almost surely the rooted approximations of
`h^ℂ - γ log|· - z|` converge vaguely to `e^{γ h_1(z)} · ν(· + z)`. Same chain as `ae_rootedMeasure_eq_translate`,
without the uniqueness step, so that `IsLQGMeasure` holds for the explicit measure below. -/
theorem ae_isLQGLimit_rooted_translate {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} (z : ℂ)
    (hcirc'_eq : ∀ ω r x, hcirc' ω r x = hcirc ω r (x + z) - hcirc ω 1 z)
    (hW' : IsWholePlaneGFF P hC' hcirc')
    (hCC : LQGMeasureCoordChange P γ γ hC' hcirc')
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ hcirc' ν) :
    ∀ᵐ ω ∂P, IsLQGLimit γ (rootedCircleAverage 0 γ z (hcirc ω))
      (ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z)) := by
  filter_upwards [hCC hW' hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2) ν hν] with ω hcc
  have hlim := hcc 1 one_ne_zero (-z)
  have hfun : (fun ε w => fieldCircleAverage γ (hcirc' ω) (‖(1 : ℂ)‖ * ε) (1 * w + -z) +
      lqgQ γ * Real.log ‖(1 : ℂ)‖) = fun ε w => fieldCircleAverage γ (hcirc' ω) ε (w - z) := by
    funext ε w
    simp [sub_eq_add_neg]
  have hmeas : (ν ω).map (fun x => (x - -z) / 1) = (ν ω).map (fun x => x + z) := by
    simp only [div_one, sub_neg_eq_add]
  rw [hfun, hmeas] at hlim
  have shifted := isLQGLimit_sub_const hlim (-(hcirc ω 1 z))
  have hfun2 : (fun e w => fieldCircleAverage γ (hcirc' ω) e (w - z) - -(hcirc ω 1 z)) =
      rootedCircleAverage 0 γ z (hcirc ω) := by
    funext e w
    exact (rootedCircleAverage_zero_eq γ (hcirc ω) (hcirc' ω) z (fun r x => hcirc'_eq ω r x) e w).symm
  have hexp : -(γ * -(hcirc ω 1 z)) = γ * hcirc ω 1 z := by ring
  rw [hfun2, hexp] at shifted
  exact shifted

end HarmonicBalls.S11c
