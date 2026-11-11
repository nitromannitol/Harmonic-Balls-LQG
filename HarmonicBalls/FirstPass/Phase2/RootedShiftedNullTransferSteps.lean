import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.CircleLogPotential
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmDMSConstant
import HarmonicBalls.FirstPass.S8c.LocalObservation

/-! # Shifted-root null transfer: the local steps L1, L2 and L5 (MQ-lh-29)

Steps of the corrected null-transfer statement `RootedShiftedDecoderNullTransfer`
(`FirstPass/Phase2/RootedDominationJoint.lean`), following `notes/fp-gaps/MATH-ANSWERS.md`, section MQ-lh-29:

* L1: almost surely the DMS constant vanishes, so the DMS-shifted circle profile is the field plus the
  shift `Av_{∂B_s(x)} dmsShift`; the unit-circle average of `dmsShift γ z` is zero (Duplantier-Miller-Sheffield,
  arXiv:1409.7055, Lemma A.10; `dmsConstant_ae_zero`).
* L2: on a small sphere inside the unit disc the normalisation `γ log max(|w|,1)` vanishes, so the circle
  average of `dmsShift γ z` is `-γ log max(ρ, |c - z|)` (Jensen's formula for `log|w - z|`, which is
  `circleAverage_log_norm_sub_eq_log_max`), and the α₀-field of the shifted profile is an explicit local
  expression (Lemma 8.2 of Bou-Rabee and Gwynne, proof, printed `h̃|_{B_r}` decomposition).
* L5: mass normalisation `N_r(η) = η(B_{r/2}(0))⁻¹ • η` removes a constant factor `c ∈ (0, ∞)`.

Terminology: Duplantier-Sheffield (LQG measures from the GFF), Armitage-Gardiner (circle averages).
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- **L1.** Almost surely the DMS constant `dmsConstant γ z (h₁(0))` vanishes for `|z| ≤ 1`, so the DMS-shifted
circle profile `hc r x + Av_{∂B_r(x)} dmsShift γ z + κ` equals the field plus the shift. -/
theorem ae_dmsShiftedCircle_eq_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ∀ᵐ ω ∂P, (fun s x => hcirc ω s x + Real.circleAverage (dmsShift γ z) x s
        + dmsConstant γ z (hcirc ω 1 0)) =
      fun s x => hcirc ω s x + Real.circleAverage (dmsShift γ z) x s := by
  filter_upwards [dmsConstant_ae_zero hG γ hz] with ω hω
  funext s x
  simp [hω]

/-- **L2 (sphere average of the DMS shift).** On a sphere `∂B_ρ(c)` contained in the closed unit disc, the
normalisation `γ log max(|w|,1)` of `dmsShift γ z` vanishes, and the circle average is
`-γ log max(ρ, |c - z|)`. -/
theorem circleAverage_dmsShift_of_sphere_le_one {γ : ℝ} {z c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ‖c‖ + ρ ≤ 1) :
    Real.circleAverage (dmsShift γ z) c ρ = -γ * Real.log (max ρ ‖c - z‖) := by
  have hs : Set.EqOn (dmsShift γ z) (fun w => (-γ) • Real.log ‖w - z‖) (sphere c |ρ|) := by
    intro w hw
    rw [mem_sphere, dist_eq_norm, abs_of_pos hρ] at hw
    have hn : ‖w‖ ≤ 1 := by
      calc ‖w‖ = ‖c + (w - c)‖ := by simp
        _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
        _ ≤ 1 := by rw [hw]; linarith
    simp only [dmsShift, max_eq_right hn, Real.log_one, mul_zero, add_zero, smul_eq_mul]
  rw [Real.circleAverage_congr_sphere hs, Real.circleAverage_fun_smul,
    circleAverage_log_norm_sub_eq_log_max hρ c z, smul_eq_mul]

/-- **L2 (local form of the shifted α₀-field).** For a sphere `∂B_ρ(c)` in the unit disc, with `ρ ≤ |c|`, the
α₀-field circle average of the DMS-shifted profile is `p ρ c - γ log max(ρ, |c - z|) - α₀ log |c|`. -/
theorem fieldCircleAverage_dmsShift_add {α₀ γ : ℝ} {z c : ℂ} (p : ℝ → ℂ → ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    (hcρ : ρ ≤ ‖c‖) (hc : ‖c‖ + ρ ≤ 1) :
    fieldCircleAverage α₀ (fun s x => p s x + Real.circleAverage (dmsShift γ z) x s) ρ c =
      p ρ c - γ * Real.log (max ρ ‖c - z‖) - α₀ * Real.log ‖c‖ := by
  have hA := circleAverage_dmsShift_of_sphere_le_one (γ := γ) (z := z) hρ hc
  have hB : Real.circleAverage (fun x : ℂ => Real.log ‖x‖) c ρ = Real.log ‖c‖ := by
    have h := circleAverage_log_norm_sub_eq_log_max hρ c 0
    simp only [sub_zero] at h
    rw [h, max_eq_right hcρ]
  simp only [fieldCircleAverage]
  rw [hA, hB]
  ring

/-- **L5 (mass normalisation removes constants).** For a constant `c ∈ (0, ∞)`, `N_r(c • η) = N_r(η)`. -/
theorem massNormalize_smul_const {r : ℝ} {c : ℝ≥0∞} (η : Measure ℂ) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    massNormalize r (c • η) = massNormalize r η := by
  unfold massNormalize
  refine Measure.ext fun s _ => ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  calc c⁻¹ * (η (ball 0 (r / 2)))⁻¹ * (c * η s)
      = (η (ball 0 (r / 2)))⁻¹ * (c⁻¹ * c) * η s := by ring
    _ = (η (ball 0 (r / 2)))⁻¹ * η s := by rw [ENNReal.inv_mul_cancel hc0 hct, mul_one]

end HarmonicBalls
