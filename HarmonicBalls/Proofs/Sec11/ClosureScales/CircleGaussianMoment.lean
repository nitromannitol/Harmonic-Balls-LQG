import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec8.CircleLogPotential

/-! # Route (A), Palm identity: the Gaussian moment of a circle average

For the whole-plane GFF `(P, hC, hcirc)` and a circle `∂B(z, r)` contained in the closed unit disk, the circle
average `h_r(z) = hcirc · r z` is a centred Gaussian with variance `-log r`: the covariance kernel `wholePlaneCov`
averaged twice over the circle, the two `log max(|·|, 1)` terms vanishing. Hence `E exp(γ h_r(z)) = r^(-γ²/2)`,
i.e. `E[r^(γ²/2) exp(γ h_r(z))] = 1`: this is the first identity of the paragraph "First moments and the required
`L¹` convergence" of r10 `l:r9-marked` (lines 2575-2790).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric

namespace HarmonicBalls

/-- The variance of a circle average inside the closed unit disk: `wholePlaneGFFCov (circle r z) (circle r z) = -log r`. -/
theorem wholePlaneGFFCov_circle_self_eq {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hdisk : ∀ x ∈ Metric.sphere z r, ‖x‖ ≤ 1) :
    wholePlaneGFFCov (.circle r z) (.circle r z) = -Real.log r := by
  have hN0 : Real.circleAverage wholePlaneNormalization z r = 0 := by
    have hEq : Set.EqOn wholePlaneNormalization (fun _ => (0 : ℝ)) (Metric.sphere z |r|) := by
      intro y hy
      rw [abs_of_pos hr] at hy
      simp [wholePlaneNormalization, max_eq_right (hdisk y hy)]
    rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]
  have hinner : ∀ x ∈ Metric.sphere z r,
      Real.circleAverage (fun y => wholePlaneCov x y) z r = -Real.log r := by
    intro x hx
    have hx0 : wholePlaneNormalization x = 0 := by
      simp [wholePlaneNormalization, max_eq_right (hdisk x hx)]
    have hzx : ‖z - x‖ = r := by
      rw [← dist_eq_norm, dist_comm]
      exact mem_sphere.1 hx
    rw [circleAverage_wholePlaneCov_eq hr z x, hx0, hN0, hzx, max_self]
    ring
  have hEq : Set.EqOn (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r)
      (fun _ => -Real.log r) (Metric.sphere z |r|) := by
    rw [abs_of_pos hr]
    exact hinner
  show Real.circleAverage (fun x => Real.circleAverage (fun y => wholePlaneCov x y) z r) z r
    = -Real.log r
  rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]

/-- **Gaussian moment of a circle average** (r10 `l:r9-marked`, "First moments"): for a circle in the closed unit
disk, `E exp(γ h_r(z)) = exp(γ² (-log r) / 2) = r^(-γ²/2)`. -/
theorem integral_exp_circleAverage_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {r : ℝ} (hr : 0 < r) (z : ℂ)
    (hdisk : ∀ x ∈ Metric.sphere z r, ‖x‖ ≤ 1) (γ : ℝ) :
    ∫ ω, Real.exp (γ * hcirc ω r z) ∂P = Real.exp (γ ^ 2 * (-Real.log r) / 2) := by
  have hadm : (GFFObservable.circle r z).IsAdmissible := hr
  set X : Ω → ℝ := fun ω => hcirc ω r z with hX_def
  have hGL : HasGaussianLaw X P :=
    hG.isGaussianProcess.hasGaussianLaw_eval ⟨GFFObservable.circle r z, hadm⟩
  have hmeas : AEMeasurable X P := (hG.measurable_circle r z hr).aemeasurable
  have hmean : ∫ ω, X ω ∂P = 0 := hG.integral_eq_zero (GFFObservable.circle r z) hadm
  have hvar : variance X P = -Real.log r := by
    rw [← covariance_self hmeas]
    exact (hG.covariance_eq (GFFObservable.circle r z) (GFFObservable.circle r z) hadm hadm).trans
      (wholePlaneGFFCov_circle_self_eq hr z hdisk)
  have hlog : 0 ≤ -Real.log r := by
    rw [← hvar]
    exact variance_nonneg X P
  have hlaw : HasLaw X (gaussianReal 0 (-Real.log r).toNNReal) P := by
    refine ⟨hmeas, ?_⟩
    rw [hGL.map_eq_gaussianReal, hmean, hvar]
  have hm := mgf_gaussianReal hlaw γ
  rw [Real.coe_toNNReal _ hlog, zero_mul, zero_add] at hm
  have hdef : (∫ ω, Real.exp (γ * hcirc ω r z) ∂P) = mgf X P γ := rfl
  rw [hdef, hm]
  congr 1
  ring

end HarmonicBalls

end
