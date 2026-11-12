import HarmonicBalls.FirstPass.Phase2.DomainMarkovOuterPotential
import HarmonicBalls.FirstPass.Phase2.CameronMartinLipschitzShiftDerived
import HarmonicBalls.Proofs.Sec8.ExteriorLaplacianIndependence

/-!
# Covariance potential of a Laplacian

The whole-plane covariance kernel `G(x, y) = log (max(|x|, 1) max(|y|, 1) / |x - y|)` has zero average over the
unit circle in each variable (the whole-plane GFF is normalized by its unit-circle average). Consequently the
covariance potential of every test function has zero unit-circle average, and for a smooth compactly supported `ψ`
the normalization constant `∫ Δψ(y) log max(|y|, 1) dy` is `2π` times the unit-circle average of `ψ` (the
distributional Laplacian of `log max(|·|, 1)` is `2π` times the uniform probability measure on the unit circle).

## Main results

* `circleAverage_outerPotential_unitCircle`: `avg_{∂B(0,1)} outerPotential φ = 0` for every test function `φ`;
* `integral_laplacian_mul_wholePlaneNormalization`: `∫ Δψ · log max(|·|, 1) = 2π avg_{∂B(0,1)} ψ`;
* `outerPotential_laplacian`: `outerPotential (Δψ) x = 2π (avg_{∂B(0,1)} ψ - ψ(x))`;
* `IsWholePlaneGFF.covariance_pairing_laplacian_eq_integral`:
  `Cov((h, φ), (h, Δψ)) = 2π ∫ φ(x) (avg_{∂B(0,1)} ψ - ψ(x)) dx` for every test function `φ`.
-/

open MeasureTheory ProbabilityTheory Set Laplacian

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The normalization `log max(|·|, 1)` vanishes on the unit circle, so its unit-circle average is `0`. -/
theorem circleAverage_wholePlaneNormalization_unitCircle :
    Real.circleAverage wholePlaneNormalization 0 1 = 0 := by
  refine Real.circleAverage_const_on_circle fun y hy => ?_
  have hy1 : ‖y‖ = 1 := by simpa using hy
  simp [wholePlaneNormalization, hy1]

/-- The whole-plane covariance kernel has zero average over the unit circle in its second variable. -/
theorem circleAverage_wholePlaneCov_unitCircle (x : ℂ) :
    Real.circleAverage (wholePlaneCov x) 0 1 = 0 := by
  change Real.circleAverage (fun y => wholePlaneCov x y) 0 1 = 0
  rw [circleAverage_wholePlaneCov_eq one_pos, circleAverage_wholePlaneNormalization_unitCircle]
  simp only [wholePlaneNormalization, zero_sub, norm_neg, add_zero, max_comm 1 ‖x‖, sub_self]

/-- **Unit-circle normalization of the covariance potential.** For every test function `φ`, the average of
`outerPotential φ` over the unit circle vanishes (by Fubini it is `∫ φ(x) avg_{∂B(0,1)} G(x, ·) dx = 0`). -/
theorem circleAverage_outerPotential_unitCircle {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) :
    Real.circleAverage (outerPotential φ) 0 1 = 0 := by
  have h := wholePlaneGFFCov_pairing_circle_symm
    (⟨φ, hφ.1, hφ.2.1, subset_univ _⟩ : LQGMetric.TestC) 0 one_pos
  change (∫ x, φ x * Real.circleAverage (wholePlaneCov x) 0 1) =
    Real.circleAverage (outerPotential φ) 0 1 at h
  rw [← h]
  simp [circleAverage_wholePlaneCov_unitCircle]

/-- **Normalization constant of a Laplacian.** For a smooth compactly supported `ψ`,
`∫ Δψ(y) log max(|y|, 1) dy = 2π avg_{∂B(0,1)} ψ`. -/
theorem integral_laplacian_mul_wholePlaneNormalization {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∫ y, Δ ψ y * wholePlaneNormalization y = 2 * Real.pi * Real.circleAverage ψ 0 1 := by
  have h0 := circleAverage_outerPotential_unitCircle (isTestFunction_laplacian_of_smooth hψ hψc)
  have hpot : outerPotential (Δ ψ) = fun x =>
      (∫ y, Δ ψ y * wholePlaneNormalization y) - 2 * Real.pi * ψ x :=
    funext (integral_laplacian_mul_wholePlaneCov (hψ.of_le (by simp)) hψc)
  have hsm : Real.circleAverage (fun x => 2 * Real.pi * ψ x) 0 1 = 2 * Real.pi * Real.circleAverage ψ 0 1 := by
    simpa [smul_eq_mul] using Real.circleAverage_fun_smul (a := 2 * Real.pi) (f := ψ) (c := 0) (R := 1)
  rw [hpot, Real.circleAverage_fun_sub
    (circleIntegrable_const (∫ y, Δ ψ y * wholePlaneNormalization y) 0 1)
    ((show Continuous fun x => 2 * Real.pi * ψ x from continuous_const.mul hψ.continuous).continuousOn.circleIntegrable
      zero_le_one),
    Real.circleAverage_const, hsm] at h0
  linarith

/-- **Covariance potential of a Laplacian.** For a smooth compactly supported `ψ`,
`outerPotential (Δψ) x = 2π (avg_{∂B(0,1)} ψ - ψ(x))`. -/
theorem outerPotential_laplacian {ψ : ℂ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (x : ℂ) : outerPotential (Δ ψ) x = 2 * Real.pi * (Real.circleAverage ψ 0 1 - ψ x) := by
  rw [show outerPotential (Δ ψ) x = ∫ y, Δ ψ y * wholePlaneCov x y from rfl,
    integral_laplacian_mul_wholePlaneCov (hψ.of_le (by simp)) hψc,
    integral_laplacian_mul_wholePlaneNormalization hψ hψc]
  ring

/-- **Covariance with a Laplacian pairing.** For a test function `φ` (of any mean) and a smooth compactly
supported `ψ`, `Cov((h, φ), (h, Δψ)) = 2π ∫ φ(x) (avg_{∂B(0,1)} ψ - ψ(x)) dx`. -/
theorem IsWholePlaneGFF.covariance_pairing_laplacian_eq_integral (hh : IsWholePlaneGFF P hC hcirc)
    {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    cov[fun s => hC s φ, fun s => hC s (Δ ψ); P] =
      2 * Real.pi * ∫ x, φ x * (Real.circleAverage ψ 0 1 - ψ x) := by
  rw [hh.covariance_pairing_eq_integral_outerPotential hφ (isTestFunction_laplacian_of_smooth hψ hψc),
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [outerPotential_laplacian hψ hψc x]
  ring

end HarmonicBalls
