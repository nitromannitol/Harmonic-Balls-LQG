import HarmonicBalls.Proofs.Sec8.PuncturedFieldGeneration

/-! # Covariance of Laplacian pairings

The imported Section 8 reduction uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

open MeasureTheory ProbabilityTheory Metric Set Laplacian Filter
open scoped Topology ProbabilityTheory

namespace HarmonicBalls

/-- Pairing a mean-zero density with the Laplacian of a compact potential
reduces the whole-plane GFF covariance to the integral against the potential. -/
theorem wholePlaneGFFCov_pairing_laplacian_eq_integral {φ ψ : ℂ → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφzero : ∫ x, φ x = 0)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    wholePlaneGFFCov (.pairing φ) (.pairing (Δ ψ)) = -2 * Real.pi * ∫ x, φ x * ψ x := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hφc
  have hφψi : Integrable (fun x => φ x * ψ x) :=
    (hφ.mul hψ.continuous).integrable_of_hasCompactSupport hφc.mul_right
  let a : ℝ := ∫ y, Δ ψ y * wholePlaneNormalization y
  change (∫ x, φ x * (∫ y, Δ ψ y * wholePlaneCov x y)) = _
  simp_rw [integral_laplacian_mul_wholePlaneCov hψ hψc]
  change (∫ x, φ x * (a - 2 * Real.pi * ψ x)) = _
  calc
    _ = ∫ x, φ x * a - (2 * Real.pi) * (φ x * ψ x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (∫ x, φ x) * a - (2 * Real.pi) * ∫ x, φ x * ψ x := by
      rw [integral_sub (hφi.mul_const a) (hφψi.const_mul _), integral_mul_const, integral_const_mul]
    _ = _ := by rw [hφzero]; ring

/-- The covariance of two compactly supported Laplacians is the integral of
one Laplacian against the other potential. -/
theorem wholePlaneGFFCov_laplacian_laplacian_eq_integral {u v : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) :
    wholePlaneGFFCov (.pairing (Δ u)) (.pairing (Δ v)) =
      -2 * Real.pi * ∫ x, Δ u x * v x := by
  exact wholePlaneGFFCov_pairing_laplacian_eq_integral
    (continuous_laplacian_of_contDiff hu) (hasCompactSupport_laplacian huc)
    (integral_laplacian_eq_zero hu huc) hv hvc

/-- Integration by parts on the plane identifies the negative Laplacian
pairing with the Dirichlet energy in the orthonormal directions `1` and `I`. -/
theorem integral_mul_laplacian_eq_neg_dirichlet_energy {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    (∫ x, u x * Δ u x) =
      -(∫ x, (fderiv ℝ u x 1) ^ 2 + (fderiv ℝ u x Complex.I) ^ 2) := by
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have key : ∀ v : ℂ,
      Integrable (fun x => fderiv ℝ u x v * fderiv ℝ u x v) ∧
      Integrable (fun x => u x * fderiv ℝ (fun y => fderiv ℝ u y v) x v) ∧
      (∫ x, u x * fderiv ℝ (fun y => fderiv ℝ u y v) x v) =
        -(∫ x, fderiv ℝ u x v * fderiv ℝ u x v) := by
    intro v
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ u x v) := hu1.clm_apply contDiff_const
    have hdc : HasCompactSupport (fun x => fderiv ℝ u x v) :=
      (huc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    have hddc : HasCompactSupport (fun x => fderiv ℝ (fun y => fderiv ℝ u y v) x v) :=
      (hdc.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
    have hdd : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ u y v) x v) :=
      (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have i1 : Integrable (fun x => fderiv ℝ u x v * fderiv ℝ u x v) :=
      (hd.continuous.mul hd.continuous).integrable_of_hasCompactSupport hdc.mul_right
    have i2 : Integrable (fun x => u x * fderiv ℝ (fun y => fderiv ℝ u y v) x v) :=
      (hu.continuous.mul hdd).integrable_of_hasCompactSupport hddc.mul_left
    have i3 : Integrable (fun x => u x * fderiv ℝ u x v) :=
      (hu.continuous.mul hd.continuous).integrable_of_hasCompactSupport hdc.mul_left
    exact ⟨i1, i2, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
      (fun x _ => (hu.differentiable (by norm_num)) x)
      (fun x _ => (hd.differentiable one_ne_zero) x)⟩
  obtain ⟨h1, h1', h1eq⟩ := key 1
  obtain ⟨hI, hI', hIeq⟩ := key Complex.I
  simp_rw [laplacian_eq_fderiv_fderiv hu, mul_add]
  rw [integral_add h1' hI', h1eq, hIeq, ← neg_add, ← integral_add h1 hI]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- The covariance of a Laplacian pairing with itself is `2π` times the
Dirichlet energy of its compact potential. -/
theorem wholePlaneGFFCov_laplacian_self_eq_dirichlet_energy {u : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    wholePlaneGFFCov (.pairing (Δ u)) (.pairing (Δ u)) =
      2 * Real.pi * ∫ x, (fderiv ℝ u x 1) ^ 2 + (fderiv ℝ u x Complex.I) ^ 2 := by
  rw [wholePlaneGFFCov_laplacian_laplacian_eq_integral hu huc hu huc]
  have heq : (∫ x, Δ u x * u x) = ∫ x, u x * Δ u x := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [heq, integral_mul_laplacian_eq_neg_dirichlet_energy hu huc]
  ring

/-- The pairing covariance is symmetric on test functions. -/
theorem IsWholePlaneGFF.wholePlaneGFFCov_pairing_comm
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) :
    wholePlaneGFFCov (.pairing φ) (.pairing ψ) =
      wholePlaneGFFCov (.pairing ψ) (.pairing φ) := by
  have h1 := h.covariance_eq (.pairing φ) (.pairing ψ) hφ hψ
  have h2 := h.covariance_eq (.pairing ψ) (.pairing φ) hψ hφ
  simp only [GFFObservable.eval] at h1 h2
  rw [← h1, ← h2, covariance_comm]

/-- For compact potentials, the covariance error between their Laplacians is
`2π` times the Dirichlet energy of their difference. -/
theorem IsWholePlaneGFF.laplacian_covariance_error_eq_dirichlet_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {u v : ℂ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hΔu : IsTestFunction univ (Δ u)) (hΔv : IsTestFunction univ (Δ v)) :
    wholePlaneGFFCov (.pairing (Δ u)) (.pairing (Δ u)) +
      wholePlaneGFFCov (.pairing (Δ v)) (.pairing (Δ v)) -
      2 * wholePlaneGFFCov (.pairing (Δ u)) (.pairing (Δ v)) =
      2 * Real.pi * ∫ x, (fderiv ℝ (u - v) x 1) ^ 2 +
        (fderiv ℝ (u - v) x Complex.I) ^ 2 := by
  have hcross : (∫ x, Δ u x * v x) = ∫ x, Δ v x * u x := by
    have hc := h.wholePlaneGFFCov_pairing_comm hΔu hΔv
    rw [wholePlaneGFFCov_laplacian_laplacian_eq_integral hu huc hv hvc,
      wholePlaneGFFCov_laplacian_laplacian_eq_integral hv hvc hu huc] at hc
    have hpi := Real.pi_pos
    nlinarith
  have hΔ : ∀ x, Δ (u - v) x = Δ u x - Δ v x := fun x =>
    hu.contDiffAt.laplacian_sub hv.contDiffAt
  have hiuu : Integrable (fun x => Δ u x * u x) :=
    ((continuous_laplacian_of_contDiff hu).mul hu.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian huc).mul_right
  have hiuv : Integrable (fun x => Δ u x * v x) :=
    ((continuous_laplacian_of_contDiff hu).mul hv.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian huc).mul_right
  have hivu : Integrable (fun x => Δ v x * u x) :=
    ((continuous_laplacian_of_contDiff hv).mul hu.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hvc).mul_right
  have hivv : Integrable (fun x => Δ v x * v x) :=
    ((continuous_laplacian_of_contDiff hv).mul hv.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hvc).mul_right
  have hdiff : (∫ x, Δ (u - v) x * (u - v) x) =
      (∫ x, Δ u x * u x) - 2 * (∫ x, Δ u x * v x) +
        (∫ x, Δ v x * v x) := by
    have heq : (fun x => Δ (u - v) x * (u - v) x) =
        fun x => (Δ u x * u x - Δ u x * v x) -
          (Δ v x * u x - Δ v x * v x) := by
      funext x
      simp only [hΔ x, Pi.sub_apply]
      ring
    rw [heq]
    change (∫ x, ((fun x => Δ u x * u x) - (fun x => Δ u x * v x)) x -
      ((fun x => Δ v x * u x) - (fun x => Δ v x * v x)) x) = _
    rw [integral_sub (hiuu.sub hiuv) (hivu.sub hivv)]
    simp only [Pi.sub_apply]
    rw [integral_sub hiuu hiuv, integral_sub hivu hivv, ← hcross]
    ring
  have hself := wholePlaneGFFCov_laplacian_self_eq_dirichlet_energy (hu.sub hv) (huc.sub hvc)
  rw [wholePlaneGFFCov_laplacian_laplacian_eq_integral (hu.sub hv) (huc.sub hvc)
    (hu.sub hv) (huc.sub hvc)] at hself
  change -2 * Real.pi * (∫ x, Δ (u - v) x * (u - v) x) =
    2 * Real.pi * ∫ x, (fderiv ℝ (u - v) x 1) ^ 2 +
      (fderiv ℝ (u - v) x Complex.I) ^ 2 at hself
  rw [hdiff] at hself
  rw [wholePlaneGFFCov_laplacian_laplacian_eq_integral hu huc hu huc,
    wholePlaneGFFCov_laplacian_laplacian_eq_integral hv hvc hv hvc,
    wholePlaneGFFCov_laplacian_laplacian_eq_integral hu huc hv hvc]
  linarith

/-- The covariance approximation error against a compact potential has a
local-integral expression. -/
theorem IsWholePlaneGFF.laplacian_covariance_error_eq_integrals
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφzero : ∫ x, φ x = 0)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hΔψ : IsTestFunction univ (Δ ψ)) :
    wholePlaneGFFCov (.pairing (Δ ψ)) (.pairing (Δ ψ)) +
      wholePlaneGFFCov (.pairing φ) (.pairing φ) -
      2 * wholePlaneGFFCov (.pairing (Δ ψ)) (.pairing φ) =
      wholePlaneGFFCov (.pairing φ) (.pairing φ) -
      2 * Real.pi * (∫ x, Δ ψ x * ψ x) +
      4 * Real.pi * ∫ x, φ x * ψ x := by
  rw [h.wholePlaneGFFCov_pairing_comm hΔψ hφ,
    wholePlaneGFFCov_laplacian_laplacian_eq_integral hψ hψc hψ hψc,
    wholePlaneGFFCov_pairing_laplacian_eq_integral hφ.1.continuous hφ.2.1 hφzero hψ hψc]
  ring

end HarmonicBalls
