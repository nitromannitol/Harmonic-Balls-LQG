import HarmonicBalls.Proofs.Sec8.LaplacianCovarianceEnergy
import HarmonicBalls.Proofs.Sec8.OriginGermZeroOne

/-! # Cameron-Martin shifts of the whole-plane GFF by functions of finite Dirichlet energy: Gaussian input

For a smooth compactly supported `u`, the pairing `(h^ℂ, Δ u)` of the whole-plane Gaussian free field is a centred
Gaussian with variance `2π ∫ |∇u|²`, and `Cov((h^ℂ, φ), (h^ℂ, Δ u)) = -2π ∫ φ u` for mean-zero test functions `φ`
(Duplantier-Sheffield, arXiv:0808.1560, Section 3.1; Berestycki-Powell, Section 1.7: the Dirichlet inner product).
Hence, if smooth compactly supported `u_n` converge to `g` uniformly with `∇u_n → ∇g` in `L²`, the pairings
`(h^ℂ, Δ(c u_n))` are Cauchy in `L²(P)` and their covariances with `(h^ℂ, φ)` converge to `-2π c ∫ φ g`: with
`c = -(2π)⁻¹` this exhibits `φ ↦ ∫ φ g` as a Cameron-Martin shift of the mean-zero pairings.

* `IsWholePlaneGFF.integral_sq_pairing_laplacian_sub`: `E[((h^ℂ, Δu) - (h^ℂ, Δv))²] = 2π ∫ |∇(u - v)|²`.
* `IsWholePlaneGFF.covariance_pairing_laplacian`: `Cov((h^ℂ, φ), (h^ℂ, Δv)) = -2π ∫ φ v`.
* `IsWholePlaneGFF.cauchy_pairing_laplacian_of_tendsto_lineDeriv`: the `L²(P)` Cauchy property.
* `IsWholePlaneGFF.tendsto_covariance_pairing_laplacian`: the limit of the covariances.
* `IsWholePlaneGFF.isGaussianProcess_meanZero_pairing`: the mean-zero pairings form a Gaussian process. -/

open MeasureTheory ProbabilityTheory Metric Set Laplacian Filter
open scoped Topology

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The Laplacian of a smooth compactly supported function is a test function. -/
theorem isTestFunction_laplacian_of_smooth {u : ℂ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u) :
    IsTestFunction univ (Δ u) :=
  ⟨contDiff_laplacian_of_smooth hu, hasCompactSupport_laplacian huc, subset_univ _⟩

/-- A constant multiple of a compactly supported function is compactly supported. -/
theorem hasCompactSupport_const_smul_fun {u : ℂ → ℝ} (c : ℝ) (huc : HasCompactSupport u) :
    HasCompactSupport (c • u) :=
  huc.mono fun x hx => by
    rw [Function.mem_support] at hx ⊢
    intro h0
    exact hx (by simp [h0])

/-- A constant multiple of a smooth function is smooth. -/
theorem contDiff_const_smul_fun {u : ℂ → ℝ} (c : ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (c • u) :=
  hu.const_smul c

/-- The mean-zero pairings of the whole-plane GFF form a Gaussian process. -/
theorem IsWholePlaneGFF.isGaussianProcess_meanZero_pairing (h : IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess
      (fun (φ : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0}) ω => hC ω φ.1) P :=
  h.isGaussianProcess.comp_right
    (fun φ : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} => ⟨.pairing φ.1, φ.2.1⟩)

/-- A pairing of the whole-plane GFF with a test function is square integrable. -/
theorem IsWholePlaneGFF.memLp_two_pairing (h : IsWholePlaneGFF P hC hcirc) {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) : MemLp (fun ω => hC ω φ) 2 P :=
  (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing φ, hφ⟩).memLp_two

/-- **Dirichlet energy as the variance of Laplacian pairings.**
`E[((h^ℂ, Δu) - (h^ℂ, Δv))²] = 2π ∫ |∇(u - v)|²` for smooth compactly supported `u`, `v`. -/
theorem IsWholePlaneGFF.integral_sq_pairing_laplacian_sub [IsProbabilityMeasure P] (h : IsWholePlaneGFF P hC hcirc) {u v : ℂ → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v) :
    ∫ ω, (hC ω (Δ u) - hC ω (Δ v)) ^ 2 ∂P =
      2 * Real.pi * ∫ x, (fderiv ℝ (u - v) x 1) ^ 2 + (fderiv ℝ (u - v) x Complex.I) ^ 2 := by
  have hΔu := isTestFunction_laplacian_of_smooth hu huc
  have hΔv := isTestFunction_laplacian_of_smooth hv hvc
  have hX : MemLp (fun ω => hC ω (Δ u)) 2 P := h.memLp_two_pairing hΔu
  have hY : MemLp (fun ω => hC ω (Δ v)) 2 P := h.memLp_two_pairing hΔv
  have hX0 : ∫ ω, hC ω (Δ u) ∂P = 0 := h.integral_eq_zero (.pairing (Δ u)) hΔu
  have hY0 : ∫ ω, hC ω (Δ v) ∂P = 0 := h.integral_eq_zero (.pairing (Δ v)) hΔv
  have hmean : P[(fun ω => hC ω (Δ u)) - fun ω => hC ω (Δ v)] = 0 := by
    have e := integral_sub (hX.integrable (by norm_num)) (hY.integrable (by norm_num))
    simp only [Pi.sub_apply]
    rw [e, hX0, hY0, sub_zero]
  have hvar := variance_of_integral_eq_zero (hX.sub hY).aestronglyMeasurable.aemeasurable hmean
  simp only [Pi.sub_apply] at hvar
  rw [← hvar, variance_sub hX hY, ← covariance_self hX.aestronglyMeasurable.aemeasurable,
    ← covariance_self hY.aestronglyMeasurable.aemeasurable]
  have c1 := h.covariance_eq (.pairing (Δ u)) (.pairing (Δ u)) hΔu hΔu
  have c2 := h.covariance_eq (.pairing (Δ v)) (.pairing (Δ v)) hΔv hΔv
  have c3 := h.covariance_eq (.pairing (Δ u)) (.pairing (Δ v)) hΔu hΔv
  simp only [GFFObservable.eval] at c1 c2 c3
  rw [c1, c2, c3]
  have key := h.laplacian_covariance_error_eq_dirichlet_energy (hu.of_le (by simp)) huc
    (hv.of_le (by simp)) hvc hΔu hΔv
  linarith

/-- **Covariance with a Laplacian pairing.** `Cov((h^ℂ, φ), (h^ℂ, Δv)) = -2π ∫ φ v` for a mean-zero test function `φ`
and a smooth compactly supported `v`. -/
theorem IsWholePlaneGFF.covariance_pairing_laplacian (h : IsWholePlaneGFF P hC hcirc) {φ v : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hφ0 : ∫ x, φ x = 0) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvc : HasCompactSupport v) :
    cov[fun ω => hC ω φ, fun ω => hC ω (Δ v); P] = -2 * Real.pi * ∫ x, φ x * v x := by
  have c := h.covariance_eq (.pairing φ) (.pairing (Δ v)) hφ (isTestFunction_laplacian_of_smooth hv hvc)
  simp only [GFFObservable.eval] at c
  rw [c]
  exact wholePlaneGFFCov_pairing_laplacian_eq_integral hφ.1.continuous hφ.2.1 hφ0 (hv.of_le (by simp)) hvc

/-- **`L²(P)` Cauchy property of Laplacian pairings.** If the directional derivatives of smooth compactly supported
`u_n` in the directions `1` and `i` converge in `L²` to those of `g`, then the pairings `(h^ℂ, Δ(c u_n))` are Cauchy
in `L²(P)`. -/
theorem IsWholePlaneGFF.cauchy_pairing_laplacian_of_tendsto_lineDeriv [IsProbabilityMeasure P]
    (h : IsWholePlaneGFF P hC hcirc)
    {g : ℂ → ℝ} {u : ℕ → ℂ → ℝ} (c : ℝ) (hu : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n)) (huc : ∀ n, HasCompactSupport (u n))
    (hd : ∀ w : ℂ, (∀ n, Integrable fun x => (lineDeriv ℝ (u n) x w - lineDeriv ℝ g x w) ^ 2) ∧
      Tendsto (fun n => ∫ x, (lineDeriv ℝ (u n) x w - lineDeriv ℝ g x w) ^ 2) atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ k ≥ N, ∫ ω, (hC ω (Δ (c • u n)) - hC ω (Δ (c • u k))) ^ 2 ∂P < ε := by
  -- the energy errors
  set G : ℕ → ℂ → ℝ := fun n x => (lineDeriv ℝ (u n) x 1 - lineDeriv ℝ g x 1) ^ 2 +
    (lineDeriv ℝ (u n) x Complex.I - lineDeriv ℝ g x Complex.I) ^ 2 with hG
  have hGi : ∀ n, Integrable (G n) := fun n => ((hd 1).1 n).add ((hd Complex.I).1 n)
  have hF : Tendsto (fun n => ∫ x, G n x) atTop (𝓝 0) := by
    have e : (fun n => ∫ x, G n x) = fun n => (∫ x, (lineDeriv ℝ (u n) x 1 - lineDeriv ℝ g x 1) ^ 2) +
        ∫ x, (lineDeriv ℝ (u n) x Complex.I - lineDeriv ℝ g x Complex.I) ^ 2 :=
      funext fun n => integral_add ((hd 1).1 n) ((hd Complex.I).1 n)
    rw [e]
    simpa using (hd 1).2.add (hd Complex.I).2
  have hbound : ∀ n k, ∫ ω, (hC ω (Δ (c • u n)) - hC ω (Δ (c • u k))) ^ 2 ∂P ≤
      4 * Real.pi * c ^ 2 * (∫ x, G n x) + 4 * Real.pi * c ^ 2 * (∫ x, G k x) := by
    intro n k
    rw [h.integral_sq_pairing_laplacian_sub (u := c • u n) (v := c • u k)
      (contDiff_const_smul_fun c (hu n)) (hasCompactSupport_const_smul_fun c (huc n))
      (contDiff_const_smul_fun c (hu k)) (hasCompactSupport_const_smul_fun c (huc k))]
    have hf : ∀ x w, fderiv ℝ (c • u n - c • u k) x w =
        c * (lineDeriv ℝ (u n) x w - lineDeriv ℝ (u k) x w) := by
      intro x w
      have dn : DifferentiableAt ℝ (u n) x := ((hu n).differentiable (by simp)).differentiableAt
      have dk : DifferentiableAt ℝ (u k) x := ((hu k).differentiable (by simp)).differentiableAt
      rw [dn.lineDeriv_eq_fderiv, dk.lineDeriv_eq_fderiv, fderiv_sub (dn.const_smul c) (dk.const_smul c),
        fderiv_const_smul dn, fderiv_const_smul dk]
      simp [mul_sub]
    have hle : (∫ x, (fderiv ℝ (c • u n - c • u k) x 1) ^ 2 +
        (fderiv ℝ (c • u n - c • u k) x Complex.I) ^ 2) ≤ ∫ x, 2 * c ^ 2 * (G n x + G k x) := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity)
        (((hGi n).add (hGi k)).const_mul _) (ae_of_all _ fun x => ?_)
      simp only [hf, hG]
      nlinarith [sq_nonneg (lineDeriv ℝ (u n) x 1 + lineDeriv ℝ (u k) x 1 - 2 * lineDeriv ℝ g x 1),
        sq_nonneg (lineDeriv ℝ (u n) x Complex.I + lineDeriv ℝ (u k) x Complex.I
          - 2 * lineDeriv ℝ g x Complex.I), sq_nonneg c,
        mul_nonneg (sq_nonneg c)
          (sq_nonneg (lineDeriv ℝ (u n) x 1 + lineDeriv ℝ (u k) x 1 - 2 * lineDeriv ℝ g x 1)),
        mul_nonneg (sq_nonneg c) (sq_nonneg (lineDeriv ℝ (u n) x Complex.I
          + lineDeriv ℝ (u k) x Complex.I - 2 * lineDeriv ℝ g x Complex.I))]
    have hsplit : (∫ x, 2 * c ^ 2 * (G n x + G k x)) = 2 * c ^ 2 * ((∫ x, G n x) + ∫ x, G k x) := by
      rw [integral_const_mul, integral_add (hGi n) (hGi k)]
    have hpi := Real.pi_pos
    calc 2 * Real.pi * ∫ x, (fderiv ℝ (c • u n - c • u k) x 1) ^ 2 +
          (fderiv ℝ (c • u n - c • u k) x Complex.I) ^ 2
        ≤ 2 * Real.pi * (2 * c ^ 2 * ((∫ x, G n x) + ∫ x, G k x)) := by
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 4 * Real.pi * c ^ 2 * (∫ x, G n x) + 4 * Real.pi * c ^ 2 * (∫ x, G k x) := by ring
  intro ε hε
  have hlim : Tendsto (fun n => 4 * Real.pi * c ^ 2 * ∫ x, G n x) atTop (𝓝 0) := by
    simpa using hF.const_mul (4 * Real.pi * c ^ 2)
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 (ε / 2) (by positivity))
  refine ⟨N, fun n hn k hk => ?_⟩
  linarith [hbound n k, hN n hn, hN k hk]

/-- **Limit of the covariances.** If smooth compactly supported `u_n` converge uniformly to a continuous `g`, then for
every mean-zero test function `φ` the covariances of `(h^ℂ, φ)` with `(h^ℂ, Δ(-(2π)⁻¹ u_n))` converge to `∫ φ g`. -/
theorem IsWholePlaneGFF.tendsto_covariance_pairing_laplacian (h : IsWholePlaneGFF P hC hcirc)
    {g : ℂ → ℝ} {u : ℕ → ℂ → ℝ} {C : ℝ} (hg : Continuous g) (hu : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n))
    (huc : ∀ n, HasCompactSupport (u n)) (hunif : ∀ n x, |u n x - g x| ≤ C / (n + 1))
    {φ : ℂ → ℝ} (hφ : IsTestFunction univ φ) (hφ0 : ∫ x, φ x = 0) :
    Tendsto (fun n => cov[fun ω => hC ω φ, fun ω => hC ω (Δ ((-(2 * Real.pi)⁻¹) • u n)); P]) atTop
      (𝓝 (∫ x, φ x * g x)) := by
  have hφi : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hφg : Integrable fun x => φ x * g x :=
    (hφ.1.continuous.mul hg).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hφu : ∀ n, Integrable fun x => φ x * u n x := fun n =>
    (hφ.1.continuous.mul (hu n).continuous).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hcov : ∀ n, cov[fun ω => hC ω φ, fun ω => hC ω (Δ ((-(2 * Real.pi)⁻¹) • u n)); P] =
      ∫ x, φ x * u n x := by
    intro n
    rw [h.covariance_pairing_laplacian (v := (-(2 * Real.pi)⁻¹) • u n) hφ hφ0
      (contDiff_const_smul_fun _ (hu n)) (hasCompactSupport_const_smul_fun _ (huc n))]
    have e : (fun x => φ x * ((-(2 * Real.pi)⁻¹) • u n) x) =
        fun x => (-(2 * Real.pi)⁻¹) * (φ x * u n x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e, integral_const_mul]
    have hpi := Real.pi_pos
    field_simp
  simp_rw [hcov]
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => C * (∫ x, |φ x|) * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (C * ∫ x, |φ x|)
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hlim
  rw [Real.dist_eq, ← integral_sub (hφu n) hφg, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (g := fun x => |φ x| * (C / ((n : ℝ) + 1)))
    (hφi.abs.mul_const _) (ae_of_all _ fun x => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (hunif n x) (abs_nonneg _)
  · rw [integral_mul_const]
    ring

end HarmonicBalls
