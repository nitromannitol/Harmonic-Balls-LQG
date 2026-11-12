import HarmonicBalls.FirstPass.Phase2.DomainMarkovDualConstant

/-!
# Summability of the weighted variances of the dual coordinates

Let `χ` be a smooth compactly supported cutoff with `0 ≤ χ ≤ 1`, and let `(ρ k)` be mean-zero test functions vanishing
where `χ ≠ 0`, with covariance potentials `v k = outerPotential (ρ k)` and dual elements
`φ k = dualElement χ (v k) (dualConstant χ (v k))`. For nonnegative weights `w k`, if the weighted sums
`∑_{k<n} w k (v k x) ^ 2` are bounded by `M` uniformly in `n` and in `x ∈ tsupport χ` (a Bessel inequality for the
covariances of the circle averages with orthogonal outer coordinates), then
`∑_k w k G(Δ(φ k), Δ(φ k)) < ∞`.

The proof bounds each variance by `π⁻¹ ∫ |∇χ|² ((v k) ^ 2 + (c k) ^ 2)`; the gradient energy density vanishes off
`tsupport χ`, where the potentials are controlled by `M`, and the constants are controlled through their unit-circle
bound `(c k) ^ 2 ≤ (1 - avg χ)⁻² avg (χ (v k)) ^ 2`.

## Main result

* `summable_weight_mul_wholePlaneGFFCov_laplacian_dualElement`.
-/

open MeasureTheory Set Laplacian

namespace HarmonicBalls

/-- Summability of the weighted variances of the Laplacian pairings of the dual elements, under a uniform bound on the
weighted sums of the squared covariance potentials over `tsupport χ`. -/
theorem summable_weight_mul_wholePlaneGFFCov_laplacian_dualElement {ρ : ℕ → ℂ → ℝ} {w : ℕ → ℝ} {χ : ℂ → ℝ}
    {M : ℝ} (hρ : ∀ k, IsTestFunction univ (ρ k)) (h0 : ∀ k, ∫ y, ρ k y = 0) (hχ : IsTestFunction univ χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (hdisj : ∀ k x, χ x ≠ 0 → ρ k x = 0) (hw : ∀ k, 0 ≤ w k)
    (hM : ∀ n, ∀ x ∈ tsupport χ, ∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 ≤ M) :
    Summable fun k => w k *
      wholePlaneGFFCov (.pairing (Δ (dualElement χ (outerPotential (ρ k)) (dualConstant χ (outerPotential (ρ k))))))
        (.pairing (Δ (dualElement χ (outerPotential (ρ k)) (dualConstant χ (outerPotential (ρ k)))))) := by
  set E : ℂ → ℝ := fun x => (fderiv ℝ χ x 1) ^ 2 + (fderiv ℝ χ x Complex.I) ^ 2 with hE
  set K : ℝ := ((1 - Real.circleAverage χ 0 1)⁻¹) ^ 2 with hK
  set M' : ℝ := max M 0 with hM'
  have hvc : ∀ k, Continuous (outerPotential (ρ k)) := fun k =>
    (contDiff_outerPotential_of_integral_eq_zero (hρ k) (h0 k)).continuous
  have hχc : Continuous χ := hχ.1.continuous
  have hχ1' : ContDiff ℝ 1 χ := hχ.1.of_le (by simp)
  have hE0 : ∀ x, 0 ≤ E x := fun x => by positivity
  have hEsupp : ∀ x, E x ≠ 0 → x ∈ tsupport χ := by
    intro x hx
    apply support_fderiv_subset (𝕜 := ℝ)
    rw [Function.mem_support]
    intro hD
    apply hx
    simp [hE, hD]
  have hsv0 : ∀ n x, 0 ≤ ∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 := fun n x =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (sq_nonneg _)
  -- the weighted sum of the squared constants
  have hc : ∀ n, ∑ k ∈ Finset.range n, w k * dualConstant χ (outerPotential (ρ k)) ^ 2 ≤ K * M' := by
    intro n
    refine (Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (dualConstant_sq_le hχc (hvc k)) (hw k)).trans ?_
    have hci : ∀ k ∈ Finset.range n,
        CircleIntegrable (fun x => w k • (χ x * outerPotential (ρ k) x) ^ 2) 0 1 := fun k _ =>
      (show Continuous (fun x => w k • (χ x * outerPotential (ρ k) x) ^ 2) by
        have := hvc k; fun_prop).continuousOn.circleIntegrable'
    have hsum : ∑ k ∈ Finset.range n,
        w k * (K * Real.circleAverage (fun x => (χ x * outerPotential (ρ k) x) ^ 2) 0 1) =
        K * Real.circleAverage (fun x => ∑ k ∈ Finset.range n, w k • (χ x * outerPotential (ρ k) x) ^ 2) 0 1 := by
      rw [Real.circleAverage_fun_sum hci, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.circleAverage_fun_smul, smul_eq_mul]
      ring
    rw [hsum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hcont : Continuous (fun x => ∑ k ∈ Finset.range n, w k • (χ x * outerPotential (ρ k) x) ^ 2) := by
      refine continuous_finsetSum _ fun k _ => ?_
      have := hvc k
      fun_prop
    refine Real.circleAverage_mono_on_of_le_circle hcont.continuousOn.circleIntegrable' fun x _ => ?_
    simp only [smul_eq_mul]
    by_cases hx : χ x = 0
    · rw [Finset.sum_eq_zero fun k _ => by rw [hx]; ring]
      exact le_max_right _ _
    have hxs : x ∈ tsupport χ := subset_tsupport _ (Function.mem_support.mpr hx)
    have hfac : ∑ k ∈ Finset.range n, w k * (χ x * outerPotential (ρ k) x) ^ 2 =
        χ x ^ 2 * ∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hfac]
    have hχsq : χ x ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
    calc χ x ^ 2 * ∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2
        ≤ 1 * ∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 :=
          mul_le_mul_of_nonneg_right hχsq (hsv0 n x)
      _ ≤ M' := by rw [one_mul]; exact (hM n x hxs).trans (le_max_left _ _)
  -- nonnegativity and the bound of each variance
  have hG0 : ∀ k, 0 ≤ wholePlaneGFFCov
      (.pairing (Δ (dualElement χ (outerPotential (ρ k)) (dualConstant χ (outerPotential (ρ k))))))
      (.pairing (Δ (dualElement χ (outerPotential (ρ k)) (dualConstant χ (outerPotential (ρ k)))))) := by
    intro k
    rw [wholePlaneGFFCov_laplacian_dualElement_self (hρ k) (h0 k) hχ (hdisj k)]
    exact mul_nonneg (by positivity) (integral_nonneg fun x => mul_nonneg (hE0 x) (sq_nonneg _))
  have hI : ∀ k, Integrable (fun x => E x *
      (outerPotential (ρ k) x ^ 2 + dualConstant χ (outerPotential (ρ k)) ^ 2)) := fun k =>
    integrable_gradientEnergy_mul hχ1' hχ.2.1 (by have := hvc k; fun_prop)
  refine summable_of_sum_range_le (c := Real.pi⁻¹ * ((∫ x, E x * (M' + K * M'))))
    (fun k => mul_nonneg (hw k) (hG0 k)) fun n => ?_
  have hsplit : (fun x => E x * (∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 +
      ∑ k ∈ Finset.range n, w k * dualConstant χ (outerPotential (ρ k)) ^ 2)) =
      fun x => ∑ k ∈ Finset.range n, w k *
        (E x * (outerPotential (ρ k) x ^ 2 + dualConstant χ (outerPotential (ρ k)) ^ 2)) := by
    funext x
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hcont2 : Continuous (fun x => ∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 +
      ∑ k ∈ Finset.range n, w k * dualConstant χ (outerPotential (ρ k)) ^ 2) := by
    refine Continuous.add (continuous_finsetSum _ fun k _ => ?_) continuous_const
    have := hvc k
    fun_prop
  calc ∑ k ∈ Finset.range n, w k * wholePlaneGFFCov
        (.pairing (Δ (dualElement χ (outerPotential (ρ k)) (dualConstant χ (outerPotential (ρ k))))))
        (.pairing (Δ (dualElement χ (outerPotential (ρ k)) (dualConstant χ (outerPotential (ρ k))))))
      ≤ ∑ k ∈ Finset.range n, w k * (Real.pi⁻¹ * ∫ x, E x *
          (outerPotential (ρ k) x ^ 2 + dualConstant χ (outerPotential (ρ k)) ^ 2)) :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
          (wholePlaneGFFCov_laplacian_dualElement_self_le (hρ k) (h0 k) hχ (hdisj k) _) (hw k)
    _ = Real.pi⁻¹ * ∫ x, E x * (∑ k ∈ Finset.range n, w k * outerPotential (ρ k) x ^ 2 +
          ∑ k ∈ Finset.range n, w k * dualConstant χ (outerPotential (ρ k)) ^ 2) := by
        rw [hsplit, integral_finsetSum _ fun k _ => (hI k).const_mul (w k), Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul]
        ring
    _ ≤ Real.pi⁻¹ * ∫ x, E x * (M' + K * M') := by
        refine mul_le_mul_of_nonneg_left (integral_mono
          (integrable_gradientEnergy_mul hχ1' hχ.2.1 hcont2)
          (integrable_gradientEnergy_mul hχ1' hχ.2.1 continuous_const) fun x => ?_) (by positivity)
        by_cases hx : E x = 0
        · simp [hx]
        exact mul_le_mul_of_nonneg_left (add_le_add ((hM n x (hEsupp x hx)).trans (le_max_left _ _)) (hc n))
          (hE0 x)

end HarmonicBalls
