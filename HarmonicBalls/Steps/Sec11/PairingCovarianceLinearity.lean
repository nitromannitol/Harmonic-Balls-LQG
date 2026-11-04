import HarmonicBalls.Proofs.Sec8.CircleDensityDoubleLog
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma

/-! # Linearity of GFF pairing covariances

The logarithmic covariance is bilinear on test functions. The imported Section 8
argument uses Leonardo Bonanno's LatticeProb formalization of the ergodic theorem.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- The whole-plane covariance potential of a compactly supported continuous
function is continuous, without a normalization on its integral. -/
theorem continuous_wholePlaneCov_potential_general {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (fun x => ∫ y, g y * wholePlaneCov x y) := by
  have heq : (fun x => ∫ y, g y * wholePlaneCov x y) =
      fun x => (∫ y, g y) * wholePlaneNormalization x +
        (∫ y, g y * wholePlaneNormalization y) -
          ∫ y, g y * Real.log ‖y - x‖ := by
    funext x
    have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
    have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
      (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
    have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
      have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
        ).integrable_smul_right_of_hasCompactSupport hg hgc
      simpa only [smul_eq_mul, mul_comm] using h
    have heq : (∫ y, g y * wholePlaneCov x y) =
        ∫ y, (g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) -
          g y * Real.log ‖y - x‖ := by
      apply integral_congr_ae
      filter_upwards [ae_ne_complex x] with y hy
      have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
      have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
      rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy',
        norm_sub_rev]
      simp only [wholePlaneNormalization]
      ring
    have hsum : (∫ y, g y * wholePlaneNormalization x + g y * wholePlaneNormalization y) =
        (∫ y, g y * wholePlaneNormalization x) + ∫ y, g y * wholePlaneNormalization y :=
      integral_add (hgi.mul_const _) hni
    have hai : Integrable (fun y => g y * wholePlaneNormalization x +
        g y * wholePlaneNormalization y) := (hgi.mul_const _).add hni
    rw [heq, integral_sub hai hli, hsum, integral_mul_const]
  rw [heq]
  exact ((continuous_const.mul continuous_wholePlaneNormalization).add continuous_const).sub
    (continuous_log_potential_of_compact_support hg hgc)

/-- Covariance is linear in its first test function. -/
theorem wholePlaneGFFCov_pairing_linear_left {φ ψ χ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hχ : IsTestFunction univ χ) (a b : ℝ) :
    wholePlaneGFFCov (.pairing (fun x => a * φ x + b * ψ x)) (.pairing χ) =
      a * wholePlaneGFFCov (.pairing φ) (.pairing χ) +
        b * wholePlaneGFFCov (.pairing ψ) (.pairing χ) := by
  let p : ℂ → ℝ := fun x => ∫ y, χ y * wholePlaneCov x y
  have hp : Continuous p := continuous_wholePlaneCov_potential_general hχ.1.continuous hχ.2.1
  have hφp : Integrable (fun x => φ x * p x) :=
    (hφ.1.continuous.mul hp).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hψp : Integrable (fun x => ψ x * p x) :=
    (hψ.1.continuous.mul hp).integrable_of_hasCompactSupport hψ.2.1.mul_right
  change (∫ x, (a * φ x + b * ψ x) * p x) =
    a * (∫ x, φ x * p x) + b * (∫ x, ψ x * p x)
  have heq : (fun x => (a * φ x + b * ψ x) * p x) =
      fun x => a * (φ x * p x) + b * (ψ x * p x) := by
    funext x
    ring
  rw [heq, integral_add (hφp.const_mul a) (hψp.const_mul b), integral_const_mul,
    integral_const_mul]

/-- Covariance is linear in its second test function. -/
theorem wholePlaneGFFCov_pairing_linear_right {φ ψ χ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hχ : IsTestFunction univ χ) (a b : ℝ) :
    wholePlaneGFFCov (.pairing χ) (.pairing (fun x => a * φ x + b * ψ x)) =
      a * wholePlaneGFFCov (.pairing χ) (.pairing φ) +
        b * wholePlaneGFFCov (.pairing χ) (.pairing ψ) := by
  let p : ℂ → ℝ := fun x => ∫ y, φ y * wholePlaneCov x y
  let q : ℂ → ℝ := fun x => ∫ y, ψ y * wholePlaneCov x y
  have hp : Continuous p := continuous_wholePlaneCov_potential_general hφ.1.continuous hφ.2.1
  have hq : Continuous q := continuous_wholePlaneCov_potential_general hψ.1.continuous hψ.2.1
  have hχp : Integrable (fun x => χ x * p x) :=
    (hχ.1.continuous.mul hp).integrable_of_hasCompactSupport hχ.2.1.mul_right
  have hχq : Integrable (fun x => χ x * q x) :=
    (hχ.1.continuous.mul hq).integrable_of_hasCompactSupport hχ.2.1.mul_right
  have hinner (x : ℂ) : (∫ y, (a * φ y + b * ψ y) * wholePlaneCov x y) =
      a * p x + b * q x := by
    have heq : (fun y => (a * φ y + b * ψ y) * wholePlaneCov x y) =
        fun y => a * (φ y * wholePlaneCov x y) + b * (ψ y * wholePlaneCov x y) := by
      funext y
      ring
    rw [heq, integral_add ((integrable_mul_wholePlaneCov hφ.1.continuous hφ.2.1 x).const_mul a)
      ((integrable_mul_wholePlaneCov hψ.1.continuous hψ.2.1 x).const_mul b),
      integral_const_mul, integral_const_mul]
  change (∫ x, χ x * (∫ y, (a * φ y + b * ψ y) * wholePlaneCov x y)) =
    a * (∫ x, χ x * p x) + b * (∫ x, χ x * q x)
  simp_rw [hinner]
  have heq : (fun x => χ x * (a * p x + b * q x)) =
      fun x => a * (χ x * p x) + b * (χ x * q x) := by
    funext x
    ring
  rw [heq, integral_add (hχp.const_mul a) (hχq.const_mul b), integral_const_mul,
    integral_const_mul]

/-- For each fixed pair of tests and fixed coefficients, GFF pairings obey
linearity almost surely. The exceptional null set may depend on the tests and
coefficients. -/
theorem IsWholePlaneGFF.ae_pairing_linear_combination
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) (a b : ℝ) :
    ∀ᵐ ω ∂P, hC ω (fun x => a * φ x + b * ψ x) = a * hC ω φ + b * hC ω ψ := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let θ : ℂ → ℝ := fun x => a * φ x + b * ψ x
  have hθ : IsTestFunction univ θ := hφ.const_mul_add_const_mul hψ a b
  let X : Ω → ℝ := fun ω => hC ω φ
  let Y : Ω → ℝ := fun ω => hC ω ψ
  let Z : Ω → ℝ := fun ω => hC ω θ
  have hX : MemLp X 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing φ, hφ⟩).memLp (by simp)
  have hY : MemLp Y 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing ψ, hψ⟩).memLp (by simp)
  have hZ : MemLp Z 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing θ, hθ⟩).memLp (by simp)
  have hA : MemLp (a • X) 2 P := hX.const_smul a
  have hB : MemLp (b • Y) 2 P := hY.const_smul b
  have hErr : MemLp (Z - (a • X + b • Y)) 2 P := hZ.sub (hA.add hB)
  have hmeanX : ∫ ω, X ω ∂P = 0 := h.integral_eq_zero (.pairing φ) hφ
  have hmeanY : ∫ ω, Y ω ∂P = 0 := h.integral_eq_zero (.pairing ψ) hψ
  have hmeanZ : ∫ ω, Z ω ∂P = 0 := h.integral_eq_zero (.pairing θ) hθ
  have hmean : ∫ ω, (Z - (a • X + b • Y)) ω ∂P = 0 := by
    change (∫ ω, Z ω - (a * X ω + b * Y ω) ∂P) = 0
    have hiX := (hX.integrable (by simp)).const_mul a
    have hiY := (hY.integrable (by simp)).const_mul b
    have hs : Integrable (fun ω => a * X ω + b * Y ω) P := hiX.add hiY
    rw [integral_sub (hZ.integrable (by simp)) hs,
      integral_add hiX hiY, integral_const_mul, integral_const_mul,
      hmeanX, hmeanY, hmeanZ, mul_zero, mul_zero, add_zero, sub_zero]
  have hcov (f g : ℂ → ℝ) (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
      cov[fun ω => hC ω f, fun ω => hC ω g; P] =
        wholePlaneGFFCov (.pairing f) (.pairing g) := by
    simpa only [GFFObservable.eval] using h.covariance_eq (.pairing f) (.pairing g) hf hg
  have hv : variance (Z - (a • X + b • Y)) P = 0 := by
    rw [variance_sub hZ (hA.add hB), variance_add hA hB,
      covariance_add_right hZ hA hB, variance_smul, variance_smul,
      covariance_smul_right, covariance_smul_right, covariance_smul_left,
      covariance_smul_right, ← covariance_self hZ.aemeasurable,
      ← covariance_self hX.aemeasurable, ← covariance_self hY.aemeasurable]
    rw [hcov θ θ hθ hθ]
    rw [hcov θ φ hθ hφ, hcov θ ψ hθ hψ, hcov φ φ hφ hφ,
      hcov φ ψ hφ hψ, hcov ψ ψ hψ hψ]
    dsimp [θ]
    rw [wholePlaneGFFCov_pairing_linear_left hφ hψ hθ a b,
      wholePlaneGFFCov_pairing_linear_right hφ hψ hφ a b,
      wholePlaneGFFCov_pairing_linear_right hφ hψ hψ a b,
      wholePlaneGFFCov_pairing_linear_left hφ hψ hφ a b,
      wholePlaneGFFCov_pairing_linear_left hφ hψ hψ a b]
    have hcomm : wholePlaneGFFCov (.pairing ψ) (.pairing φ) =
        wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
      rw [← hcov ψ φ hψ hφ, ← hcov φ ψ hφ hψ, covariance_comm]
    rw [hcomm]
    ring
  have he := ae_eq_integral_of_variance_eq_zero hErr hv
  filter_upwards [he] with ω he
  rw [hmean] at he
  change hC ω θ - (a * hC ω φ + b * hC ω ψ) = 0 at he
  exact sub_eq_zero.mp he

/-- Reference centering agrees almost surely with subtracting the reference
pairing for each fixed local test function. -/
theorem IsWholePlaneGFF.ae_centeredTestPairing_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {U : Set ℂ} {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction U φ) (hψ : IsTestFunction U ψ) :
    ∀ᵐ ω ∂P, centeredTestPairing (hC ω) ψ φ =
      hC ω φ - (∫ x, φ x) * hC ω ψ := by
  have he := h.ae_pairing_linear_combination (hφ.mono_set (subset_univ _))
    (hψ.mono_set (subset_univ _)) 1 (-(∫ x, φ x))
  filter_upwards [he] with ω he
  unfold centeredTestPairing
  rw [he]
  ring

/-- Reference centering holds on a common full-measure set for every test in a
countable family. No simultaneous assertion over all tests is made. -/
theorem IsWholePlaneGFF.ae_centeredTestPairing_eq_countable
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {U : Set ℂ} (φ : ι → ℂ → ℝ) {ψ : ℂ → ℝ}
    (hφ : ∀ i, IsTestFunction U (φ i)) (hψ : IsTestFunction U ψ) :
    ∀ᵐ ω ∂P, ∀ i, centeredTestPairing (hC ω) ψ (φ i) =
      hC ω (φ i) - (∫ x, φ i x) * hC ω ψ := by
  exact ae_all_iff.mpr (fun i => h.ae_centeredTestPairing_eq (hφ i) hψ)

#print axioms continuous_wholePlaneCov_potential_general
#print axioms wholePlaneGFFCov_pairing_linear_left
#print axioms wholePlaneGFFCov_pairing_linear_right
#print axioms IsWholePlaneGFF.ae_pairing_linear_combination
#print axioms IsWholePlaneGFF.ae_centeredTestPairing_eq_countable

end HarmonicBalls
