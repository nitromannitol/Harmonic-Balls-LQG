import HarmonicBalls.FirstPass.S11i.DilationMixing
import HarmonicBalls.Defs.GFF

/-!
# Step 8 helper: dilation invariance of the covariance of mean-zero pairings (owner n3)

Source: corrected paper, `s11-pinch:lem:mixing` (tex lines 3769-3812), covariance step (C6 part). For test
functions `φ, ψ` with `∫ φ = 0 = ∫ ψ` and `n : ℕ`, with `κₙ` the dilation `dilateTest n`,

  `Cov((h, κₙ φ), (h, κₙ ψ)) = Cov((h, φ), (h, ψ))`  for the whole-plane kernel `wholePlaneCov`.

Proof (no Fubini on the outer step): `κₙ` is a change of variables (`integral_dilateTest_mul`). Off the diagonal
the kernel changes under `x ↦ c • x` (`c = 2⁻ⁿ`) by `g(x) + g(z) - log c`, where `g(x) = log max(c‖x‖,1) -
log max(‖x‖,1)`. The one-variable terms integrate to zero against a mean-zero test function.
-/

open MeasureTheory Filter Topology Metric Set

namespace HarmonicBalls

/-- Off the diagonal, `wholePlaneCov x z = log max(‖x‖,1) + log max(‖z‖,1) - log ‖z - x‖`. -/
theorem wholePlaneCov_eq_log_of_ne {x z : ℂ} (h : x ≠ z) :
    wholePlaneCov x z = Real.log (max ‖x‖ 1) + Real.log (max ‖z‖ 1) - Real.log ‖z - x‖ := by
  have hx : (0 : ℝ) < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hz : (0 : ℝ) < max ‖z‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hd : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 h.symm)
  unfold wholePlaneCov
  rw [norm_sub_rev x z, Real.log_div (mul_pos hx hz).ne' hd.ne', Real.log_mul hx.ne' hz.ne']

/-- The one-variable gap `g_c(x) = log max(c‖x‖,1) - log max(‖x‖,1)` produced by the dilation `x ↦ c • x`. -/
noncomputable def dilationGap (c : ℝ) (x : ℂ) : ℝ :=
  Real.log (max (c * ‖x‖) 1) - Real.log (max ‖x‖ 1)

/-- Off the diagonal, dilation by `c > 0` shifts the kernel by `g_c(x) + g_c(z) - log c`. -/
theorem wholePlaneCov_smul_of_ne {c : ℝ} (hc : 0 < c) {x z : ℂ} (h : x ≠ z) :
    wholePlaneCov (c • x) (c • z) = wholePlaneCov x z + dilationGap c x + dilationGap c z - Real.log c := by
  have hne : c • x ≠ c • z := fun e => h (smul_right_injective ℂ hc.ne' e)
  have e1 : ‖c • x‖ = c * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg hc.le]
  have e2 : ‖c • z‖ = c * ‖z‖ := by rw [norm_smul, Real.norm_of_nonneg hc.le]
  have e3 : ‖c • z - c • x‖ = c * ‖z - x‖ := by
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hc.le]
  have hd : 0 < ‖z - x‖ := norm_pos_iff.2 (sub_ne_zero.2 h.symm)
  rw [wholePlaneCov_eq_log_of_ne hne, wholePlaneCov_eq_log_of_ne h, e1, e2, e3, Real.log_mul hc.ne' hd.ne']
  unfold dilationGap
  ring

/-- Continuity of the gap `g_c` for `c > 0`. -/
theorem continuous_dilationGap (c : ℝ) : Continuous (dilationGap c) := by
  have h1 : Continuous fun x : ℂ => Real.log (max (c * ‖x‖) 1) :=
    Continuous.log ((continuous_const.mul continuous_norm).max continuous_const)
      (fun x => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne')
  have h2 : Continuous fun x : ℂ => Real.log (max ‖x‖ 1) :=
    Continuous.log (continuous_norm.max continuous_const)
      (fun x => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne')
  exact h1.sub h2

/-- The whole-plane kernel is integrable against a test function, for every fixed centre `x`
(the kernel is `log`-singular at `x` only, a null set). -/
theorem integrable_mul_wholePlaneCov_dil {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ) (x : ℂ) :
    Integrable (fun z => ψ z * wholePlaneCov x z) := by
  obtain ⟨R, hR⟩ := (hψ.2.1.isCompact.isBounded).subset_closedBall (0 : ℂ)
  have hsupp : ∀ z, ψ z ≠ 0 → ‖z‖ ≤ R := fun z hz =>
    mem_closedBall_zero_iff.1 (hR (subset_tsupport ψ (Function.mem_support.2 hz)))
  have hb : Continuous fun z : ℂ => Real.log (max ‖z‖ 1) :=
    Continuous.log (continuous_norm.max continuous_const)
      (fun z => (lt_of_lt_of_le one_pos (le_max_right _ _)).ne')
  have h1 : Integrable (fun z => ψ z * Real.log (max ‖x‖ 1)) :=
    (integrable_of_isTestFunction hψ).mul_const _
  have h2 : Integrable (fun z => ψ z * Real.log (max ‖z‖ 1)) :=
    (hψ.1.continuous.mul hb).integrable_of_hasCompactSupport hψ.2.1.mul_right
  have h3 : Integrable (fun z => ψ z * Real.log ‖z - x‖) := integrable_mul_log_norm_sub hψ hsupp x
  refine ((h1.add h2).sub h3).congr ?_
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ x := compl_mem_ae_iff.2 (measure_singleton x)
  filter_upwards [hae] with z hz
  simp only [Pi.add_apply, Pi.sub_apply, wholePlaneCov_eq_log_of_ne hz.symm]
  ring

/-- Pointwise dilation identity for a mean-zero test function `ψ`: for every `w`,
`∫ ψ(z) Cov(c w, c z) dz = ∫ ψ(z) Cov(w, z) dz + ∫ ψ(z) g_c(z) dz`
(the one-variable term `(g_c(w) - log c) ∫ ψ` vanishes). -/
theorem integral_dilate_wholePlaneCov {c : ℝ} (hc : 0 < c) {ψ : ℂ → ℝ} (hψ : IsTestFunction univ ψ)
    (hψ0 : ∫ z, ψ z = 0) (w : ℂ) :
    ∫ z, ψ z * wholePlaneCov (c • w) (c • z) =
      (∫ z, ψ z * wholePlaneCov w z) + ∫ z, ψ z * dilationGap c z := by
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ w := compl_mem_ae_iff.2 (measure_singleton w)
  have hg : Integrable (fun z => ψ z * dilationGap c z) :=
    (hψ.1.continuous.mul (continuous_dilationGap c)).integrable_of_hasCompactSupport hψ.2.1.mul_right
  have hconst : Integrable (fun z => (dilationGap c w - Real.log c) * ψ z) :=
    (integrable_of_isTestFunction hψ).const_mul _
  have e : (fun z => ψ z * wholePlaneCov (c • w) (c • z)) =ᵐ[volume]
      (fun z => ψ z * wholePlaneCov w z + ((dilationGap c w - Real.log c) * ψ z + ψ z * dilationGap c z)) := by
    filter_upwards [hae] with z hz
    rw [wholePlaneCov_smul_of_ne hc hz.symm]
    ring
  have hconst' : Integrable (fun z => (dilationGap c w - Real.log c) * ψ z + ψ z * dilationGap c z) :=
    hconst.add hg
  rw [integral_congr_ae e, integral_add (integrable_mul_wholePlaneCov_dil hψ w) hconst',
    integral_add hconst hg, integral_const_mul, hψ0, mul_zero, zero_add]

/-- Covariance invariance under dilation (paper `lem:mixing`, covariance step): for mean-zero test functions
`φ, ψ` and every `n : ℕ`, `Cov((h, κₙφ), (h, κₙψ)) = Cov((h, φ), (h, ψ))` for the whole-plane kernel, with
`κₙ = dilateTest n`. No condition on the dilation index is needed. -/
theorem wholePlaneGFFCov_pairing_dilate {φ ψ : ℂ → ℝ} (hφ : IsTestFunction univ φ)
    (hψ : IsTestFunction univ ψ) (hφ0 : ∫ x, φ x = 0) (hψ0 : ∫ z, ψ z = 0) (n : ℕ) :
    wholePlaneGFFCov (GFFObservable.pairing (dilateTest n φ)) (GFFObservable.pairing (dilateTest n ψ)) =
      wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing ψ) := by
  set c : ℝ := ((2 : ℝ) ^ n)⁻¹ with hc_def
  have hc : 0 < c := by rw [hc_def]; positivity
  have hA : ∀ x : ℂ, ∫ y, dilateTest n ψ y * wholePlaneCov x y =
      ∫ z, ψ z * wholePlaneCov x (c • z) :=
    fun x => integral_dilateTest_mul n ψ (fun y => wholePlaneCov x y)
  have hK : ∀ w : ℂ, (∫ z, ψ z * wholePlaneCov (c • w) (c • z)) =
      (∫ z, ψ z * wholePlaneCov w z) + ∫ z, ψ z * dilationGap c z :=
    fun w => integral_dilate_wholePlaneCov hc hψ hψ0 w
  have hL : wholePlaneGFFCov (GFFObservable.pairing (dilateTest n φ))
      (GFFObservable.pairing (dilateTest n ψ)) =
      ∫ w, φ w * ∫ z, ψ z * wholePlaneCov (c • w) (c • z) := by
    show ∫ x, dilateTest n φ x * ∫ y, dilateTest n ψ y * wholePlaneCov x y = _
    simp_rw [hA]
    exact integral_dilateTest_mul n φ (fun x => ∫ z, ψ z * wholePlaneCov x (c • z))
  have hR : wholePlaneGFFCov (GFFObservable.pairing φ) (GFFObservable.pairing ψ) =
      ∫ w, φ w * ∫ z, ψ z * wholePlaneCov w z := rfl
  rw [hL, hR]
  set K : ℝ := ∫ z, ψ z * dilationGap c z with hK_def
  have hpt : ∀ w : ℂ, φ w * ∫ z, ψ z * wholePlaneCov (c • w) (c • z) =
      φ w * (∫ z, ψ z * wholePlaneCov w z) + K * φ w := fun w => by rw [hK w]; ring
  have hfun : (fun w => φ w * ∫ z, ψ z * wholePlaneCov (c • w) (c • z)) =
      fun w => φ w * (∫ z, ψ z * wholePlaneCov w z) + K * φ w := funext hpt
  have hKφ : Integrable (fun w => K * φ w) := (integrable_of_isTestFunction hφ).const_mul K
  by_cases hI : Integrable (fun w => φ w * ∫ z, ψ z * wholePlaneCov w z)
  · rw [hfun, integral_add hI hKφ, integral_const_mul, hφ0, mul_zero, add_zero]
  · have hI' : ¬ Integrable (fun w => φ w * ∫ z, ψ z * wholePlaneCov (c • w) (c • z)) := by
      intro h
      apply hI
      refine (h.sub hKφ).congr (Filter.Eventually.of_forall fun w => ?_)
      show φ w * (∫ z, ψ z * wholePlaneCov (c • w) (c • z)) - K * φ w = φ w * (∫ z, ψ z * wholePlaneCov w z)
      rw [hpt w]
      ring
    rw [integral_undef hI, integral_undef hI']

end HarmonicBalls
