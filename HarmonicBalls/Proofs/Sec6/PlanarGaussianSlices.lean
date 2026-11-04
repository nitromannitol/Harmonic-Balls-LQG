import HarmonicBalls.Proofs.Sec6.PlanarGaussianEstimate
import HarmonicBalls.Proofs.Sec6.LaplacianConvolution

/-! # Gaussian estimates for planar coordinate slices -/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped ContDiff NNReal Topology

/-- The second derivative of a restriction to a real affine line is the
second directional derivative of the planar function. -/
theorem iteratedDeriv_two_affine_line {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (z v : ℂ) (s : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => g (z + t • v)) s =
      fderiv ℝ (fun w => fderiv ℝ g w v) (z + s • v) v := by
  have hd : ContDiff ℝ ∞ (fun w => fderiv ℝ g w v) :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hline (t : ℝ) : HasDerivAt (fun r : ℝ => z + r • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hfirst : deriv (fun t : ℝ => g (z + t • v)) =
      fun t => fderiv ℝ g (z + t • v) v := by
    funext t
    exact (((hg.differentiable (by simp)) (z + t • v)).hasFDerivAt.comp_hasDerivAt t
      (hline t)).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst]
  exact (((hd.differentiable (by simp)) (z + s • v)).hasFDerivAt.comp_hasDerivAt s
    (hline s)).deriv

/-- Second directional derivatives of smooth compactly supported functions
are uniformly continuous and bounded. -/
theorem second_directionalDeriv_uniformlyContinuous_and_bounded
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (v : ℂ) :
    UniformContinuous (fun z => fderiv ℝ (fun w => fderiv ℝ g w v) z v) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ z, |fderiv ℝ (fun w => fderiv ℝ g w v) z v| ≤ M := by
  have hd : ContDiff ℝ ∞ (fun w => fderiv ℝ g w v) :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hd2 : ContDiff ℝ ∞ (fun z => fderiv ℝ (fun w => fderiv ℝ g w v) z v) :=
    (hd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hc2 : HasCompactSupport (fun z => fderiv ℝ (fun w => fderiv ℝ g w v) z v) :=
    (hgc.fderiv_apply ℝ v).fderiv_apply ℝ v
  refine ⟨hc2.uniformContinuous_of_continuous hd2.continuous, ?_⟩
  obtain ⟨M, hM⟩ := hd2.continuous.bounded_above_of_compact_support hc2
  exact ⟨max M 0, le_max_right _ _, fun z => (by simpa [Real.norm_eq_abs] using hM z :
    |fderiv ℝ (fun w => fderiv ℝ g w v) z v| ≤ M).trans (le_max_left _ _)⟩

/-- The Gaussian difference quotients along all affine lines in a fixed unit
or subunit direction converge uniformly in the base point and line parameter. -/
theorem tendstoUniformly_gaussianQuotient_affine_lines
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : ℂ) (hv : ‖v‖ ≤ 1) :
    TendstoUniformly
      (fun (t : ℝ≥0) (p : ℂ × ℝ) => (t : ℝ)⁻¹ *
        (∫ y, g (p.1 + y • v) ∂gaussianReal p.2 t - g (p.1 + p.2 • v)))
      (fun p => fderiv ℝ (fun w => fderiv ℝ g w v) (p.1 + p.2 • v) v / 2)
      (𝓝[>] 0) := by
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨huc, M, hMnn, hM⟩ := second_directionalDeriv_uniformlyContinuous_and_bounded hg hgc v
  have hsmooth (z : ℂ) : ContDiff ℝ 2 (fun t : ℝ => g (z + t • v)) := by
    apply (hg.of_le (by norm_num)).comp
    fun_prop
  have hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (z : ℂ) (u w : ℝ),
      |u - w| < δ →
      |iteratedDeriv 2 (fun t : ℝ => g (z + t • v)) u -
        iteratedDeriv 2 (fun t : ℝ => g (z + t • v)) w| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp huc ε hε
    refine ⟨δ, hδ, fun z u w huw => ?_⟩
    rw [iteratedDeriv_two_affine_line hg, iteratedDeriv_two_affine_line hg]
    have hdist : dist (z + u • v) (z + w • v) < δ := by
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs]
      exact lt_of_le_of_lt (by nlinarith [abs_nonneg (u - w), norm_nonneg v]) huw
    have h := hδ' hdist
    rw [Real.dist_eq] at h
    exact le_of_lt h
  have h := tendstoUniformly_gaussianQuotient_family (F := fun z t => g (z + t • v))
    hsmooth hMnn (fun z t => by simpa [Real.norm_eq_abs] using hB (z + t • v))
    (fun z t => by rw [iteratedDeriv_two_affine_line hg]; exact hM _) hmod
  simpa only [iteratedDeriv_two_affine_line hg] using h

end HarmonicBalls.Section6
