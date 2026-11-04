import HarmonicBalls.Proofs.Sec6.PlanarGaussianSlices

/-! # Uniform convergence of planar Gaussian coordinate averages -/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped ContDiff NNReal Topology

/-- Gaussian averaging along parallel lines converges uniformly to the original
smooth compactly supported function. -/
theorem tendstoUniformly_gaussianAverage_affine_lines
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (v : ℂ) (hv : ‖v‖ ≤ 1) :
    TendstoUniformly
      (fun (t : ℝ≥0) (p : ℂ × ℝ) =>
        ∫ y, g (p.1 + y • v) ∂gaussianReal p.2 t)
      (fun p => g (p.1 + p.2 • v)) (𝓝[>] 0) := by
  obtain ⟨_, M, hMnn, hM⟩ :=
    second_directionalDeriv_uniformlyContinuous_and_bounded hg hgc v
  have hq := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_gaussianQuotient_affine_lines hg hgc v hv) 1 zero_lt_one
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hsmall : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, (t : ℝ) < ε / (M + 1) := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < ε / (M + 1)} :=
      isOpen_lt NNReal.continuous_coe continuous_const
    have hmem : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ) < ε / (M + 1)} := by
      simpa using div_pos hε (by linarith : 0 < M + 1)
    exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hq, hsmall, self_mem_nhdsWithin] with t hq ht htpos
  intro p
  have htp : (0 : ℝ) < t := NNReal.coe_pos.mpr htpos
  have hq' := hq p
  rw [Real.dist_eq] at hq' ⊢
  have hhalf : |fderiv ℝ (fun w => fderiv ℝ g w v) (p.1 + p.2 • v) v / 2| ≤ M / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (hM _) (by norm_num)
  have hquot : |(t : ℝ)⁻¹ *
      (∫ y, g (p.1 + y • v) ∂gaussianReal p.2 t - g (p.1 + p.2 • v))| < M + 1 := by
    have := abs_sub_lt_iff.mp hq'
    have := abs_le.mp hhalf
    rw [abs_lt]
    constructor <;> linarith
  have hid : (∫ y, g (p.1 + y • v) ∂gaussianReal p.2 t - g (p.1 + p.2 • v)) =
      (t : ℝ) * ((t : ℝ)⁻¹ *
      (∫ y, g (p.1 + y • v) ∂gaussianReal p.2 t - g (p.1 + p.2 • v))) := by
    field_simp
  rw [abs_sub_comm, hid, abs_mul, abs_of_pos htp]
  have hmul := mul_lt_mul_of_pos_left hquot htp
  have hsmall' : (t : ℝ) * (M + 1) < ε := by
    exact (lt_div_iff₀ (by linarith : 0 < M + 1)).mp ht
  exact lt_trans hmul hsmall'

end HarmonicBalls.Section6
