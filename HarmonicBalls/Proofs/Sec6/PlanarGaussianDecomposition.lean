import HarmonicBalls.Proofs.Sec6.PlanarGaussianCoordinate

/-! # Decomposition of planar Gaussian difference quotients -/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Set Metric Laplacian
open scoped ContDiff NNReal Topology

/-- The planar Gaussian difference quotient splits into the real-coordinate
quotient averaged in the imaginary coordinate and the imaginary-coordinate
quotient. -/
theorem planarGaussian_quotient_decomposition {g : ℂ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (x y : ℝ) (t : ℝ≥0) :
    (t : ℝ)⁻¹ * ((∫ z, g z ∂planarGaussian ((x : ℂ) + (y : ℂ) * Complex.I) t) -
      g (y • Complex.I + x • (1 : ℂ))) =
    (∫ b, (t : ℝ)⁻¹ *
      ((∫ a, g (b • Complex.I + a • (1 : ℂ)) ∂gaussianReal x t) -
        g (b • Complex.I + x • (1 : ℂ))) ∂gaussianReal y t) +
    (t : ℝ)⁻¹ * ((∫ b, g (b • Complex.I + x • (1 : ℂ)) ∂gaussianReal y t) -
      g (y • Complex.I + x • (1 : ℂ))) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hgc
  have hc : Continuous (fun q : ℝ × ℝ => g (q.2 • Complex.I + q.1 • (1 : ℂ))) := by
    fun_prop
  have hi : Integrable (fun q : ℝ × ℝ => g (q.2 • Complex.I + q.1 • (1 : ℂ)))
      ((gaussianReal x t).prod (gaussianReal y t)) := by
    apply Integrable.of_bound hc.aestronglyMeasurable B
    exact Filter.Eventually.of_forall (fun q => hB _)
  have hb : Integrable (fun b : ℝ => g (b • Complex.I + x • (1 : ℂ)))
      (gaussianReal y t) := by
    apply Integrable.of_bound (by fun_prop) B
    exact Filter.Eventually.of_forall (fun b => hB _)
  have hprod : (∫ z, g z ∂planarGaussian ((x : ℂ) + (y : ℂ) * Complex.I) t) =
      ∫ b, ∫ a, g (b • Complex.I + a • (1 : ℂ))
        ∂gaussianReal x t ∂gaussianReal y t := by
    simpa only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      zero_mul, zero_add, add_zero, sub_zero, Algebra.smul_def, Complex.coe_algebraMap,
      add_comm] using integral_planarGaussian_eq_iterated hg hgc ((x : ℂ) + (y : ℂ) * Complex.I) t
  rw [hprod, integral_const_mul, integral_sub hi.integral_prod_right hb]
  ring

/-- The planar Gaussian difference quotient converges uniformly to one half of
the Laplacian for smooth compactly supported functions. -/
theorem tendstoUniformly_planarGaussian_quotient
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    TendstoUniformly
      (fun (t : ℝ≥0) (z : ℂ) => (t : ℝ)⁻¹ *
        ((∫ w, g w ∂planarGaussian z t) - g z))
      (fun z => Δ g z / 2) (𝓝[>] 0) := by
  have ha := tendstoUniformly_averaged_realCoordinate_quotient hg hgc
  have hb := tendstoUniformly_averaged_realSecondDeriv hg hgc
  have hc : TendstoUniformly
      (fun (t : ℝ≥0) (p : ℝ × ℝ) => (t : ℝ)⁻¹ *
        ((∫ b, g (b • Complex.I + p.1 • (1 : ℂ)) ∂gaussianReal p.2 t) -
          g (p.2 • Complex.I + p.1 • (1 : ℂ))))
      (fun p => fderiv ℝ (fun w => fderiv ℝ g w Complex.I)
        (p.2 • Complex.I + p.1 • (1 : ℂ)) Complex.I / 2) (𝓝[>] 0) := by
    have h := Metric.tendstoUniformly_iff.mp
      (tendstoUniformly_gaussianQuotient_affine_lines hg hgc Complex.I (by simp))
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [h ε hε] with t ht
    rintro ⟨x, y⟩
    simpa only [add_comm] using ht (x • (1 : ℂ), y)
  have hsum := (ha.add hb).add hc
  have hpair : TendstoUniformly
      (fun (t : ℝ≥0) (p : ℝ × ℝ) => (t : ℝ)⁻¹ *
        ((∫ w, g w ∂planarGaussian ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) t) -
          g (p.2 • Complex.I + p.1 • (1 : ℂ))))
      (fun p => Δ g (p.2 • Complex.I + p.1 • (1 : ℂ)) / 2) (𝓝[>] 0) := by
    have hh := hsum
    convert hh using 1
    · funext t p
      simp only [Pi.add_apply, sub_add_cancel]
      exact planarGaussian_quotient_decomposition hg.continuous hgc p.1 p.2 t
    · funext p
      simp only [Pi.add_apply, zero_add]
      rw [HarmonicBalls.laplacian_eq_fderiv_fderiv (hg.of_le (by norm_num))]
      ring
  have hh := hpair.comp (fun z : ℂ => (z.re, z.im))
  convert hh using 1
  · funext t z
    simp only [Function.comp_apply, Algebra.smul_def, Complex.coe_algebraMap, mul_one]
    rw [add_comm ((z.im : ℂ) * Complex.I), Complex.re_add_im]
  · funext z
    simp only [Function.comp_apply, Algebra.smul_def, Complex.coe_algebraMap, mul_one]
    rw [add_comm ((z.im : ℂ) * Complex.I), Complex.re_add_im]

end HarmonicBalls.Section6
