import HarmonicBalls.Proofs.Sec6.PlanarGaussianProduct

/-! # Uniform convergence of the averaged coordinate quotient -/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped ContDiff NNReal Topology

/-- After averaging in the imaginary coordinate, the real-coordinate Gaussian
quotient still converges uniformly to the averaged second derivative. -/
theorem tendstoUniformly_averaged_realCoordinate_quotient
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    TendstoUniformly
      (fun (t : ℝ≥0) (p : ℝ × ℝ) =>
        (∫ b, (t : ℝ)⁻¹ *
          ((∫ a, g (b • Complex.I + a • (1 : ℂ)) ∂gaussianReal p.1 t) -
            g (b • Complex.I + p.1 • (1 : ℂ))) ∂gaussianReal p.2 t) -
        ∫ b, fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ))
          (b • Complex.I + p.1 • (1 : ℂ)) (1 : ℂ) / 2 ∂gaussianReal p.2 t)
      (fun _ => 0) (𝓝[>] 0) := by
  obtain ⟨B, hB⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨_, M, _, hM⟩ :=
    second_directionalDeriv_uniformlyContinuous_and_bounded hg hgc (1 : ℂ)
  have hd : ContDiff ℝ ∞ (fun w => fderiv ℝ g w (1 : ℂ)) :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hd2 : ContDiff ℝ ∞ (fun z =>
      fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ)) z (1 : ℂ)) :=
    (hd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  apply tendstoUniformly_integral_sub_of_tendstoUniformly (𝓝[>] 0)
    (fun t (p : ℝ × ℝ) => gaussianReal p.2 t) (fun _ _ => inferInstance)
    (fun t (q : (ℝ × ℝ) × ℝ) => (t : ℝ)⁻¹ *
      ((∫ a, g (q.2 • Complex.I + a • (1 : ℂ)) ∂gaussianReal q.1.1 t) -
        g (q.2 • Complex.I + q.1.1 • (1 : ℂ))))
    (fun (q : (ℝ × ℝ) × ℝ) => fderiv ℝ
      (fun w => fderiv ℝ g w (1 : ℂ)) (q.2 • Complex.I + q.1.1 • (1 : ℂ))
      (1 : ℂ) / 2)
  · intro t p
    have hc : Continuous (fun q : ℝ × ℝ =>
        g (q.2 • Complex.I + q.1 • (1 : ℂ))) := by fun_prop
    have hi : Integrable (fun q : ℝ × ℝ =>
        g (q.2 • Complex.I + q.1 • (1 : ℂ)))
        ((gaussianReal p.1 t).prod (gaussianReal p.2 t)) := by
      apply Integrable.of_bound hc.aestronglyMeasurable B
      exact Filter.Eventually.of_forall (fun q => hB _)
    have hb : Integrable (fun b : ℝ => g (b • Complex.I + p.1 • (1 : ℂ)))
        (gaussianReal p.2 t) := by
      apply Integrable.of_bound (by fun_prop) B
      exact Filter.Eventually.of_forall (fun b => hB _)
    exact (hi.integral_prod_right.sub hb).const_mul _
  · intro t p
    apply Integrable.of_bound (by fun_prop) (M / 2)
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (hM _) (by norm_num)
  · have h := Metric.tendstoUniformly_iff.mp
      (tendstoUniformly_gaussianQuotient_affine_lines hg hgc (1 : ℂ) (by simp))
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [h ε hε] with t ht
    rintro ⟨⟨x, y⟩, b⟩
    exact ht (b • Complex.I, x)

/-- Averaging the real second derivative in the imaginary direction converges
uniformly to that derivative at the centre of the Gaussian. -/
theorem tendstoUniformly_averaged_realSecondDeriv
    {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    TendstoUniformly
      (fun (t : ℝ≥0) (p : ℝ × ℝ) =>
        ∫ b, fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ))
          (b • Complex.I + p.1 • (1 : ℂ)) (1 : ℂ) / 2 ∂gaussianReal p.2 t)
      (fun p => fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ))
        (p.2 • Complex.I + p.1 • (1 : ℂ)) (1 : ℂ) / 2) (𝓝[>] 0) := by
  let d : ℂ → ℝ := fun z => fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ)) z (1 : ℂ)
  have hd : ContDiff ℝ ∞ d := by
    dsimp [d]
    exact (((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hc : HasCompactSupport d := (hgc.fderiv_apply ℝ (1 : ℂ)).fderiv_apply ℝ (1 : ℂ)
  have h := Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_gaussianAverage_affine_lines hd hc Complex.I (by simp))
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [h (2 * ε) (by positivity)] with t ht
  intro ⟨x, y⟩
  have hh := ht (x • (1 : ℂ), y)
  rw [Real.dist_eq] at hh ⊢
  simp only [integral_div, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simp only [add_comm] at hh
  dsimp [d] at hh
  have hh' : |fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ))
        (y • Complex.I + x • (1 : ℂ)) (1 : ℂ) -
      ∫ b, fderiv ℝ (fun w => fderiv ℝ g w (1 : ℂ))
        (b • Complex.I + x • (1 : ℂ)) (1 : ℂ) ∂gaussianReal y t| < 2 * ε := by
    simpa only [Algebra.smul_def, Complex.coe_algebraMap] using hh
  linarith

end HarmonicBalls.Section6
