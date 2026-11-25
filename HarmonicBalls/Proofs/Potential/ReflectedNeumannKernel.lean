import HarmonicBalls.Proofs.Potential.ReflectedGreenPotentialBound

/-!
# The Neumann heat kernel of reflected Brownian motion in the unit square

The law at time `s > 0` of reflected Brownian motion in `[0, 1]` started at `u` is the image of
the Gaussian law `N(u, s)` under the triangle wave `unitIntervalFold`; on `[0, 1]` it has the
density, with respect to Lebesgue measure, given by the method of images
`q_s(u, v) = ∑_{n ∈ ℤ} (φ_s(v + 2n - u) + φ_s(2n - v - u))`, `φ_s` the centred Gaussian density
of variance `s` (`intervalNeumannKernel`, `lintegral_gaussianReal_unitIntervalFold`). Reflected
Brownian motion in the unit square is the product of two such motions, so its law at time `s` from
`x` has the density `k_s(x, y) = q_s(x₁, y₁) q_s(x₂, y₂)` on `K₀ = closedSquare 0 1`
(`squareNeumannKernel`, `lintegral_reflected_eval_eq_neumannKernel`). This is the Neumann heat
kernel of the square (the reflection of the Gaussian kernel in the sides). It is symmetric in
`(x, y)`, positive, and jointly continuous in `(s, x, y)` for `s > 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-! ### The triangle wave as a sum over the cells -/

/-- **The triangle wave cell by cell**: for every `w`, exactly one of the cells `[2n, 2n + 1)`
(where `unitIntervalFold w = w - 2n`) and `[2n - 1, 2n)` (where `unitIntervalFold w = 2n - w`)
contains `w`. -/
theorem unitIntervalFold_eq_tsum_indicator (ψ : ℝ → ℝ≥0∞) (w : ℝ) :
    ψ (unitIntervalFold w) = ∑' n : ℤ, ((Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) +
      (Ioc (0 : ℝ) 1).indicator ψ (2 * n - w)) := by
  set n₀ : ℤ := ⌊w / 2⌋ with hn₀
  have h1 : (n₀ : ℝ) ≤ w / 2 := Int.floor_le _
  have h2 : w / 2 < n₀ + 1 := Int.lt_floor_add_one _
  have hfold : unitIntervalFold w = unitIntervalFold (w - 2 * n₀) := by
    have h := unitIntervalFold_sign_mul_sub (Or.inl rfl) n₀ w
    rw [one_mul] at h
    exact h.symm
  rw [ENNReal.tsum_add]
  by_cases hr : w - 2 * n₀ < 1
  · have hmem : w - 2 * n₀ ∈ Ico (0 : ℝ) 1 := ⟨by linarith, hr⟩
    have hA : ∑' n : ℤ, (Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) = ψ (w - 2 * n₀) := by
      rw [tsum_eq_single n₀, indicator_of_mem hmem]
      intro n hn
      refine indicator_of_notMem (fun hm => hn ?_) _
      have ha : ((n - n₀ : ℤ) : ℝ) < 1 := by push_cast; linarith [hm.1, hmem.2]
      have hb : ((n₀ - n : ℤ) : ℝ) < 1 := by push_cast; linarith [hm.2, hmem.1]
      have ha' : n - n₀ < 1 := by exact_mod_cast ha
      have hb' : n₀ - n < 1 := by exact_mod_cast hb
      omega
    have hB : ∑' n : ℤ, (Ioc (0 : ℝ) 1).indicator ψ (2 * n - w) = 0 := by
      refine ENNReal.tsum_eq_zero.2 fun n => indicator_of_notMem (fun hm => ?_) _
      have ha : ((n₀ : ℤ) : ℝ) < n := by linarith [hm.1, hmem.1]
      have hb : (n : ℝ) < n₀ + 1 := by linarith [hm.2, hr]
      have ha' : n₀ < n := by exact_mod_cast ha
      have hb' : n < n₀ + 1 := by exact_mod_cast hb
      omega
    rw [hA, hB, add_zero, hfold, unitIntervalFold_of_mem_Icc ⟨hmem.1, hr.le⟩]
  · have hr' : 1 ≤ w - 2 * n₀ := not_lt.1 hr
    have hmem : 2 * ((n₀ + 1 : ℤ) : ℝ) - w ∈ Ioc (0 : ℝ) 1 := by
      push_cast
      constructor <;> linarith
    have hA : ∑' n : ℤ, (Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) = 0 := by
      refine ENNReal.tsum_eq_zero.2 fun n => indicator_of_notMem (fun hm => ?_) _
      have ha : ((n₀ : ℤ) : ℝ) < n := by linarith [hm.2]
      have hb : (n : ℝ) < n₀ + 1 := by linarith [hm.1]
      have ha' : n₀ < n := by exact_mod_cast ha
      have hb' : n < n₀ + 1 := by exact_mod_cast hb
      omega
    have hB : ∑' n : ℤ, (Ioc (0 : ℝ) 1).indicator ψ (2 * n - w) = ψ (2 * ((n₀ + 1 : ℤ) : ℝ) - w) := by
      rw [tsum_eq_single (n₀ + 1), indicator_of_mem hmem]
      intro n hn
      refine indicator_of_notMem (fun hm => hn ?_) _
      have ha : ((n - (n₀ + 1) : ℤ) : ℝ) < 1 := by push_cast at hmem ⊢; linarith [hm.2, hmem.1]
      have hb : ((n₀ + 1 - n : ℤ) : ℝ) < 1 := by push_cast at hmem ⊢; linarith [hm.1, hmem.2]
      have ha' : n - (n₀ + 1) < 1 := by exact_mod_cast ha
      have hb' : n₀ + 1 - n < 1 := by exact_mod_cast hb
      omega
    rw [hA, hB, zero_add, hfold, unitIntervalFold_of_mem_Icc_one_two ⟨hr', by linarith⟩]
    congr 1
    push_cast
    ring

/-! ### The interval kernel -/

/-- The heat kernel of reflected Brownian motion in `[0, 1]` at variance `s` (method of images):
`q_s(u, v) = ∑_n (φ_s(v + 2n - u) + φ_s(2n - v - u))`, as an extended nonnegative real. -/
noncomputable def intervalNeumannKernel (s : ℝ≥0) (u v : ℝ) : ℝ≥0∞ :=
  ∑' n : ℤ, (gaussianPDF u s (v + 2 * n) + gaussianPDF u s (2 * n - v))

theorem measurable_intervalNeumannKernel (s : ℝ≥0) :
    Measurable fun p : ℝ × ℝ => intervalNeumannKernel s p.1 p.2 := by
  unfold intervalNeumannKernel gaussianPDF
  refine Measurable.ennreal_tsum fun n => ?_
  refine (ENNReal.measurable_ofReal.comp ?_).add (ENNReal.measurable_ofReal.comp ?_) <;>
  · simp only [gaussianPDFReal_def]
    fun_prop

/-- **The law of reflected Brownian motion in `[0, 1]` at time `s`**: for measurable `ψ ≥ 0`,
`E ψ(fold(N(u, s))) = ∫_{[0,1]} ψ(v) q_s(u, v) dv`. -/
theorem lintegral_gaussianReal_unitIntervalFold {ψ : ℝ → ℝ≥0∞} (hψ : Measurable ψ) (u : ℝ)
    {s : ℝ≥0} (hs : s ≠ 0) :
    ∫⁻ w, ψ (unitIntervalFold w) ∂gaussianReal u s =
      ∫⁻ v in Icc (0 : ℝ) 1, ψ v * intervalNeumannKernel s u v := by
  have hpdf := measurable_gaussianPDF u s
  have hI : Measurable ((Ico (0 : ℝ) 1).indicator ψ) := hψ.indicator measurableSet_Ico
  have hJ : Measurable ((Ioc (0 : ℝ) 1).indicator ψ) := hψ.indicator measurableSet_Ioc
  rw [gaussianReal_of_var_ne_zero _ hs,
    lintegral_withDensity_eq_lintegral_mul _ hpdf
      (show Measurable fun w => ψ (unitIntervalFold w) from
        hψ.comp continuous_unitIntervalFold.measurable)]
  simp only [Pi.mul_apply]
  simp_rw [unitIntervalFold_eq_tsum_indicator ψ, ← ENNReal.tsum_mul_left, mul_add]
  rw [lintegral_tsum (f := fun (n : ℤ) w =>
      gaussianPDF u s w * (Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) +
        gaussianPDF u s w * (Ioc (0 : ℝ) 1).indicator ψ (2 * n - w))
    fun n => ((hpdf.mul (hI.comp (measurable_sub_const _))).add
      (hpdf.mul (hJ.comp (measurable_const_sub _)))).aemeasurable]
  have hterm : ∀ n : ℤ, ∫⁻ w, (gaussianPDF u s w * (Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) +
      gaussianPDF u s w * (Ioc (0 : ℝ) 1).indicator ψ (2 * n - w)) =
      ∫⁻ v in Icc (0 : ℝ) 1, ψ v * (gaussianPDF u s (v + 2 * n) + gaussianPDF u s (2 * n - v)) := by
    intro n
    have m1 : Measurable fun w => gaussianPDF u s w * (Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) :=
      hpdf.mul (hI.comp (measurable_sub_const _))
    have m2 : Measurable fun v => ψ v * gaussianPDF u s (v + 2 * n) :=
      hψ.mul (hpdf.comp (measurable_add_const _))
    rw [lintegral_add_left m1]
    have e1 : ∫⁻ w, gaussianPDF u s w * (Ico (0 : ℝ) 1).indicator ψ (w - 2 * n) =
        ∫⁻ v in Icc (0 : ℝ) 1, ψ v * gaussianPDF u s (v + 2 * n) := by
      have h := (measurePreserving_sub_right volume (2 * (n : ℝ))).lintegral_comp
        (f := fun v => gaussianPDF u s (v + 2 * n) * (Ico (0 : ℝ) 1).indicator ψ v)
        ((hpdf.comp (measurable_add_const _)).mul hI)
      simp only [sub_add_cancel] at h
      rw [h, ← setLIntegral_congr Ico_ae_eq_Icc]
      rw [← lintegral_indicator measurableSet_Ico]
      refine lintegral_congr fun v => ?_
      by_cases hv : v ∈ Ico (0 : ℝ) 1 <;> simp [hv, mul_comm]
    have e2 : ∫⁻ w, gaussianPDF u s w * (Ioc (0 : ℝ) 1).indicator ψ (2 * n - w) =
        ∫⁻ v in Icc (0 : ℝ) 1, ψ v * gaussianPDF u s (2 * n - v) := by
      have h := (Measure.measurePreserving_sub_left volume (2 * (n : ℝ))).lintegral_comp
        (f := fun v => gaussianPDF u s (2 * n - v) * (Ioc (0 : ℝ) 1).indicator ψ v)
        ((hpdf.comp (measurable_const_sub _)).mul hJ)
      simp only [sub_sub_cancel] at h
      rw [h, ← setLIntegral_congr Ioc_ae_eq_Icc]
      rw [← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun v => ?_
      by_cases hv : v ∈ Ioc (0 : ℝ) 1 <;> simp [hv, mul_comm]
    rw [e1, e2, ← lintegral_add_left m2]
    simp_rw [mul_add]
  simp_rw [hterm]
  rw [← lintegral_tsum (μ := volume.restrict (Icc (0 : ℝ) 1)) (f := fun (n : ℤ) v =>
      ψ v * (gaussianPDF u s (v + 2 * n) + gaussianPDF u s (2 * n - v)))
    fun n => (hψ.mul ((hpdf.comp (measurable_add_const _)).add
      (hpdf.comp (measurable_const_sub _)))).aemeasurable]
  simp_rw [ENNReal.tsum_mul_left]
  rfl

end HarmonicBalls
