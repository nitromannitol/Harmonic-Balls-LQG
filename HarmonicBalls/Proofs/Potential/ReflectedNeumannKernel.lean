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
  refine Measurable.tsum fun n => ?_
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

/-- `φ_s(x - μ)` depends only on `(x - μ)²`. -/
theorem gaussianPDF_congr_sq {μ μ' x x' : ℝ} (v : ℝ≥0) (h : (x - μ) ^ 2 = (x' - μ') ^ 2) :
    gaussianPDF μ v x = gaussianPDF μ' v x' := by
  simp only [gaussianPDF_def, gaussianPDFReal_def, h]

/-- **Symmetry of the interval kernel**: `q_s(u, v) = q_s(v, u)`. -/
theorem intervalNeumannKernel_comm (s : ℝ≥0) (u v : ℝ) :
    intervalNeumannKernel s u v = intervalNeumannKernel s v u := by
  unfold intervalNeumannKernel
  rw [ENNReal.tsum_add, ENNReal.tsum_add]
  congr 1
  · rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun n => gaussianPDF_congr_sq s ?_
    simp only [Equiv.neg_apply, Int.cast_neg]
    ring
  · exact tsum_congr fun n => gaussianPDF_congr_sq s (by ring)

attribute [irreducible] intervalNeumannKernel

/-! ### The square kernel -/

/-- The Neumann heat kernel of the unit square at variance `s`:
`k_s(x, y) = q_s(x₁, y₁) q_s(x₂, y₂)`. -/
noncomputable def squareNeumannKernel (s : ℝ≥0) (x y : ℂ) : ℝ≥0∞ :=
  intervalNeumannKernel s x.re y.re * intervalNeumannKernel s x.im y.im

theorem measurable_squareNeumannKernel (s : ℝ≥0) :
    Measurable fun p : ℂ × ℂ => squareNeumannKernel s p.1 p.2 := by
  have h := measurable_intervalNeumannKernel s
  have h1 : Measurable fun p : ℂ × ℂ => intervalNeumannKernel s p.1.re p.2.re :=
    h.comp (Measurable.prodMk (Complex.measurable_re.comp measurable_fst)
      (Complex.measurable_re.comp measurable_snd))
  have h2 : Measurable fun p : ℂ × ℂ => intervalNeumannKernel s p.1.im p.2.im :=
    h.comp (Measurable.prodMk (Complex.measurable_im.comp measurable_fst)
      (Complex.measurable_im.comp measurable_snd))
  unfold squareNeumannKernel
  exact h1.mul h2

attribute [irreducible] squareNeumannKernel

/-- **Symmetry of the square kernel**: `k_s(x, y) = k_s(y, x)`. -/
theorem squareNeumannKernel_comm (s : ℝ≥0) (x y : ℂ) :
    squareNeumannKernel s x y = squareNeumannKernel s y x := by
  unfold squareNeumannKernel
  rw [intervalNeumannKernel_comm s x.re, intervalNeumannKernel_comm s x.im]

/-- **The folded planar Gaussian law**: for measurable `Φ ≥ 0` and `s ≠ 0`,
`E Φ(fold(N(x, s))) = ∫_{K₀} Φ(y) k_s(x, y) dy`. -/
theorem lintegral_planarGaussian_squareFold_eq {Φ : ℂ → ℝ≥0∞} (hΦ : Measurable Φ) (x : ℂ)
    {s : ℝ≥0} (hs : s ≠ 0) :
    ∫⁻ w, Φ (squareFold 0 1 w) ∂planarGaussian x s =
      ∫⁻ y in closedSquare 0 1, Φ y * squareNeumannKernel s x y := by
  have he := Complex.measurableEquivRealProd.symm.measurable
  have hu := continuous_unitIntervalFold.measurable
  have hq := measurable_intervalNeumannKernel s
  have hF : Measurable fun p : ℝ × ℝ => Φ ⟨unitIntervalFold p.1, unitIntervalFold p.2⟩ :=
    hΦ.comp (measurable_complex_mk_comp (hu.comp measurable_fst) (hu.comp measurable_snd))
  have hqi : Measurable fun c₂ : ℝ => intervalNeumannKernel s x.im c₂ :=
    hq.comp (measurable_const.prodMk measurable_id)
  have hqr : Measurable fun c₁ : ℝ => intervalNeumannKernel s x.re c₁ :=
    hq.comp (measurable_const.prodMk measurable_id)
  have hGm : Measurable fun t : ℝ =>
      ∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨t, c₂⟩ * intervalNeumannKernel s x.im c₂ := by
    have : Measurable fun p : ℝ × ℝ => Φ ⟨p.1, p.2⟩ * intervalNeumannKernel s x.im p.2 :=
      (hΦ.comp measurable_complex_mk).mul (hqi.comp measurable_snd)
    exact this.lintegral_prod_right'
  have hmK : Measurable fun y : ℂ => Φ y * squareNeumannKernel s x y :=
    hΦ.mul ((measurable_squareNeumannKernel s).comp (measurable_const.prodMk measurable_id))
  have s1 : ∫⁻ w, Φ (squareFold 0 1 w) ∂planarGaussian x s =
      ∫⁻ p, Φ ⟨unitIntervalFold p.1, unitIntervalFold p.2⟩
        ∂((gaussianReal x.re s).prod (gaussianReal x.im s)) := by
    rw [planarGaussian, lintegral_map (show Measurable fun w => Φ (squareFold 0 1 w) from
      hΦ.comp (continuous_squareFold 0 1).measurable) he]
    exact lintegral_congr fun p => by rw [squareFold_measurableEquivRealProd_symm p]
  have s2 : ∫⁻ p, Φ ⟨unitIntervalFold p.1, unitIntervalFold p.2⟩
      ∂((gaussianReal x.re s).prod (gaussianReal x.im s)) =
      ∫⁻ w₁, ∫⁻ w₂, Φ ⟨unitIntervalFold w₁, unitIntervalFold w₂⟩ ∂gaussianReal x.im s
        ∂gaussianReal x.re s := lintegral_prod _ hF.aemeasurable
  have s3 : ∀ w₁ : ℝ, ∫⁻ w₂, Φ ⟨unitIntervalFold w₁, unitIntervalFold w₂⟩ ∂gaussianReal x.im s =
      ∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨unitIntervalFold w₁, c₂⟩ * intervalNeumannKernel s x.im c₂ :=
    fun w₁ => lintegral_gaussianReal_unitIntervalFold
      (ψ := fun t => Φ ⟨unitIntervalFold w₁, t⟩) (hΦ.comp (measurable_complex_mk_left _)) _ hs
  have s4 : ∫⁻ w₁, (∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨unitIntervalFold w₁, c₂⟩ *
        intervalNeumannKernel s x.im c₂) ∂gaussianReal x.re s =
      ∫⁻ c₁ in Icc (0 : ℝ) 1, (∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨c₁, c₂⟩ *
        intervalNeumannKernel s x.im c₂) * intervalNeumannKernel s x.re c₁ :=
    lintegral_gaussianReal_unitIntervalFold
      (ψ := fun t => ∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨t, c₂⟩ * intervalNeumannKernel s x.im c₂) hGm _ hs
  have s5 : ∫⁻ c₁ in Icc (0 : ℝ) 1, (∫⁻ c₂ in Icc (0 : ℝ) 1, Φ ⟨c₁, c₂⟩ *
        intervalNeumannKernel s x.im c₂) * intervalNeumannKernel s x.re c₁ =
      ∫⁻ y in closedSquare 0 1, Φ y * squareNeumannKernel s x y := by
    rw [setLIntegral_closedSquare_zero_one_eq hmK]
    refine setLIntegral_congr_fun measurableSet_Icc fun c₁ _ => ?_
    rw [← lintegral_mul_const _ (show Measurable fun c₂ => Φ ⟨c₁, c₂⟩ *
      intervalNeumannKernel s x.im c₂ from (hΦ.comp (measurable_complex_mk_left c₁)).mul hqi)]
    refine setLIntegral_congr_fun measurableSet_Icc fun c₂ _ => ?_
    unfold squareNeumannKernel
    ring
  rw [s1, s2, lintegral_congr s3, s4, s5]

/-- **The law of reflected Brownian motion in the unit square at time `s > 0`** has the density
`k_s(x, ·)` on `K₀`: `E_x Φ(b_s) = ∫_{K₀} Φ(y) k_s(x, y) dy` for measurable `Φ ≥ 0`. -/
theorem lintegral_reflected_eval_eq_neumannKernel {Φ : ℂ → ℝ≥0∞} (hΦ : Measurable Φ) (x : ℂ)
    {s : ℝ≥0} (hs : s ≠ 0) :
    ∫⁻ b, Φ (b s) ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ y in closedSquare 0 1, Φ y * squareNeumannKernel s x y := by
  have h := congrArg (fun m : Measure ℂ => ∫⁻ y, Φ y ∂m)
    (reflectedPlanarBrownianMotion_zero_one_map_eval x s)
  rw [lintegral_map hΦ (continuous_eval_const s).measurable,
    lintegral_map hΦ (continuous_squareFold 0 1).measurable] at h
  rw [h, lintegral_planarGaussian_squareFold_eq hΦ x hs]

/-! ### Continuity and bounds -/

theorem summable_exp_neg_mul_abs_int {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-c) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      ((Real.exp_lt_exp.2 (by linarith : -c < 0)).trans_eq Real.exp_zero)
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    have h : |(((n : ℤ) : ℝ))| = (n : ℝ) := by simp
    rw [h]
    ring
  · refine (hg.mul_left (Real.exp (-c))).congr fun n => ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    have h : |(((-((n : ℤ) + 1)) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      rw [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, abs_neg,
        abs_of_nonneg (by positivity)]
    rw [h]
    ring

/-- A uniform bound on the Gaussian terms of the interval kernel for `s ∈ [a, b]` and
`|z| ≤ 3`. -/
theorem gaussianPDFReal_add_two_mul_le {a b : ℝ} (ha : 0 < a) {s : ℝ≥0} (hsa : a ≤ s)
    (hsb : (s : ℝ) ≤ b) {z : ℝ} (hz : |z| ≤ 3) (n : ℤ) :
    gaussianPDFReal 0 s (z + 2 * n) ≤
      (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (3 / (2 * a)) *
        Real.exp (-(1 / (2 * b)) * |(n : ℝ)|) := by
  have hs : 0 < (s : ℝ) := lt_of_lt_of_le ha hsa
  have hb : 0 < b := hs.trans_le hsb
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  have h1 : (Real.sqrt (2 * Real.pi * s))⁻¹ ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ := by
    refine inv_anti₀ (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_le_sqrt ?_)
    have := Real.pi_pos
    nlinarith
  suffices h2 : Real.exp (-(z + 2 * n) ^ 2 / (2 * s)) ≤
      Real.exp (3 / (2 * a) + -(1 / (2 * b)) * |(n : ℝ)|) by
    calc (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(z + 2 * n) ^ 2 / (2 * s))
        ≤ (Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (3 / (2 * a) + -(1 / (2 * b)) * |(n : ℝ)|) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by rw [Real.exp_add]; ring
  · refine Real.exp_le_exp.2 ?_
    -- `(z + 2n)² ≥ |n| - 3`
    have hsq : |(n : ℝ)| - 3 ≤ (z + 2 * n) ^ 2 := by
      have h1 : 2 * |(n : ℝ)| - 3 ≤ |z + 2 * n| := by
        have := abs_sub_abs_le_abs_sub (2 * (n : ℝ)) (-z)
        rw [sub_neg_eq_add, abs_mul, abs_two, abs_neg] at this
        rw [add_comm]
        linarith
      rcases le_or_gt (|(n : ℝ)|) 1 with hn | hn
      · nlinarith [sq_nonneg (z + 2 * n)]
      · have h2 : 1 ≤ |z + 2 * n| := by
          have : (2 : ℝ) ≤ |(n : ℝ)| := by
            have hn' : (1 : ℝ) < |(n : ℝ)| := hn
            have : (1 : ℤ) < |n| := by exact_mod_cast hn'
            have : (2 : ℤ) ≤ |n| := this
            exact_mod_cast this
          linarith
        have : |z + 2 * n| ≤ (z + 2 * n) ^ 2 := by
          rw [← sq_abs]
          nlinarith
        linarith
    have hdiv : -((z + 2 * n) ^ 2) / (2 * (s : ℝ)) ≤ (3 - |(n : ℝ)|) / (2 * (s : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h3 : (3 - |(n : ℝ)|) / (2 * (s : ℝ)) ≤ 3 / (2 * a) + -(1 / (2 * b)) * |(n : ℝ)| := by
      rw [sub_div]
      have e1 : 3 / (2 * (s : ℝ)) ≤ 3 / (2 * a) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      have e2 : |(n : ℝ)| / (2 * b) ≤ |(n : ℝ)| / (2 * (s : ℝ)) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by linarith)
      have e3 : -(1 / (2 * b)) * |(n : ℝ)| = -(|(n : ℝ)| / (2 * b)) := by ring
      rw [e3]
      linarith
    calc -(z + 2 * n) ^ 2 / (2 * (s : ℝ)) = -((z + 2 * n) ^ 2) / (2 * (s : ℝ)) := by ring
      _ ≤ _ := hdiv.trans h3

/-- The terms of the interval kernel, recentred: `φ_s(v - u + 2n) + φ_s(-v - u + 2n)`. -/
noncomputable def intervalNeumannTerm (s : ℝ≥0) (u v : ℝ) (n : ℤ) : ℝ :=
  gaussianPDFReal 0 s (v - u + 2 * n) + gaussianPDFReal 0 s (-v - u + 2 * n)

/-- The real interval kernel `∑_n (φ_s(v - u + 2n) + φ_s(-v - u + 2n))`. -/
noncomputable def intervalNeumannKernelReal (s : ℝ≥0) (u v : ℝ) : ℝ :=
  ∑' n : ℤ, intervalNeumannTerm s u v n

theorem intervalNeumannTerm_nonneg (s : ℝ≥0) (u v : ℝ) (n : ℤ) :
    0 ≤ intervalNeumannTerm s u v n :=
  add_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)

/-- The summable majorant of the terms for `s ∈ [a, b]`, `u ∈ [0, 1]`, `v ∈ [-1, 2]`. -/
theorem intervalNeumannTerm_le {a b : ℝ} (ha : 0 < a) {s : ℝ≥0} (hsa : a ≤ s) (hsb : (s : ℝ) ≤ b)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 2) (n : ℤ) :
    intervalNeumannTerm s u v n ≤ 2 * ((Real.sqrt (2 * Real.pi * a))⁻¹ * Real.exp (3 / (2 * a)) *
      Real.exp (-(1 / (2 * b)) * |(n : ℝ)|)) := by
  unfold intervalNeumannTerm
  have h1 : |v - u| ≤ 3 := abs_le.2 ⟨by linarith [hu.2, hv.1], by linarith [hu.1, hv.2]⟩
  have h2 : |-v - u| ≤ 3 := abs_le.2 ⟨by linarith [hu.2, hv.2], by linarith [hu.1, hv.1]⟩
  exact (add_le_add (gaussianPDFReal_add_two_mul_le ha hsa hsb h1 n)
    (gaussianPDFReal_add_two_mul_le ha hsa hsb h2 n)).trans_eq (by ring)

theorem summable_intervalNeumannTerm {s : ℝ≥0} (hs : s ≠ 0) {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (-1 : ℝ) 2) : Summable (intervalNeumannTerm s u v) := by
  have hs' : 0 < (s : ℝ) := lt_of_le_of_ne s.coe_nonneg (by exact_mod_cast (Ne.symm hs))
  refine Summable.of_nonneg_of_le (intervalNeumannTerm_nonneg s u v)
    (intervalNeumannTerm_le hs' le_rfl le_rfl hu hv) ?_
  exact ((summable_exp_neg_mul_abs_int (by positivity : (0 : ℝ) < 1 / (2 * s))).mul_left _).mul_left _

/-- The interval kernel is the real kernel. -/
theorem intervalNeumannKernel_eq_ofReal {s : ℝ≥0} (hs : s ≠ 0) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 2) :
    intervalNeumannKernel s u v = ENNReal.ofReal (intervalNeumannKernelReal s u v) := by
  rw [intervalNeumannKernelReal, ENNReal.ofReal_tsum_of_nonneg (intervalNeumannTerm_nonneg s u v)
    (summable_intervalNeumannTerm hs hu hv), intervalNeumannKernel]
  refine tsum_congr fun n => ?_
  unfold intervalNeumannTerm
  rw [ENNReal.ofReal_add (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _)]
  simp only [gaussianPDF, gaussianPDFReal_def]
  congr 3 <;> ring

theorem continuousOn_gaussianPDFReal_zero {f : ℝ≥0 × ℝ → ℝ} (hf : Continuous f) {a : ℝ}
    (ha : 0 < a) :
    ContinuousOn (fun p : ℝ≥0 × ℝ => gaussianPDFReal 0 p.1 (f p)) {p | a ≤ (p.1 : ℝ)} := by
  simp only [gaussianPDFReal_def, sub_zero]
  have hc : Continuous fun p : ℝ≥0 × ℝ => ((p.1 : ℝ≥0) : ℝ) := NNReal.continuous_coe.comp continuous_fst
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.inv₀ ?_ fun p hp => ?_
    · exact (Real.continuous_sqrt.comp (continuous_const.mul hc)).continuousOn
    · have hp' : a ≤ (p.1 : ℝ) := hp
      have : 0 < 2 * Real.pi * (p.1 : ℝ) :=
        mul_pos (mul_pos two_pos Real.pi_pos) (lt_of_lt_of_le ha hp')
      exact (Real.sqrt_pos.2 this).ne'
  · refine Real.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.div (hf.pow 2).neg.continuousOn (continuous_const.mul hc).continuousOn
      fun p hp => ?_
    have hp' : a ≤ (p.1 : ℝ) := hp
    exact (mul_pos two_pos (lt_of_lt_of_le ha hp')).ne'

/-- **Continuity of the interval kernel** on `[a, b] × [-1, 2]` in `(s, v)`, for `u ∈ [0, 1]`. -/
theorem continuousOn_intervalNeumannKernelReal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun p : ℝ≥0 × ℝ => intervalNeumannKernelReal p.1 u p.2)
      ({p | a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b} ∩ {p | p.2 ∈ Icc (-1 : ℝ) 2}) := by
  unfold intervalNeumannKernelReal
  refine continuousOn_tsum (u := fun n : ℤ => 2 * ((Real.sqrt (2 * Real.pi * a))⁻¹ *
      Real.exp (3 / (2 * a)) * Real.exp (-(1 / (2 * b)) * |(n : ℝ)|))) (fun n => ?_) ?_ ?_
  · unfold intervalNeumannTerm
    have hS : {p : ℝ≥0 × ℝ | a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b} ∩ {p | p.2 ∈ Icc (-1 : ℝ) 2} ⊆
        {p | a ≤ (p.1 : ℝ)} := fun p hp => hp.1.1
    exact ((continuousOn_gaussianPDFReal_zero (by fun_prop) ha).mono hS).add
      ((continuousOn_gaussianPDFReal_zero (by fun_prop) ha).mono hS)
  · exact ((summable_exp_neg_mul_abs_int (div_pos one_pos (mul_pos two_pos
      (lt_of_lt_of_le ha hab)))).mul_left _).mul_left _
  · rintro n p ⟨⟨h1, h2⟩, h3⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalNeumannTerm_nonneg _ _ _ _)]
    exact intervalNeumannTerm_le ha h1 h2 hu h3 n

end HarmonicBalls
