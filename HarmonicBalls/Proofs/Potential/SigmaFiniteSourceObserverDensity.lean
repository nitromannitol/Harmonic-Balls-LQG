import HarmonicBalls.Proofs.Potential.IntegrableDensityObserverBound

/-! # Sigma-finite sources with integrable densities

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- A signed integrable density gives a mixed integrable transposed kernel. -/
theorem sigmaFinite_integrable_density_green_product_of_local_upper_growth
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [SigmaFinite ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) {f : ℂ → ℝ} (hf : Measurable f)
    (hfi : Integrable f ν) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) := by
  let ρ := ν.withDensity (fun y => ENNReal.ofReal ‖f y‖)
  have hd : Measurable (fun y => ENNReal.ofReal ‖f y‖) := hf.norm.ennreal_ofReal
  let : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hfi.norm.2
  have hc : ∀ᵐ y ∂ρ, y ∈ V := (withDensity_absolutelyContinuous ν _).ae_le hν
  have hi := generalDomain_green_integrable_product_of_local_upper_growth hup hV hVb hc
  change Integrable _ ((ν.withDensity _).prod (μ.restrict V)) at hi
  rw [prod_withDensity_left hd] at hi
  have hi' := (integrable_withDensity_iff_integrable_smul'
    (hd.comp measurable_fst) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hi
  have hi'' : Integrable (fun p : ℂ × ℂ => ‖f p.1‖ * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) := by
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (norm_nonneg _), smul_eq_mul] using hi'
  apply hi''.mono' (((hf.comp measurable_fst).mul
    (measurable_greenFunction_uncurry hV)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖f p.1 * greenFunction V p.1 p.2‖ ≤ ‖f p.1‖ * greenFunction V p.1 p.2
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg hVb _ _)]
  exact le_rfl

/-- The nonnegative weighted kernel is integrable on the product and on
almost every source slice for the observer measure. -/
theorem sigmaFinite_integrable_weighted_green_product_and_slices
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [SigmaFinite ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) {f : ℂ → ℝ} (hf : Measurable f)
    (hfi : Integrable f ν) :
    Integrable (fun p : ℂ × ℂ => ‖f p.1‖ * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) ∧
    (∀ᵐ x ∂μ.restrict V, Integrable (fun y => ‖f y‖ * greenFunction V y x) ν) := by
  have hp := sigmaFinite_integrable_density_green_product_of_local_upper_growth
    hup hV hVb hν hf.norm hfi.norm
  exact ⟨hp, hp.prod_left_ae⟩

/-- A single constant bounds all integrable-density potentials on subdomains
of the given disc, and supplies product and slice integrability. -/
theorem sigmaFinite_integrable_density_observer_bound
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball (0 : ℂ) R →
      ∀ {ν : Measure ℂ} [SigmaFinite ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∀ {f : ℂ → ℝ}, Measurable f → Integrable f ν →
      Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
        (ν.prod (μ.restrict V)) ∧
      (∀ᵐ x ∂μ.restrict V, Integrable (fun y => f y * greenFunction V y x) ν) ∧
      Integrable (fun x => ∫ y, f y * greenFunction V y x ∂ν) (μ.restrict V) ∧
      (∫ x in V, ‖∫ y, f y * greenFunction V y x ∂ν‖ ∂μ) ≤
        C * ∫ y, ‖f y‖ ∂ν := by
  obtain ⟨C, hC, hrow⟩ := green_row_bound_of_local_upper_growth hup hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν f hf hfi
  have hVb := isBounded_ball.subset hsub
  have hp := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hV hVb hν hf hfi
  refine ⟨hp, hp.prod_left_ae, hp.integral_prod_right, ?_⟩
  have hnorm := hp.norm
  have hrowint : (∫ y, ∫ x in V, ‖f y * greenFunction V y x‖ ∂μ ∂ν) ≤
      C * ∫ y, ‖f y‖ ∂ν := by
    rw [← integral_const_mul]
    apply integral_mono_ae hnorm.integral_prod_left (hfi.norm.const_mul C)
    filter_upwards [hν] with y hy
    have hi := (hrow hV hsub y hy).1
    have heq : (fun x => ‖f y * greenFunction V y x‖) =
        fun x => ‖f y‖ * greenFunction V y x := by
      funext x
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg hVb y x)]
    rw [heq, integral_const_mul]
    exact (mul_le_mul_of_nonneg_left ((hrow hV hsub y hy).2) (norm_nonneg _)).trans_eq (mul_comm _ _)
  calc
    (∫ x in V, ‖∫ y, f y * greenFunction V y x ∂ν‖ ∂μ) ≤
        ∫ x in V, ∫ y, ‖f y * greenFunction V y x‖ ∂ν ∂μ := by
      apply integral_mono_ae hp.integral_prod_right.norm hnorm.integral_prod_right
      exact Eventually.of_forall fun x => norm_integral_le_integral_norm _
    _ = ∫ y, ∫ x in V, ‖f y * greenFunction V y x‖ ∂μ ∂ν :=
      (integral_integral_swap (f := fun y x => ‖f y * greenFunction V y x‖) hnorm).symm
    _ ≤ C * ∫ y, ‖f y‖ ∂ν := hrowint

/-- L¹ convergence of source densities implies L¹ convergence of the observed
transposed potentials. No pointwise convergence is asserted. -/
theorem tendsto_integral_norm_sigmaFinite_integrable_density_observer
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [SigmaFinite ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) {V : Set ℂ} (hV : IsOpen V)
    (hsub : V ⊆ ball (0 : ℂ) R) (hν : ∀ᵐ y ∂ν, y ∈ V)
    (F : ℕ → ℂ → ℝ) (f : ℂ → ℝ)
    (hF : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) ν)
    (hf : Measurable f) (hfi : Integrable f ν)
    (hconv : Tendsto (fun n => ∫ y, ‖F n y - f y‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, ‖(∫ y, F n y * greenFunction V y x ∂ν) -
      (∫ y, f y * greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := sigmaFinite_integrable_density_observer_bound hup hR
  have hlim : Tendsto (fun n => C * ∫ y, ‖F n y - f y‖ ∂ν) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hconv
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) ?_ hlim
  intro n
  have hn := hb hV hsub hν (hF n) (hFi n)
  have hf' := hb hV hsub hν hf hfi
  have hd := hb hV hsub hν ((hF n).sub hf) ((hFi n).sub hfi)
  have heq : ∀ᵐ x ∂μ.restrict V,
      (∫ y, F n y * greenFunction V y x ∂ν) - (∫ y, f y * greenFunction V y x ∂ν) =
        ∫ y, (F n y - f y) * greenFunction V y x ∂ν := by
    filter_upwards [hn.2.1, hf'.2.1] with x hx hy
    rw [← integral_sub hx hy]
    apply integral_congr_ae
    filter_upwards with y
    rw [sub_mul]
  calc
    _ = ∫ x in V, ‖∫ y, (F n y - f y) * greenFunction V y x ∂ν‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ ≤ _ := hd.2.2.2

end HarmonicBalls
