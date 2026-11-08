import HarmonicBalls.Proofs.Potential.TransposedGreenDomainExhaustion
import HarmonicBalls.Proofs.Potential.SigmaFiniteSourceObserverDensity

/-! # Integrable-density Green potentials along domain exhaustions

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- Weighted kernels on every exhaustion domain are integrable against the full
source and full observer measures. -/
theorem sigmaFinite_integrable_density_observer_exhaustion_product
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V U : Set ℂ} (hV : IsOpen V) (hsub : V ⊆ U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ U)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict U)) := by
  have hi := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf.norm hfi.norm
  apply hi.mono' (((hf.comp measurable_fst).mul (measurable_greenFunction_uncurry hV)).aestronglyMeasurable)
  filter_upwards with p
  change ‖f p.1 * greenFunction V p.1 p.2‖ ≤ ‖f p.1‖ * greenFunction U p.1 p.2
  rw [norm_mul, Real.norm_eq_abs (greenFunction V p.1 p.2),
    abs_of_nonneg (greenFunction_nonneg (hUb.subset hsub) p.1 p.2)]
  exact mul_le_mul_of_nonneg_left (Section6.greenFunction_le_of_subset hsub hUb p.1 p.2) (norm_nonneg _)

/-- Exhaustion kernels converge in product L¹ in source-observer order. -/
theorem tendsto_integral_norm_sigmaFinite_observer_exhaustion_product
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Tendsto (fun n => ∫ p, ‖f p.1 * greenFunction (V n) p.1 p.2 -
      f p.1 * greenFunction U p.1 p.2‖ ∂(ν.prod (μ.restrict U))) atTop (𝓝 0) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf.norm hfi.norm
  have hu := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf hfi
  have hn (n : ℕ) := sigmaFinite_integrable_density_observer_exhaustion_product hup (hopen n) (hsub n) hU hUb hν hf hfi
  have hpoint : ∀ᵐ p ∂(ν.prod (μ.restrict U)),
      Tendsto (fun n => f p.1 * greenFunction (V n) p.1 p.2) atTop
        (𝓝 (f p.1 * greenFunction U p.1 p.2)) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hν,
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hU.measurableSet)] with p hy hx
    by_cases h : p.1 = p.2
    · rw [h]
      simpa only [greenFunction_self, mul_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · exact tendsto_const_nhds.mul
        (tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hy hx h)
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun p : ℂ × ℂ => 2 * (‖f p.1‖ * greenFunction U p.1 p.2))
    (fun n => ((hn n).sub hu).norm.aestronglyMeasurable) (hp.const_mul 2) ?_ ?_
  · simpa only [Pi.sub_apply, integral_zero] using ht
  · intro n
    filter_upwards with p
    have hb : ‖f p.1 * greenFunction (V n) p.1 p.2‖ ≤ ‖f p.1‖ * greenFunction U p.1 p.2 := by
      rw [norm_mul, Real.norm_eq_abs (greenFunction (V n) p.1 p.2), abs_of_nonneg (greenFunction_nonneg (hUb.subset (hsub n)) _ _)]
      exact mul_le_mul_of_nonneg_left (Section6.greenFunction_le_of_subset (hsub n) hUb _ _) (norm_nonneg _)
    have hc : ‖f p.1 * greenFunction U p.1 p.2‖ = ‖f p.1‖ * greenFunction U p.1 p.2 := by
      rw [norm_mul, Real.norm_eq_abs (greenFunction U p.1 p.2), abs_of_nonneg (greenFunction_nonneg hUb _ _)]
    have hd := norm_sub_le (f p.1 * greenFunction (V n) p.1 p.2) (f p.1 * greenFunction U p.1 p.2)
    change ‖‖f p.1 * greenFunction (V n) p.1 p.2 - f p.1 * greenFunction U p.1 p.2‖‖ ≤ _
    rw [norm_norm]
    linarith
  · filter_upwards [hpoint] with p hp
    simpa only [Pi.sub_apply, sub_self, norm_zero] using (hp.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f p.1 * greenFunction U p.1 p.2) atTop _)).norm

/-- The signed weighted potentials converge almost everywhere on the full domain. -/
theorem ae_tendsto_sigmaFinite_integrable_density_observer_exhaustion
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    ∀ᵐ x ∂μ.restrict U,
      Tendsto (fun n => ∫ y, f y * greenFunction (V n) y x ∂ν) atTop
        (𝓝 (∫ y, f y * greenFunction U y x ∂ν)) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf.norm hfi.norm
  filter_upwards [hp.swap.prod_right_ae, ae_restrict_mem hU.measurableSet] with x hx hxU
  apply tendsto_integral_of_dominated_convergence (fun y => ‖f y‖ * greenFunction U y x)
  · intro n
    exact (hf.mul ((measurable_greenFunction_uncurry (hopen n)).comp
      (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  · exact hx
  · intro n
    filter_upwards with y
    rw [norm_mul, Real.norm_eq_abs (greenFunction (V n) y x),
      abs_of_nonneg (greenFunction_nonneg (hUb.subset (hsub n)) y x)]
    exact mul_le_mul_of_nonneg_left (Section6.greenFunction_le_of_subset (hsub n) hUb y x) (norm_nonneg _)
  · filter_upwards [hν] with y hy
    by_cases h : y = x
    · subst y
      simpa only [greenFunction_self, mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · exact tendsto_const_nhds.mul (tendsto_greenFunction_of_exhaustion V hopen hmono hU hUb hcover hy hxU h)

/-- The same convergence holds in integral norm over all of the domain. -/
theorem tendsto_integral_norm_sigmaFinite_integrable_density_observer_exhaustion
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Tendsto (fun n => ∫ x in U, ‖(∫ y, f y * greenFunction (V n) y x ∂ν) -
      (∫ y, f y * greenFunction U y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf hfi
  have ha := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf.norm hfi.norm
  have hn (n : ℕ) := sigmaFinite_integrable_density_observer_exhaustion_product hup (hopen n) (hsub n) hU hUb hν hf hfi
  have hi := hp.integral_prod_right
  have hb (n : ℕ) : ∀ᵐ x ∂μ.restrict U,
      ‖(∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖ ≤
        2 * (∫ y, ‖f y‖ * greenFunction U y x ∂ν) := by
    filter_upwards [(hn n).swap.prod_right_ae, hp.swap.prod_right_ae, ha.swap.prod_right_ae] with x hxn hx hax
    have bound (W : Set ℂ) (hWb : Bornology.IsBounded W) (hW : W ⊆ U)
        (hw : Integrable (fun y => f y * greenFunction W y x) ν) :
        ‖∫ y, f y * greenFunction W y x ∂ν‖ ≤ ∫ y, ‖f y‖ * greenFunction U y x ∂ν := by
      calc
        _ ≤ ∫ y, ‖f y * greenFunction W y x‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ _ := by
          apply integral_mono_ae hw.norm hax
          filter_upwards with y
          change ‖f y * greenFunction W y x‖ ≤ ‖f y‖ * greenFunction U y x
          rw [norm_mul, Real.norm_eq_abs (greenFunction W y x), abs_of_nonneg (greenFunction_nonneg hWb y x)]
          exact mul_le_mul_of_nonneg_left (Section6.greenFunction_le_of_subset hW hUb y x) (norm_nonneg _)
    have h1 := bound (V n) (hUb.subset (hsub n)) (hsub n) hxn
    have h2 := bound U hUb (Subset.refl U) hx
    calc
      _ ≤ ‖∫ y, f y * greenFunction (V n) y x ∂ν‖ + ‖∫ y, f y * greenFunction U y x ∂ν‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have ht := tendsto_integral_of_dominated_convergence
    (fun x => 2 * ∫ y, ‖f y‖ * greenFunction U y x ∂ν)
    (fun n => (((hn n).integral_prod_right).sub hi).aestronglyMeasurable.norm)
    (ha.integral_prod_right.const_mul 2)
    (fun n => by filter_upwards [hb n] with x hx; simpa only [Pi.sub_apply, norm_norm] using hx)
    (by filter_upwards [ae_tendsto_sigmaFinite_integrable_density_observer_exhaustion hup V hopen hmono hU hUb hcover hν hf hfi] with x hx
        simpa only [Pi.sub_apply, sub_self, norm_zero] using (hx.sub tendsto_const_nhds).norm)
  simpa only [Pi.sub_apply, sub_self, norm_zero, integral_zero] using ht

/-- A single constant controls the potentials on subdomains, integrated over U. -/
theorem sigmaFinite_integrable_density_observer_exhaustion_bound
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ U →
      ∀ (ν : Measure ℂ) [SigmaFinite ν], (∀ᵐ y ∂ν, y ∈ U) →
      ∀ (f : ℂ → ℝ), Measurable f → Integrable f ν →
      (∫ x in U, ‖∫ y, f y * greenFunction V y x ∂ν‖ ∂μ) ≤ C * ∫ y, |f y| ∂ν := by
  obtain ⟨R, hR, hball⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨C, hC, hbound⟩ := sigmaFinite_integrable_density_observer_bound hup hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν f hf hfi
  have hn := sigmaFinite_integrable_density_observer_exhaustion_product hup hV hsub hU hUb hν hf hfi
  have ha := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf.norm hfi.norm
  have hbase := hbound hU hball hν hf.norm hfi.norm
  calc
    (∫ x in U, ‖∫ y, f y * greenFunction V y x ∂ν‖ ∂μ) ≤
        ∫ x in U, ∫ y, ‖f y‖ * greenFunction U y x ∂ν ∂μ := by
      apply integral_mono_ae hn.integral_prod_right.norm ha.integral_prod_right
      filter_upwards [(hn.swap.prod_right_ae), (ha.swap.prod_right_ae)] with x hx hax
      calc
        _ ≤ ∫ y, ‖f y * greenFunction V y x‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ _ := by
          apply integral_mono_ae hx.norm hax
          filter_upwards with y
          change ‖f y * greenFunction V y x‖ ≤ ‖f y‖ * greenFunction U y x
          rw [norm_mul, Real.norm_eq_abs (greenFunction V y x),
            abs_of_nonneg (greenFunction_nonneg (hUb.subset hsub) y x)]
          exact mul_le_mul_of_nonneg_left (Section6.greenFunction_le_of_subset hsub hUb y x) (norm_nonneg _)
    _ = ∫ x in U, ‖∫ y, ‖f y‖ * greenFunction U y x ∂ν‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact integral_nonneg fun y => mul_nonneg (norm_nonneg _) (greenFunction_nonneg hUb y x)
    _ ≤ C * ∫ y, |f y| ∂ν := by
      simpa only [Real.norm_eq_abs, abs_abs] using hbase.2.2.2

/-- L¹ convergence persists when the integrable densities also converge in L¹. -/
theorem tendsto_integral_norm_sigmaFinite_varying_density_observer_exhaustion
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [SigmaFinite ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (F : ℕ → ℂ → ℝ) (hF : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) ν)
    (hconv : Tendsto (fun n => ∫ y, |F n y - f y| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, ‖(∫ y, F n y * greenFunction (V n) y x ∂ν) -
      (∫ y, f y * greenFunction U y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  obtain ⟨C, hC, hbound⟩ := sigmaFinite_integrable_density_observer_exhaustion_bound hup hU hUb
  have hfixed := tendsto_integral_norm_sigmaFinite_integrable_density_observer_exhaustion hup V hopen hmono hU hUb hcover hν hf hfi
  have hupper : Tendsto (fun n => C * (∫ y, |F n y - f y| ∂ν) +
      ∫ x in U, ‖(∫ y, f y * greenFunction (V n) y x ∂ν) -
        (∫ y, f y * greenFunction U y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hconv).add hfixed
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) ?_ hupper
  intro n
  have hfn := sigmaFinite_integrable_density_observer_exhaustion_product hup (hopen n) (hsub n) hU hUb hν (hF n) (hFi n)
  have hff := sigmaFinite_integrable_density_observer_exhaustion_product hup (hopen n) (hsub n) hU hUb hν hf hfi
  have hd := sigmaFinite_integrable_density_observer_exhaustion_product hup (hopen n) (hsub n) hU hUb hν ((hF n).sub hf) ((hFi n).sub hfi)
  have hu := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hU hUb hν hf hfi
  have hpoint : ∀ᵐ x ∂μ.restrict U,
      (∫ y, F n y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction (V n) y x ∂ν) =
        ∫ y, (F n y - f y) * greenFunction (V n) y x ∂ν := by
    filter_upwards [hfn.swap.prod_right_ae, hff.swap.prod_right_ae] with x hx hy
    change Integrable (fun y => F n y * greenFunction (V n) y x) ν at hx
    change Integrable (fun y => f y * greenFunction (V n) y x) ν at hy
    rw [← integral_sub hx hy]
    apply integral_congr_ae
    filter_upwards with y
    simp only [sub_mul]
  calc
    _ ≤ ∫ x in U, (‖∫ y, (F n y - f y) * greenFunction (V n) y x ∂ν‖ +
        ‖(∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖) ∂μ := by
      apply integral_mono_ae ((hfn.integral_prod_right.sub hu.integral_prod_right).norm)
        (hd.integral_prod_right.norm.add ((hff.integral_prod_right.sub hu.integral_prod_right).norm))
      filter_upwards [hpoint] with x hx
      have ht := norm_add_le ((∫ y, F n y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction (V n) y x ∂ν))
        ((∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν))
      have heq : (∫ y, F n y * greenFunction (V n) y x ∂ν) -
          (∫ y, f y * greenFunction U y x ∂ν) =
          ((∫ y, F n y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction (V n) y x ∂ν)) +
          ((∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)) := by ring
      change ‖(∫ y, F n y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖ ≤
        ‖∫ y, (F n y - f y) * greenFunction (V n) y x ∂ν‖ +
          ‖(∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖
      rw [heq, hx]
      simpa only [hx] using ht
    _ = (∫ x in U, ‖∫ y, (F n y - f y) * greenFunction (V n) y x ∂ν‖ ∂μ) +
        ∫ x in U, ‖(∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖ ∂μ :=
      integral_add hd.integral_prod_right.norm ((hff.integral_prod_right.sub hu.integral_prod_right).norm)
    _ ≤ _ := by
      gcongr
      exact hbound (hopen n) (hsub n) ν hν (fun y => F n y - f y) ((hF n).sub hf) ((hFi n).sub hfi)

#print axioms sigmaFinite_integrable_density_observer_exhaustion_product
#print axioms ae_tendsto_sigmaFinite_integrable_density_observer_exhaustion
#print axioms tendsto_integral_norm_sigmaFinite_integrable_density_observer_exhaustion
#print axioms sigmaFinite_integrable_density_observer_exhaustion_bound
#print axioms tendsto_integral_norm_sigmaFinite_varying_density_observer_exhaustion
/-- Distance cutoffs converge in product L¹ and at almost every observer, and
also converge in observer L¹. The kernel is in source-observer order. -/
theorem sigmaFinite_integrable_density_observer_diagonal_cutoff
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) ∧
    (∀ n, Integrable (fun p : ℂ × ℂ =>
      if ε n ≤ dist p.1 p.2 then f p.1 * greenFunction V p.1 p.2 else 0)
      (ν.prod (μ.restrict V))) ∧
    Integrable (fun x => ∫ y, f y * greenFunction V y x ∂ν) (μ.restrict V) ∧
    (∀ n, Integrable (fun x => ∫ y, if ε n ≤ dist y x then
      f y * greenFunction V y x else 0 ∂ν) (μ.restrict V)) ∧
    Tendsto (fun n => ∫ p, ‖(if ε n ≤ dist p.1 p.2 then
      f p.1 * greenFunction V p.1 p.2 else 0) -
      f p.1 * greenFunction V p.1 p.2‖ ∂(ν.prod (μ.restrict V))) atTop (𝓝 0) ∧
    (∀ᵐ x ∂μ.restrict V,
      Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∀ n, Integrable (fun y => if ε n ≤ dist y x then
        f y * greenFunction V y x else 0) ν) ∧
      Tendsto (fun n => ∫ y, if ε n ≤ dist y x then
        f y * greenFunction V y x else 0 ∂ν) atTop
        (𝓝 (∫ y, f y * greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(∫ y, if ε n ≤ dist y x then
      f y * greenFunction V y x else 0 ∂ν) -
      (∫ y, f y * greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  let A (n : ℕ) : Set (ℂ × ℂ) := {p | ε n ≤ dist p.1 p.2}
  let G : ℂ × ℂ → ℝ := fun p => f p.1 * greenFunction V p.1 p.2
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le measurable_const measurable_dist
  have hp : Integrable G (ν.prod (μ.restrict V)) :=
    sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hV hVb hν hf hfi
  have hi (n : ℕ) : Integrable ((A n).indicator G) (ν.prod (μ.restrict V)) :=
    hp.indicator (hA n)
  have hkernel (y x : ℂ) : Tendsto (fun n => (A n).indicator G (y, x)) atTop
      (𝓝 (G (y, x))) := by
    by_cases hyx : y = x
    · subst y
      simp [A, G, Set.indicator_apply, greenFunction_self]
    · apply tendsto_const_nhds.congr'
      filter_upwards [hε.eventually (eventually_lt_nhds (dist_pos.mpr hyx))] with n hn
      simp [A, G, le_of_lt hn]
  have hpoint : ∀ᵐ x ∂μ.restrict V, Integrable (fun y => G (y, x)) ν ∧
      (∀ n, Integrable (fun y => (A n).indicator G (y, x)) ν) ∧
      Tendsto (fun n => ∫ y, (A n).indicator G (y, x) ∂ν) atTop
        (𝓝 (∫ y, G (y, x) ∂ν)) := by
    filter_upwards [hp.prod_left_ae, ae_all_iff.mpr (fun n => (hi n).prod_left_ae)] with x hx hix
    refine ⟨hx, hix, ?_⟩
    apply tendsto_integral_of_dominated_convergence (fun y => ‖G (y, x)‖)
      (fun n => (hix n).aestronglyMeasurable) hx.norm
    · intro n
      filter_upwards with y
      by_cases h : ε n ≤ dist y x <;> simp [A, h]
    · exact Eventually.of_forall (fun y => hkernel y x)
  have hprod := tendsto_integral_of_dominated_convergence
    (μ := ν.prod (μ.restrict V)) (fun p => ‖G p‖)
    (fun n => ((hi n).sub hp).norm.aestronglyMeasurable) hp.norm
    (fun n => by
      filter_upwards with p
      by_cases h : ε n ≤ dist p.1 p.2 <;> simp [A, h])
    (Eventually.of_forall fun p => by
      simpa using ((hkernel p.1 p.2).sub tendsto_const_nhds).norm)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ.restrict V) (fun x => 2 * ∫ y, ‖G (y, x)‖ ∂ν)
    (fun n => (((hi n).integral_prod_right).sub hp.integral_prod_right).norm.aestronglyMeasurable)
    (hp.norm.integral_prod_right.const_mul 2)
    (fun n => by
      filter_upwards [hp.prod_left_ae, (hi n).prod_left_ae] with x hx hix
      have hb : (∫ y, ‖(A n).indicator G (y, x)‖ ∂ν) ≤ ∫ y, ‖G (y, x)‖ ∂ν := by
        apply integral_mono_ae hix.norm hx.norm
        filter_upwards with y
        by_cases h : ε n ≤ dist y x <;> simp [A, h]
      change ‖‖(∫ y, (A n).indicator G (y, x) ∂ν) - (∫ y, G (y, x) ∂ν)‖‖ ≤ _
      rw [norm_norm]
      have ha := norm_integral_le_integral_norm (μ := ν) (fun y => (A n).indicator G (y, x))
      have hc := norm_integral_le_integral_norm (μ := ν) (fun y => G (y, x))
      have hd := norm_sub_le (∫ y, (A n).indicator G (y, x) ∂ν) (∫ y, G (y, x) ∂ν)
      linarith)
    (hpoint.mono fun x hx => by simpa using (hx.2.2.sub tendsto_const_nhds).norm)
  have heq (n : ℕ) : (A n).indicator G = (fun p =>
      if ε n ≤ dist p.1 p.2 then f p.1 * greenFunction V p.1 p.2 else 0) := by
    funext p
    simp [A, G, Set.indicator_apply]
  refine ⟨hp, ?_, hp.integral_prod_right, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [← heq n]
    exact hi n
  · intro n
    simpa [A, G, Set.indicator_apply] using (hi n).integral_prod_right
  · simpa [A, G, Set.indicator_apply] using hprod
  · filter_upwards [hpoint] with x hx
    simpa [A, G, Set.indicator_apply] using hx
  · simpa [A, G, Set.indicator_apply] using hlim


#print axioms tendsto_integral_norm_sigmaFinite_observer_exhaustion_product
/-- Diagonal-cutoff potentials also converge in observer L¹ when the source
 densities converge in L¹. -/
theorem tendsto_integral_norm_sigmaFinite_varying_density_diagonal_cutoff
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (F : ℕ → ℂ → ℝ) (hF : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) ν)
    (hconv : Tendsto (fun n => ∫ y, |F n y - f y| ∂ν) atTop (𝓝 0))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, ‖(∫ y, if ε n ≤ dist y x then
      F n y * greenFunction V y x else 0 ∂ν) -
      (∫ y, f y * greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := sigmaFinite_integrable_density_observer_exhaustion_bound hup hV hVb
  have hfixed := (sigmaFinite_integrable_density_observer_diagonal_cutoff hup hV hVb hν hf hfi ε hε).2.2.2.2.2.2
  have hupper : Tendsto (fun n => C * (∫ y, |F n y - f y| ∂ν) +
      ∫ x in V, ‖(∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν) -
        (∫ y, f y * greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hconv).add hfixed
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) ?_ hupper
  intro n
  let D : ℂ → ℝ := fun y => F n y - f y
  let K : ℂ × ℂ → ℝ := fun p => if ε n ≤ dist p.1 p.2 then D p.1 * greenFunction V p.1 p.2 else 0
  have hd : Measurable D := (hF n).sub hf
  have hdi : Integrable D ν := (hFi n).sub hfi
  have hk : Integrable K (ν.prod (μ.restrict V)) :=
    (sigmaFinite_integrable_density_observer_diagonal_cutoff hup hV hVb hν hd hdi ε hε).2.1 n
  have hfn := (sigmaFinite_integrable_density_observer_diagonal_cutoff hup hV hVb hν (hF n) (hFi n) ε hε).2.1 n
  have hff := (sigmaFinite_integrable_density_observer_diagonal_cutoff hup hV hVb hν hf hfi ε hε).2.1 n
  have hu := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hV hVb hν hf hfi
  have ha := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hV hVb hν hd.norm hdi.norm
  have hbound : (∫ x in V, ‖∫ y, K (y, x) ∂ν‖ ∂μ) ≤ C * ∫ y, |D y| ∂ν := by
    calc
      _ ≤ ∫ x in V, ∫ y, ‖D y‖ * greenFunction V y x ∂ν ∂μ := by
        apply integral_mono_ae hk.integral_prod_right.norm ha.integral_prod_right
        filter_upwards [hk.prod_left_ae, ha.prod_left_ae] with x hx hax
        calc
          _ ≤ ∫ y, ‖K (y, x)‖ ∂ν := norm_integral_le_integral_norm _
          _ ≤ _ := by
            apply integral_mono_ae hx.norm hax
            filter_upwards with y
            by_cases h : ε n ≤ dist y x
            · simp only [K, h, ↓reduceIte, norm_mul, Real.norm_eq_abs (greenFunction V y x),
                abs_of_nonneg (greenFunction_nonneg hVb y x)]
              exact le_rfl
            · simp only [K, h, ↓reduceIte, norm_zero]
              exact mul_nonneg (norm_nonneg _) (greenFunction_nonneg hVb y x)
      _ = ∫ x in V, ‖∫ y, ‖D y‖ * greenFunction V y x ∂ν‖ ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact integral_nonneg fun y => mul_nonneg (norm_nonneg _) (greenFunction_nonneg hVb y x)
      _ ≤ _ := by
        simpa only [Real.norm_eq_abs, abs_abs] using hb hV (Subset.refl V) ν hν (fun y => ‖D y‖) hd.norm hdi.norm
  have hpoint : ∀ᵐ x ∂μ.restrict V,
      (∫ y, if ε n ≤ dist y x then F n y * greenFunction V y x else 0 ∂ν) -
      (∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν) = ∫ y, K (y, x) ∂ν := by
    filter_upwards [hfn.prod_left_ae, hff.prod_left_ae] with x hx hy
    rw [← integral_sub hx hy]
    apply integral_congr_ae
    filter_upwards with y
    by_cases h : ε n ≤ dist y x <;> simp [K, D, h, sub_mul]
  calc
    _ ≤ ∫ x in V, (‖∫ y, K (y, x) ∂ν‖ +
        ‖(∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν) -
          (∫ y, f y * greenFunction V y x ∂ν)‖) ∂μ := by
      apply integral_mono_ae (hfn.integral_prod_right.sub hu.integral_prod_right).norm
        (hk.integral_prod_right.norm.add (hff.integral_prod_right.sub hu.integral_prod_right).norm)
      filter_upwards [hpoint] with x hx
      have ht := norm_add_le ((∫ y, if ε n ≤ dist y x then F n y * greenFunction V y x else 0 ∂ν) -
        (∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν))
        ((∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν) -
        (∫ y, f y * greenFunction V y x ∂ν))
      change ‖(∫ y, if ε n ≤ dist y x then F n y * greenFunction V y x else 0 ∂ν) -
        (∫ y, f y * greenFunction V y x ∂ν)‖ ≤ _
      have heq : (∫ y, if ε n ≤ dist y x then F n y * greenFunction V y x else 0 ∂ν) -
          (∫ y, f y * greenFunction V y x ∂ν) =
          ((∫ y, if ε n ≤ dist y x then F n y * greenFunction V y x else 0 ∂ν) -
          (∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν)) +
          ((∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν) -
          (∫ y, f y * greenFunction V y x ∂ν)) := by ring
      rw [heq, hx]
      simpa only [hx, Pi.add_apply, Pi.sub_apply] using ht
    _ = (∫ x in V, ‖∫ y, K (y, x) ∂ν‖ ∂μ) +
        ∫ x in V, ‖(∫ y, if ε n ≤ dist y x then f y * greenFunction V y x else 0 ∂ν) -
          (∫ y, f y * greenFunction V y x ∂ν)‖ ∂μ :=
      integral_add hk.integral_prod_right.norm (hff.integral_prod_right.sub hu.integral_prod_right).norm
    _ ≤ _ := add_le_add hbound le_rfl

#print axioms tendsto_integral_norm_sigmaFinite_varying_density_diagonal_cutoff
#print axioms sigmaFinite_integrable_density_observer_diagonal_cutoff
end HarmonicBalls
