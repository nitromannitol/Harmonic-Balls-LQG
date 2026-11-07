import HarmonicBalls.Proofs.Potential.TransposedGreenDomainExhaustion
import HarmonicBalls.Proofs.Potential.TransposedGreenL1Operator

/-! # Integrable-density Green potentials along domain exhaustions

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology

/-- Weighted kernels on every exhaustion domain are integrable against the full
source and full observer measures. -/
theorem integrable_density_exhaustion_product
    {V U : Set ℂ} (hV : IsOpen V) (hsub : V ⊆ U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ U)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict U)) := by
  have hi := integrable_density_transposedGreen_product hU hUb hν hf.norm hfi.norm
  apply hi.mono' (((hf.comp measurable_fst).mul (measurable_greenFunction_uncurry hV)).aestronglyMeasurable)
  filter_upwards with p
  change ‖f p.1 * greenFunction V p.1 p.2‖ ≤ ‖f p.1‖ * greenFunction U p.1 p.2
  rw [norm_mul, Real.norm_eq_abs (greenFunction V p.1 p.2),
    abs_of_nonneg (greenFunction_nonneg (hUb.subset hsub) p.1 p.2)]
  exact mul_le_mul_of_nonneg_left (Section6.greenFunction_le_of_subset hsub hUb p.1 p.2) (norm_nonneg _)

/-- The signed weighted potentials converge almost everywhere on the full domain. -/
theorem ae_tendsto_integrable_density_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    ∀ᵐ x ∂volume.restrict U,
      Tendsto (fun n => ∫ y, f y * greenFunction (V n) y x ∂ν) atTop
        (𝓝 (∫ y, f y * greenFunction U y x ∂ν)) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := integrable_density_transposedGreen_product hU hUb hν hf.norm hfi.norm
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
theorem tendsto_integral_norm_integrable_density_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Tendsto (fun n => ∫ x in U, ‖(∫ y, f y * greenFunction (V n) y x ∂ν) -
      (∫ y, f y * greenFunction U y x ∂ν)‖) atTop (𝓝 0) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  have hp := integrable_density_transposedGreen_product hU hUb hν hf hfi
  have ha := integrable_density_transposedGreen_product hU hUb hν hf.norm hfi.norm
  have hn (n : ℕ) := integrable_density_exhaustion_product (hopen n) (hsub n) hU hUb hν hf hfi
  have hi := hp.integral_prod_right
  have hb (n : ℕ) : ∀ᵐ x ∂volume.restrict U,
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
    (by filter_upwards [ae_tendsto_integrable_density_exhaustion V hopen hmono hU hUb hcover hν hf hfi] with x hx
        simpa only [Pi.sub_apply, sub_self, norm_zero] using (hx.sub tendsto_const_nhds).norm)
  simpa only [Pi.sub_apply, sub_self, norm_zero, integral_zero] using ht

/-- A single constant controls the potentials on subdomains, integrated over U. -/
theorem integrable_density_exhaustion_bound
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ U →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ U) →
      ∀ (f : ℂ → ℝ), Measurable f → Integrable f ν →
      (∫ x in U, ‖∫ y, f y * greenFunction V y x ∂ν‖) ≤ C * ∫ y, |f y| ∂ν := by
  obtain ⟨R, hR, hball⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨C, hC, hbound⟩ := integrable_density_transposedGreen_bound hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν f hf hfi
  have hn := integrable_density_exhaustion_product hV hsub hU hUb hν hf hfi
  have ha := integrable_density_transposedGreen_product hU hUb hν hf.norm hfi.norm
  have hbase := hbound hU hball ν hν (fun y => ‖f y‖) hf.norm hfi.norm
  calc
    (∫ x in U, ‖∫ y, f y * greenFunction V y x ∂ν‖) ≤
        ∫ x in U, ∫ y, ‖f y‖ * greenFunction U y x ∂ν := by
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
    _ = ∫ x in U, ‖∫ y, ‖f y‖ * greenFunction U y x ∂ν‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact integral_nonneg fun y => mul_nonneg (norm_nonneg _) (greenFunction_nonneg hUb y x)
    _ ≤ C * ∫ y, |f y| ∂ν := by
      simpa only [Real.norm_eq_abs, abs_abs] using hbase.2

/-- L¹ convergence persists when the integrable densities also converge in L¹. -/
theorem tendsto_integral_norm_varying_density_exhaustion
    (V : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (V n)) (hmono : Monotone V)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcover : (⋃ n, V n) = U) {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hν : ∀ᵐ y ∂ν, y ∈ U) {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (F : ℕ → ℂ → ℝ) (hF : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) ν)
    (hconv : Tendsto (fun n => ∫ y, |F n y - f y| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in U, ‖(∫ y, F n y * greenFunction (V n) y x ∂ν) -
      (∫ y, f y * greenFunction U y x ∂ν)‖) atTop (𝓝 0) := by
  have hsub (n : ℕ) : V n ⊆ U := by rw [← hcover]; exact subset_iUnion V n
  obtain ⟨C, hC, hbound⟩ := integrable_density_exhaustion_bound hU hUb
  have hfixed := tendsto_integral_norm_integrable_density_exhaustion V hopen hmono hU hUb hcover hν hf hfi
  have hupper : Tendsto (fun n => C * (∫ y, |F n y - f y| ∂ν) +
      ∫ x in U, ‖(∫ y, f y * greenFunction (V n) y x ∂ν) -
        (∫ y, f y * greenFunction U y x ∂ν)‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hconv).add hfixed
  apply squeeze_zero (fun n => integral_nonneg fun _ => norm_nonneg _) ?_ hupper
  intro n
  have hfn := integrable_density_exhaustion_product (hopen n) (hsub n) hU hUb hν (hF n) (hFi n)
  have hff := integrable_density_exhaustion_product (hopen n) (hsub n) hU hUb hν hf hfi
  have hd := integrable_density_exhaustion_product (hopen n) (hsub n) hU hUb hν ((hF n).sub hf) ((hFi n).sub hfi)
  have hu := integrable_density_transposedGreen_product hU hUb hν hf hfi
  have hpoint : ∀ᵐ x ∂volume.restrict U,
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
        ‖(∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖) := by
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
    _ = (∫ x in U, ‖∫ y, (F n y - f y) * greenFunction (V n) y x ∂ν‖) +
        ∫ x in U, ‖(∫ y, f y * greenFunction (V n) y x ∂ν) - (∫ y, f y * greenFunction U y x ∂ν)‖ :=
      integral_add hd.integral_prod_right.norm ((hff.integral_prod_right.sub hu.integral_prod_right).norm)
    _ ≤ _ := by
      gcongr
      exact hbound (hopen n) (hsub n) ν hν (fun y => F n y - f y) ((hF n).sub hf) ((hFi n).sub hfi)

#print axioms integrable_density_exhaustion_product
#print axioms ae_tendsto_integrable_density_exhaustion
#print axioms tendsto_integral_norm_integrable_density_exhaustion
#print axioms integrable_density_exhaustion_bound
#print axioms tendsto_integral_norm_varying_density_exhaustion
end HarmonicBalls
