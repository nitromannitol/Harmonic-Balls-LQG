import HarmonicBalls.Proofs.Potential.IntegrableDensityTransposedLaplacian
import HarmonicBalls.Proofs.Potential.SigmaFiniteSourceObserverDensity

/-! # Sigma-finite density Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Laplacian Filter
open scoped ENNReal Topology

/-- The weighted potential is integrable on the domain and agrees almost everywhere
with the difference of its positive and negative density potentials. -/
theorem sigmaFinite_density_transposedGreen_slice {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    IntegrableOn (fun x => ∫ y, f y * greenFunction V y x ∂ν) V ∧
    ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∫ y, f y * greenFunction V y x ∂ν) =
        (∫ y, greenFunction V y x ∂(positiveSource ν f)) -
        ∫ y, greenFunction V y x ∂(negativeSource ν f) := by
  let μp := positiveSource ν f
  let μm := negativeSource ν f
  let : IsFiniteMeasure μp := finite_positiveSource_of_integrable hf hfi
  let : IsFiniteMeasure μm := finite_negativeSource_of_integrable hf hfi
  have hνp : ∀ᵐ y ∂μp, y ∈ V := (withDensity_absolutelyContinuous ν _).ae_le hν
  have hνm : ∀ᵐ y ∂μm, y ∈ V := (withDensity_absolutelyContinuous ν _).ae_le hν
  have hp := (generalDomain_green_integrable_product_volume hV hVb hνp).prod_left_ae
  have hm := (generalDomain_green_integrable_product_volume hV hVb hνm).prod_left_ae
  have hae : ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∫ y, f y * greenFunction V y x ∂ν) =
        (∫ y, greenFunction V y x ∂μp) - ∫ y, greenFunction V y x ∂μm := by
    filter_upwards [hp, hm] with x hxp hxm
    have hmp : Measurable (fun y => ENNReal.ofReal (max (f y) 0)) :=
      (hf.max measurable_const).ennreal_ofReal
    have hmm : Measurable (fun y => ENNReal.ofReal (max (-f y) 0)) :=
      (hf.neg.max measurable_const).ennreal_ofReal
    have htop : ∀ᵐ y ∂ν, ENNReal.ofReal (max (f y) 0) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have htop' : ∀ᵐ y ∂ν, ENNReal.ofReal (max (-f y) 0) < ∞ :=
      Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have hip : Integrable (fun y => max (f y) 0 * greenFunction V y x) ν := by
      change Integrable (fun y => greenFunction V y x) (ν.withDensity _) at hxp
      have h := (integrable_withDensity_iff_integrable_smul' hmp htop).1 hxp
      simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
    have him : Integrable (fun y => max (-f y) 0 * greenFunction V y x) ν := by
      change Integrable (fun y => greenFunction V y x) (ν.withDensity _) at hxm
      have h := (integrable_withDensity_iff_integrable_smul' hmm htop').1 hxm
      simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
    have heq (y : ℂ) : f y * greenFunction V y x =
        max (f y) 0 * greenFunction V y x - max (-f y) 0 * greenFunction V y x := by
      have h : max (f y) 0 - max (-f y) 0 = f y := by
        rcases le_total 0 (f y) with h | h
        · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
        · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      rw [← sub_mul, h]
    refine ⟨?_, ?_⟩
    · convert hip.sub him using 1
      funext y
      exact heq y
    · have hpEq : (∫ y, greenFunction V y x ∂μp) =
          ∫ y, max (f y) 0 * greenFunction V y x ∂ν := by
        simpa only [μp, positiveSource, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using
          (integral_withDensity_eq_integral_toReal_smul hmp htop (fun y => greenFunction V y x))
      have hmEq : (∫ y, greenFunction V y x ∂μm) =
          ∫ y, max (-f y) 0 * greenFunction V y x ∂ν := by
        simpa only [μm, negativeSource, positiveSource,
          ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using
          (integral_withDensity_eq_integral_toReal_smul hmm htop' (fun y => greenFunction V y x))
      change _ = (∫ y, greenFunction V y x ∂μp) - ∫ y, greenFunction V y x ∂μm
      rw [hpEq, hmEq]
      simp_rw [heq]
      exact integral_sub hip him

  refine ⟨?_, hae⟩
  have hi := (integrableOn_generalDomain_transposedGreenPotential hV hVb hνp).sub
    (integrableOn_generalDomain_transposedGreenPotential hV hVb hνm)
  exact (integrable_congr (hae.mono fun _ hx => hx.2.symm)).1 hi

/-- An integrable measurable signed density has distributional Laplacian equal to the
negative of the signed source on the bounded open domain. -/
theorem hasLaplacian_sigmaFinite_density_transposedGreen {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    IntegrableOn (fun x => ∫ y, f y * greenFunction V y x ∂ν) V ∧
    (∀ᵐ x ∂(volume.restrict V), Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∫ y, f y * greenFunction V y x ∂ν) =
        (∫ y, greenFunction V y x ∂(positiveSource ν f)) -
        ∫ y, greenFunction V y x ∂(negativeSource ν f)) ∧
    HasLaplacian (fun x => ∫ y, f y * greenFunction V y x ∂ν)
      (negativeSource ν f) (positiveSource ν f) V := by
  let : IsFiniteMeasure (positiveSource ν f) := finite_positiveSource_of_integrable hf hfi
  let : IsFiniteMeasure (negativeSource ν f) := finite_negativeSource_of_integrable hf hfi
  have hp : ∀ᵐ y ∂(positiveSource ν f), y ∈ V :=
    (withDensity_absolutelyContinuous ν _).ae_le hν
  have hm : ∀ᵐ y ∂(negativeSource ν f), y ∈ V :=
    (withDensity_absolutelyContinuous ν _).ae_le hν
  obtain ⟨hi, hae⟩ := sigmaFinite_density_transposedGreen_slice hV hVb hν hf hfi
  refine ⟨hi, hae, ?_⟩
  apply (hasLaplacian_generalDomain_sub_transposedGreenPotential hV hVb hp hm).congr_ae_restrict_volume
    hV.measurableSet
  filter_upwards [hae] with x hx
  exact hx.2.symm


/-- Planar volume has the local upper growth needed for the observer estimates. -/
private theorem planar_volume_upper_growth :
    ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        volume (ball z r) ≤ ENNReal.ofReal (r ^ β) := by
  intro R hR
  obtain ⟨_, _, r₀, hr₀, hg⟩ := volumeGrowth_volume R
  exact ⟨r₀, 1, hr₀, by norm_num, fun r hr hrr z hz => (hg r hr hrr z hz).2⟩

/-- The literal transposed kernel is integrable against source and planar volume. -/
theorem sigmaFinite_density_transposedGreen_product {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) :=
  sigmaFinite_integrable_density_green_product_of_local_upper_growth
    planar_volume_upper_growth hV hVb hν hf hfi

/-- L¹ convergence of densities gives L¹ convergence of their transposed potentials. -/
theorem tendsto_sigmaFinite_density_transposedGreen_L1 {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    (F : ℕ → ℂ → ℝ) (f : ℂ → ℝ)
    (hF : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) ν)
    (hf : Measurable f) (hfi : Integrable f ν)
    (hconv : Tendsto (fun n => ∫ y, ‖F n y - f y‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, ‖(∫ y, F n y * greenFunction V y x ∂ν) -
      (∫ y, f y * greenFunction V y x ∂ν)‖) atTop (𝓝 0) := by
  obtain ⟨R, hsub⟩ := hVb.subset_ball (0 : ℂ)
  have hsub' : V ⊆ ball (0 : ℂ) (max R 1) :=
    hsub.trans (ball_subset_ball (le_max_left _ _))
  exact tendsto_integral_norm_sigmaFinite_integrable_density_observer
    planar_volume_upper_growth (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    hV hsub' hν F f hF hFi hf hfi hconv

/-- Bounded tests pair continuously with L¹-convergent source densities. -/
theorem tendsto_sigmaFinite_density_test {ν : Measure ℂ}
    (F : ℕ → ℂ → ℝ) (f φ : ℂ → ℝ)
    (hFi : ∀ n, Integrable (F n) ν) (hfi : Integrable f ν)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ᵐ y ∂ν, ‖φ y‖ ≤ B)
    (hconv : Tendsto (fun n => ∫ y, ‖F n y - f y‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, F n y * φ y ∂ν) atTop
      (𝓝 (∫ y, f y * φ y ∂ν)) := by
  have hp (g : ℂ → ℝ) (hg : Integrable g ν) : Integrable (fun y => g y * φ y) ν :=
    hg.mul_bdd hφ.aestronglyMeasurable hB
  have hbound (n : ℕ) :
      ‖(∫ y, F n y * φ y ∂ν) - (∫ y, f y * φ y ∂ν)‖ ≤
        B * ∫ y, ‖F n y - f y‖ ∂ν := by
    rw [← integral_sub (hp _ (hFi n)) (hp _ hfi), ← integral_const_mul]
    calc
      _ ≤ ∫ y, ‖F n y * φ y - f y * φ y‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ y, B * ‖F n y - f y‖ ∂ν := by
        apply integral_mono_ae ((hp _ (hFi n)).sub (hp _ hfi)).norm
          (((hFi n).sub hfi).norm.const_mul B)
        filter_upwards [hB] with y hy
        simp only [Pi.sub_apply]
        rw [← sub_mul, norm_mul]
        exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (mul_comm _ _)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa only [mul_zero] using tendsto_const_nhds.mul hconv

/-- The signed weighted source acts as integration against the density. -/
theorem integral_negativeSource_sub_positiveSource {ν : Measure ℂ}
    {f φ : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ᵐ y ∂ν, ‖φ y‖ ≤ B) :
    (∫ y, φ y ∂(negativeSource ν f)) - (∫ y, φ y ∂(positiveSource ν f)) =
      -(∫ y, f y * φ y ∂ν) := by
  have part (g : ℂ → ℝ) (hg : Measurable g) (hgi : Integrable g ν) :
      Integrable (fun y => max (g y) 0 * φ y) ν := by
    apply (hgi.norm.mono' (hg.max measurable_const).aestronglyMeasurable ?_).mul_bdd
      hφ.aestronglyMeasurable hB
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hp := part f hf hfi
  have hm := part (fun y => -f y) hf.neg hfi.neg
  have heq (g : ℂ → ℝ) (hg : Measurable g) :
      (∫ y, φ y ∂(positiveSource ν g)) = ∫ y, max (g y) 0 * φ y ∂ν := by
    simpa only [positiveSource, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using
      (integral_withDensity_eq_integral_toReal_smul (μ := ν) (hg.max (measurable_const : Measurable (fun _ : ℂ => (0 : ℝ)))).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ)
  change (∫ y, φ y ∂(positiveSource ν (fun y => -f y))) - _ = _
  rw [heq (fun y => -f y) hf.neg, heq f hf, ← integral_sub hm hp, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  have h : max (f y) 0 - max (-f y) 0 = f y := by
    rcases le_total 0 (f y) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  have hh := congrArg (fun a : ℝ => a * φ y) h
  linarith

/-- Distributional test identities converge along L¹-convergent densities. -/
theorem tendsto_sigmaFinite_density_distributional_tests {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    (F : ℕ → ℂ → ℝ) (f φ : ℂ → ℝ)
    (hF : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) ν)
    (hf : Measurable f) (hfi : Integrable f ν) (hφ : IsTestFunction V φ)
    (hconv : Tendsto (fun n => ∫ y, ‖F n y - f y‖ ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (∫ y, F n y * greenFunction V y x ∂ν) * Δ φ x)
      atTop (𝓝 (∫ x, (∫ y, f y * greenFunction V y x ∂ν) * Δ φ x)) := by
  obtain ⟨B, hB⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have ht := tendsto_sigmaFinite_density_test F f φ hFi hfi hφ.1.continuous.measurable
    (Filter.Eventually.of_forall hB) hconv
  have heq (g : ℂ → ℝ) (hg : Measurable g) (hgi : Integrable g ν) :
      (∫ x, (∫ y, g y * greenFunction V y x ∂ν) * Δ φ x) =
        -(∫ y, g y * φ y ∂ν) := by
    rw [((hasLaplacian_sigmaFinite_density_transposedGreen hV hVb hν hg hgi).2.2.2 φ hφ).2.2]
    exact integral_negativeSource_sub_positiveSource hg hgi hφ.1.continuous.measurable
      (Filter.Eventually.of_forall hB)
  simp_rw [heq _ hf hfi, heq _ (hF _) (hFi _)]
  exact ht.neg

end HarmonicBalls
