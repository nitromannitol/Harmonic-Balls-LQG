import HarmonicBalls.Proofs.Potential.FiniteSourceTransposedSourceFreeHarmonicity
import HarmonicBalls.Proofs.Potential.IntegrableDensityTransposedLaplacian

/-! # Source-free potentials of sigma-finite integrable densities

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls
open MeasureTheory Metric Set Filter InnerProductSpace
open scoped ENNReal Topology

private theorem density_zero_on {ν : Measure ℂ} {g : ℂ → ℝ} {U : Set ℂ}
    (hg : Measurable g) (hU : IsOpen U) (hz : ∀ᵐ y ∂ν, y ∈ U → g y = 0) :
    positiveSource ν g U = 0 := by
  rw [positiveSource, withDensity_apply _ hU.measurableSet]
  apply (lintegral_eq_zero_iff (hg.max measurable_const).ennreal_ofReal).2
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem hU.measurableSet] with y hy hyU
  simp only [hy hyU, max_self, ENNReal.ofReal_zero, Pi.zero_apply]

private theorem integrable_green_of_source_free {V U : Set ℂ} {μ : Measure ℂ}
    [IsFiniteMeasure μ] (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hμV : μ Vᶜ = 0) (hU : IsOpen U) (hUV : U ⊆ V) (hμU : μ U = 0)
    {x : ℂ} (hx : x ∈ U) : Integrable (fun y => greenFunction V y x) μ := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free hVb hU
    isCompact_singleton (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr (hUV hx))
  have hae : ∀ᵐ y ∂μ, y ∈ V \ U := by
    rw [ae_iff]
    apply measure_mono_null (show (V \ U)ᶜ ⊆ Vᶜ ∪ U from by
      intro y hy
      by_cases hv : y ∈ V
      · right
        by_contra hu
        exact hy ⟨hv, hu⟩
      · exact Or.inl hv)
    exact measure_union_null hμV hμU
  apply (integrable_const (max C 0)).mono'
    ((measurable_greenFunction_uncurry hV).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [hae] with y hy
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg (le_max_right C 0)] using
    (hC y hy x (mem_singleton x)).trans (le_max_left C 0)

/-- An integrable signed density vanishing almost everywhere on an open set has
an everywhere integrable transposed Green kernel and a harmonic potential there. -/
theorem sigmaFinite_integrable_density_transposedGreen_source_free {V U : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [SigmaFinite ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    (hU : IsOpen U) (hUV : U ⊆ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (hz : ∀ᵐ y ∂ν, y ∈ U → f y = 0) :
    (∀ x ∈ U, Integrable (fun y => f y * greenFunction V y x) ν) ∧
    HarmonicOnNhd (fun x => ∫ y, f y * greenFunction V y x ∂ν) U := by
  let μp := positiveSource ν f
  let μm := negativeSource ν f
  let : IsFiniteMeasure μp := finite_positiveSource_of_integrable hf hfi
  let : IsFiniteMeasure μm := finite_negativeSource_of_integrable hf hfi
  have hzneg : ∀ᵐ y ∂ν, y ∈ U → -f y = 0 := by
    filter_upwards [hz] with y hy hyU
    simp only [hy hyU, neg_zero]
  have hpU : μp U = 0 := density_zero_on hf hU hz
  have hmU : μm U = 0 := density_zero_on hf.neg hU hzneg
  have hνV : ν Vᶜ = 0 := (ae_iff.mp hν)
  have hpV : μp Vᶜ = 0 := withDensity_absolutelyContinuous _ _ hνV
  have hmV : μm Vᶜ = 0 := withDensity_absolutelyContinuous _ _ hνV
  have hmp : Measurable (fun y => ENNReal.ofReal (max (f y) 0)) :=
    (hf.max measurable_const).ennreal_ofReal
  have hmm : Measurable (fun y => ENNReal.ofReal (max (-f y) 0)) :=
    (hf.neg.max measurable_const).ennreal_ofReal
  have htop : ∀ᵐ y ∂ν, ENNReal.ofReal (max (f y) 0) < ∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have htop' : ∀ᵐ y ∂ν, ENNReal.ofReal (max (-f y) 0) < ∞ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hs (x : ℂ) (hx : x ∈ U) :
      Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∫ y, f y * greenFunction V y x ∂ν) =
        (∫ y, greenFunction V y x ∂μp) - ∫ y, greenFunction V y x ∂μm := by
    have hxp := integrable_green_of_source_free hV hVb hpV hU hUV hpU hx
    have hxm := integrable_green_of_source_free hV hVb hmV hU hUV hmU hx
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
      rw [hpEq, hmEq]
      simp_rw [heq]
      exact integral_sub hip him
  refine ⟨fun x hx => (hs x hx).1, ?_⟩
  have hh := (harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb hpV hU hUV hpU).sub
    (harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb hmV hU hUV hmU)
  intro x hx
  apply (harmonicAt_congr_nhds ?_).2 (hh x hx)
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hs y hy).2

#print axioms sigmaFinite_integrable_density_transposedGreen_source_free
end HarmonicBalls
