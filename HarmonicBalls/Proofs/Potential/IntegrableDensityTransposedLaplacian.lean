import HarmonicBalls.Proofs.Potential.WeightedTransposedLaplacian

/-! # Integrable density transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Laplacian
open scoped ENNReal

/-- An integrable positive density defines a finite source. -/
theorem finite_positiveSource_of_integrable {ν : Measure ℂ}
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    IsFiniteMeasure (positiveSource ν f) := by
  apply isFiniteMeasure_withDensity_ofReal
  apply (hfi.norm.mono' (hf.max measurable_const).aestronglyMeasurable ?_).2
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_abs_self _) (abs_nonneg _)

/-- An integrable negative density defines a finite source. -/
theorem finite_negativeSource_of_integrable {ν : Measure ℂ}
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    IsFiniteMeasure (negativeSource ν f) :=
  finite_positiveSource_of_integrable hf.neg hfi.neg

/-- An integrable density gives an integrable weighted Green kernel on the product. -/
theorem integrable_density_transposedGreen_product {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) := by
  have part (g : ℂ → ℝ) (hg : Measurable g) (hgi : Integrable g ν) :
      Integrable (fun p : ℂ × ℂ => max (g p.1) 0 * greenFunction V p.1 p.2)
        (ν.prod (volume.restrict V)) := by
    let : IsFiniteMeasure (positiveSource ν g) := finite_positiveSource_of_integrable hg hgi
    have hc : ∀ᵐ y ∂(positiveSource ν g), y ∈ V :=
      (withDensity_absolutelyContinuous ν _).ae_le hν
    have hi := generalDomain_green_integrable_product_volume hV hVb hc
    have hd : Measurable (fun y => ENNReal.ofReal (max (g y) 0)) :=
      (hg.max measurable_const).ennreal_ofReal
    rw [positiveSource, prod_withDensity_left hd] at hi
    have h := (integrable_withDensity_iff_integrable_smul'
      (hd.comp measurable_fst) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hi
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  have hp := part f hf hfi
  have hm := part (fun y => -f y) hf.neg hfi.neg
  convert hp.sub hm using 1
  funext p
  have h : max (f p.1) 0 - max (-f p.1) 0 = f p.1 := by
    rcases le_total 0 (f p.1) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
  simp only [Pi.sub_apply, ← sub_mul, h]

/-- The weighted potential is integrable on the domain and agrees almost everywhere
with the difference of its positive and negative density potentials. -/
theorem integrable_density_transposedGreen_slice {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
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
theorem hasLaplacian_integrable_density_transposedGreen {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
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
  obtain ⟨hi, hae⟩ := integrable_density_transposedGreen_slice hV hVb hν hf hfi
  refine ⟨hi, hae, ?_⟩
  apply (hasLaplacian_generalDomain_sub_transposedGreenPotential hV hVb hp hm).congr_ae_restrict_volume
    hV.measurableSet
  filter_upwards [hae] with x hx
  exact hx.2.symm


end HarmonicBalls
