import HarmonicBalls.Proofs.Potential.GeneralDomainTransposedFiniteSourceLaplacian
import HarmonicBalls.Proofs.Potential.WeightedTransposedGreenBound
import HarmonicBalls.Proofs.Potential.WeightedWholePlaneLaplacian

/-! # Laplacian of weighted transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

/-- The difference of two transposed potentials has the corresponding signed Laplacian. -/
theorem hasLaplacian_generalDomain_sub_transposedGreenPotential {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν η : Measure ℂ} [IsFiniteMeasure ν] [IsFiniteMeasure η]
    (hν : ∀ᵐ y ∂ν, y ∈ V) (hη : ∀ᵐ y ∂η, y ∈ V) :
    HasLaplacian (fun x => (∫ y, greenFunction V y x ∂ν) -
      ∫ y, greenFunction V y x ∂η) η ν V := by
  have hp := hasLaplacian_generalDomain_transposedGreenPotential hV hVb hν
  have hm := hasLaplacian_generalDomain_transposedGreenPotential hV hVb hη
  refine ⟨hp.1.sub hm.1, fun φ hφ => ?_⟩
  obtain ⟨_, hνφ, hνeq⟩ := hp.2 φ hφ
  obtain ⟨_, hηφ, hηeq⟩ := hm.2 φ hφ
  refine ⟨hηφ, hνφ, ?_⟩
  have heq : (fun x => ((∫ y, greenFunction V y x ∂ν) -
      ∫ y, greenFunction V y x ∂η) * Δ φ x) =
      fun x => (∫ y, greenFunction V y x ∂ν) * Δ φ x -
        (∫ y, greenFunction V y x ∂η) * Δ φ x := by
    funext x
    exact sub_mul _ _ _
  rw [heq, integral_sub (integrable_mul_laplacian_of_test hp.1 hφ)
    (integrable_mul_laplacian_of_test hm.1 hφ), hνeq, hηeq]
  simp only [integral_zero_measure]
  ring

/-- The weighted potential is integrable on the domain and agrees almost everywhere
with the difference of its positive and negative density potentials. -/
theorem weighted_transposedGreen_slice {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    IntegrableOn (fun x => ∫ y, f y * greenFunction V y x ∂ν) V ∧
    ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∫ y, f y * greenFunction V y x ∂ν) =
        (∫ y, greenFunction V y x ∂(positiveSource ν f)) -
        ∫ y, greenFunction V y x ∂(negativeSource ν f) := by
  let μp := positiveSource ν f
  let μm := negativeSource ν f
  let : IsFiniteMeasure μp := finite_positiveSource hf hC
  let : IsFiniteMeasure μm := finite_negativeSource hf hC
  have hνp : ∀ᵐ y ∂μp, y ∈ V := (withDensity_absolutelyContinuous ν _).ae_le hν
  have hνm : ∀ᵐ y ∂μm, y ∈ V := (withDensity_absolutelyContinuous ν _).ae_le hν
  have hp := (generalDomain_green_integrable_product_volume hV hVb hνp).prod_left_ae
  have hm := (generalDomain_green_integrable_product_volume hV hVb hνm).prod_left_ae
  refine ⟨(weighted_transposedGreen_integrable_product hV hVb hν hf hC).integral_prod_right, ?_⟩
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

/-- A bounded measurable signed density has distributional Laplacian equal to the
negative of the signed source on the bounded open domain. -/
theorem hasLaplacian_weighted_transposedGreen {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    IntegrableOn (fun x => ∫ y, f y * greenFunction V y x ∂ν) V ∧
    (∀ᵐ x ∂(volume.restrict V), Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∫ y, f y * greenFunction V y x ∂ν) =
        (∫ y, greenFunction V y x ∂(positiveSource ν f)) -
        ∫ y, greenFunction V y x ∂(negativeSource ν f)) ∧
    HasLaplacian (fun x => ∫ y, f y * greenFunction V y x ∂ν)
      (negativeSource ν f) (positiveSource ν f) V := by
  let : IsFiniteMeasure (positiveSource ν f) := finite_positiveSource hf hC
  let : IsFiniteMeasure (negativeSource ν f) := finite_negativeSource hf hC
  have hp : ∀ᵐ y ∂(positiveSource ν f), y ∈ V :=
    (withDensity_absolutelyContinuous ν _).ae_le hν
  have hm : ∀ᵐ y ∂(negativeSource ν f), y ∈ V :=
    (withDensity_absolutelyContinuous ν _).ae_le hν
  obtain ⟨hi, hae⟩ := weighted_transposedGreen_slice hV hVb hν hf hC
  refine ⟨hi, hae, ?_⟩
  apply (hasLaplacian_generalDomain_sub_transposedGreenPotential hV hVb hp hm).congr_ae_restrict_volume
    hV.measurableSet
  filter_upwards [hae] with x hx
  exact hx.2.symm

#print axioms hasLaplacian_generalDomain_sub_transposedGreenPotential
#print axioms weighted_transposedGreen_slice
#print axioms hasLaplacian_weighted_transposedGreen

end HarmonicBalls
