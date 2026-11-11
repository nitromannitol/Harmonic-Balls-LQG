import HarmonicBalls.Proofs.Potential.WholePlaneFiniteSourceLaplacian
import HarmonicBalls.Proofs.Potential.WholePlaneSourceTruncation
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Weighted whole-plane potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian
open scoped ENNReal

/-- The positive density associated with a real source weight. -/
noncomputable def positiveSource (ν : Measure ℂ) (f : ℂ → ℝ) : Measure ℂ :=
  ν.withDensity (fun y => ENNReal.ofReal (max (f y) 0))

/-- The negative density associated with a real source weight. -/
noncomputable def negativeSource (ν : Measure ℂ) (f : ℂ → ℝ) : Measure ℂ :=
  positiveSource ν (fun y => -f y)

/-- A bounded measurable positive density gives a finite source. -/
theorem finite_positiveSource {ν : Measure ℂ} [IsFiniteMeasure ν]
    {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    IsFiniteMeasure (positiveSource ν f) := by
  apply isFiniteMeasure_withDensity_ofReal
  apply (Integrable.of_bound (hf.max measurable_const).aestronglyMeasurable C ?_).2
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC y))
    (le_trans (norm_nonneg (f y)) (hC y))

/-- A bounded measurable negative density gives a finite source. -/
theorem finite_negativeSource {ν : Measure ℂ} [IsFiniteMeasure ν]
    {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    IsFiniteMeasure (negativeSource ν f) :=
  finite_positiveSource hf.neg (fun y => by simpa using hC y)

/-- Subtracting whole-plane positive potentials reverses their source order. -/
theorem hasLaplacian_wholePlane_sub_greenPotential {ν η : Measure ℂ}
    [IsFiniteMeasure ν] [IsFiniteMeasure η] {K : Set ℂ}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hη : η Kᶜ = 0) :
    HasLaplacian (greenPotential univ ν - greenPotential univ η) η ν univ := by
  have hp := hasLaplacian_wholePlane_greenPotential hK hν
  have hm := hasLaplacian_wholePlane_greenPotential hK hη
  refine ⟨hp.1.sub hm.1, fun φ hφ => ?_⟩
  obtain ⟨_, hνφ, hνeq⟩ := hp.2 φ hφ
  obtain ⟨_, hηφ, hηeq⟩ := hm.2 φ hφ
  refine ⟨hηφ, hνφ, ?_⟩
  have heq : (fun x => (greenPotential univ ν - greenPotential univ η) x * Δ φ x) =
      fun x => greenPotential univ ν x * Δ φ x - greenPotential univ η x * Δ φ x := by
    funext x
    simp only [Pi.sub_apply, sub_mul]
  rw [heq, integral_sub (integrable_mul_laplacian_of_test hp.1 hφ)
    (integrable_mul_laplacian_of_test hm.1 hφ), hνeq, hηeq]
  simp only [integral_zero_measure]
  ring

/-- On bounded observer sets, weighted source slices are integrable almost everywhere,
    and their integral is the difference of the two positive potentials. -/
theorem weighted_wholePlane_slice {ν : Measure ℂ} [IsFiniteMeasure ν]
    {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    {K V : Set ℂ} (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (hV : Bornology.IsBounded V) :
    ∀ᵐ x ∂(volume.restrict V),
      Integrable (fun y => f y * newtonKernel y x) ν ∧
      (∫ y, f y * newtonKernel y x ∂ν) =
        (greenPotential univ (positiveSource ν f) -
          greenPotential univ (negativeSource ν f)) x := by
  let μp := positiveSource ν f
  let μm := negativeSource ν f
  let : IsFiniteMeasure μp := finite_positiveSource hf hC
  let : IsFiniteMeasure μm := finite_positiveSource hf.neg (fun y => by simpa using hC y)
  have hνp : μp Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hν
  have hνm : μm Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hν
  have hp := (wholePlane_kernel_integrable_product hK hνp hV).prod_left_ae
  have hm := (wholePlane_kernel_integrable_product hK hνm hV).prod_left_ae
  filter_upwards [hp, hm] with x hxp hxm
  have hmp : Measurable (fun y => ENNReal.ofReal (max (f y) 0)) :=
    (hf.max measurable_const).ennreal_ofReal
  have hmm : Measurable (fun y => ENNReal.ofReal (max (-f y) 0)) :=
    (hf.neg.max measurable_const).ennreal_ofReal
  have htop : ∀ᵐ y ∂ν, ENNReal.ofReal (max (f y) 0) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have htop' : ∀ᵐ y ∂ν, ENNReal.ofReal (max (-f y) 0) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hip : Integrable (fun y => max (f y) 0 * newtonKernel y x) ν := by
    simp only [greenFunction_univ_eq_newtonKernel, μp, positiveSource] at hxp
    have h := (integrable_withDensity_iff_integrable_smul' hmp htop).1 hxp
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  have him : Integrable (fun y => max (-f y) 0 * newtonKernel y x) ν := by
    simp only [greenFunction_univ_eq_newtonKernel, μm, negativeSource, positiveSource] at hxm
    have h := (integrable_withDensity_iff_integrable_smul' hmm htop').1 hxm
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  have heq (y : ℂ) : f y * newtonKernel y x =
      max (f y) 0 * newtonKernel y x - max (-f y) 0 * newtonKernel y x := by
    have h : max (f y) 0 - max (-f y) 0 = f y := by
      rcases le_total 0 (f y) with h | h
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
    rw [← sub_mul, h]
  refine ⟨?_, ?_⟩
  · convert hip.sub him using 1
    funext y
    exact heq y
  · have hpEq : greenPotential univ μp x = ∫ y, max (f y) 0 * newtonKernel y x ∂ν := by
      simpa only [μp, positiveSource, greenPotential, greenFunction_univ_eq_newtonKernel,
        newtonKernel_comm, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul hmp htop (fun y => newtonKernel y x))
    have hmEq : greenPotential univ μm x = ∫ y, max (-f y) 0 * newtonKernel y x ∂ν := by
      simpa only [μm, negativeSource, positiveSource, greenPotential, greenFunction_univ_eq_newtonKernel,
        newtonKernel_comm, ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using
        (integral_withDensity_eq_integral_toReal_smul hmm htop' (fun y => newtonKernel y x))
    change _ = greenPotential univ μp x - greenPotential univ μm x
    rw [hpEq, hmEq]
    simp_rw [heq]
    exact integral_sub hip him

/-- A bounded measurable weight gives a locally integrable whole-plane potential.
Its distributional Laplacian is the negative of the signed source, represented
by its two genuine positive density measures. -/
theorem hasLaplacian_weighted_wholePlane {ν : Measure ℂ} [IsFiniteMeasure ν]
    {f : ℂ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C)
    {K : Set ℂ} (hK : IsCompact K) (hν : ν Kᶜ = 0) :
    (∀ᵐ x ∂volume, Integrable (fun y => f y * newtonKernel y x) ν ∧
      (∫ y, f y * newtonKernel y x ∂ν) =
        (greenPotential univ (positiveSource ν f) -
          greenPotential univ (negativeSource ν f)) x) ∧
    HasLaplacian (fun x => ∫ y, f y * newtonKernel y x ∂ν)
      (negativeSource ν f) (positiveSource ν f) univ := by
  let : IsFiniteMeasure (positiveSource ν f) := finite_positiveSource hf hC
  let : IsFiniteMeasure (negativeSource ν f) :=
    finite_positiveSource hf.neg (fun y => by simpa using hC y)
  have hp : positiveSource ν f Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hν
  have hm : negativeSource ν f Kᶜ = 0 := withDensity_absolutelyContinuous _ _ hν
  have hae : ∀ᵐ x ∂volume, Integrable (fun y => f y * newtonKernel y x) ν ∧
      (∫ y, f y * newtonKernel y x ∂ν) =
        (greenPotential univ (positiveSource ν f) -
          greenPotential univ (negativeSource ν f)) x := by
    have h := (ae_restrict_iUnion_iff (μ := volume)
      (fun n : ℕ => ball (0 : ℂ) n) _).2 (fun n =>
        weighted_wholePlane_slice hf hC hK hν isBounded_ball)
    simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ] using h
  refine ⟨hae, ?_⟩
  apply (hasLaplacian_wholePlane_sub_greenPotential hK hp hm).congr_ae_restrict_volume
    MeasurableSet.univ
  rw [Measure.restrict_univ]
  filter_upwards [hae] with x hx
  exact hx.2.symm


end HarmonicBalls
