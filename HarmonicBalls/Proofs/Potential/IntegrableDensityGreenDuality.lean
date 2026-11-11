import HarmonicBalls.Proofs.Potential.IntegrableDensityTransposedLaplacian

/-! # Integrable-density transposed Green duality

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- An integrable source density and an almost everywhere bounded observer yield
integrable mixed kernels and slices, and the signed Green pairings agree. -/
theorem integrable_density_transposedGreen_fubini_duality
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f g : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (hg : Measurable g) {D : ℝ} (hgD : ∀ᵐ x ∂volume.restrict V, ‖g x‖ ≤ D) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2 * g p.2)
      (ν.prod (volume.restrict V)) ∧
    (∀ᵐ x ∂volume.restrict V, Integrable (fun y => f y * greenFunction V y x) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => g x * greenFunction V y x) (volume.restrict V)) ∧
    (∀ᵐ x ∂volume.restrict V, Integrable (fun y => f y * greenFunction V y x * g x) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => f y * greenFunction V y x * g x) (volume.restrict V)) ∧
    Integrable (fun x => g x * ∫ y, f y * greenFunction V y x ∂ν) (volume.restrict V) ∧
    Integrable (fun y => f y * ∫ x, g x * greenFunction V y x ∂volume.restrict V) ν ∧
    (∫ x, g x * (∫ y, f y * greenFunction V y x ∂ν) ∂volume.restrict V) =
      ∫ y, f y * (∫ x, g x * greenFunction V y x ∂volume.restrict V) ∂ν := by
  have hF := integrable_density_transposedGreen_product hV hVb hν hf hfi
  have hp := generalDomain_green_integrable_product_volume hV hVb hν
  have hm := measurable_greenFunction_uncurry hV
  have hbound : ∀ᵐ p ∂ν.prod (volume.restrict V), ‖g p.2‖ ≤ D :=
    Measure.quasiMeasurePreserving_snd.ae hgD
  have hG : Integrable (fun p : ℂ × ℂ => g p.2 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) := by
    apply (hp.norm.const_mul D).mono' (((hg.comp measurable_snd).mul hm).aestronglyMeasurable)
    filter_upwards [hbound] with p h
    change ‖g p.2 * greenFunction V p.1 p.2‖ ≤ D * ‖greenFunction V p.1 p.2‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have hFG : Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2 * g p.2)
      (ν.prod (volume.restrict V)) := by
    apply (hF.norm.const_mul D).mono' ((((hf.comp measurable_fst).mul hm).mul
      (hg.comp measurable_snd)).aestronglyMeasurable)
    filter_upwards [hbound] with p h
    change ‖f p.1 * greenFunction V p.1 p.2 * g p.2‖ ≤
      D * ‖f p.1 * greenFunction V p.1 p.2‖
    rw [norm_mul, mul_comm (‖f p.1 * greenFunction V p.1 p.2‖)]
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
  have heq₁ (x : ℂ) : (∫ y, f y * greenFunction V y x * g x ∂ν) =
      g x * ∫ y, f y * greenFunction V y x ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have heq₂ (y : ℂ) : (∫ x, f y * greenFunction V y x * g x ∂volume.restrict V) =
      f y * ∫ x, g x * greenFunction V y x ∂volume.restrict V := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  refine ⟨hFG, hF.prod_left_ae, hG.prod_right_ae, hFG.prod_left_ae,
    hFG.prod_right_ae, ?_, ?_, ?_⟩
  · simpa only [heq₁] using hFG.integral_prod_right
  · simpa only [heq₂] using hFG.integral_prod_left
  · simpa only [heq₁, heq₂] using
      (integral_integral_swap (f := fun y x => f y * greenFunction V y x * g x) hFG).symm


end HarmonicBalls
