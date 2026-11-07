import HarmonicBalls.Proofs.Potential.FiniteSourceObservationIntegrability

/-! # Signed weighted transposed Green duality

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Bounded measurable source and observer densities preserve mixed and slice
integrability, and their transposed Green pairings agree by Fubini. -/
theorem weighted_transposedGreen_fubini_duality
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) (f g : ℂ → ℝ) (C D : ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfC : ∀ y, ‖f y‖ ≤ C) (hgD : ∀ x, ‖g x‖ ≤ D) :
    Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) ∧
    (∀ᵐ x ∂μ.restrict V, Integrable (fun y => f y * greenFunction V y x) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => g x * greenFunction V y x) (μ.restrict V)) ∧
    (∀ᵐ x ∂μ.restrict V, Integrable (fun y => f y * g x * greenFunction V y x) ν) ∧
    (∀ᵐ y ∂ν, Integrable (fun x => f y * g x * greenFunction V y x) (μ.restrict V)) ∧
    Integrable (fun x => g x * ∫ y, f y * greenFunction V y x ∂ν) (μ.restrict V) ∧
    Integrable (fun y => f y * ∫ x, g x * greenFunction V y x ∂μ.restrict V) ν ∧
    (∫ x, g x * (∫ y, f y * greenFunction V y x ∂ν) ∂μ.restrict V) =
      ∫ y, f y * (∫ x, g x * greenFunction V y x ∂μ.restrict V) ∂ν := by
  have hp := generalDomain_green_integrable_product_of_local_upper_growth hup hV hVb hν
  have hmeas := measurable_greenFunction_uncurry hV
  have hF : Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) := by
    apply (hp.norm.const_mul C).mono' (((hf.comp measurable_fst).mul hmeas).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖f p.1 * greenFunction V p.1 p.2‖ ≤ C * ‖greenFunction V p.1 p.2‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hfC p.1) (norm_nonneg _)
  have hG : Integrable (fun p : ℂ × ℂ => g p.2 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) := by
    apply (hp.norm.const_mul D).mono' (((hg.comp measurable_snd).mul hmeas).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖g p.2 * greenFunction V p.1 p.2‖ ≤ D * ‖greenFunction V p.1 p.2‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hgD p.2) (norm_nonneg _)
  have hFG : Integrable (fun p : ℂ × ℂ => f p.1 * g p.2 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) := by
    apply (hF.norm.const_mul D).mono' ((((hf.comp measurable_fst).mul
      (hg.comp measurable_snd)).mul hmeas).aestronglyMeasurable)
    filter_upwards [] with p
    calc
      ‖f p.1 * g p.2 * greenFunction V p.1 p.2‖ =
          ‖g p.2‖ * ‖f p.1 * greenFunction V p.1 p.2‖ := by simp only [norm_mul]; ring
      _ ≤ D * ‖f p.1 * greenFunction V p.1 p.2‖ :=
        mul_le_mul_of_nonneg_right (hgD p.2) (norm_nonneg _)
  have heq₁ (x : ℂ) : (∫ y, f y * g x * greenFunction V y x ∂ν) =
      g x * ∫ y, f y * greenFunction V y x ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have heq₂ (y : ℂ) : (∫ x, f y * g x * greenFunction V y x ∂μ.restrict V) =
      f y * ∫ x, g x * greenFunction V y x ∂μ.restrict V := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  refine ⟨hFG, hF.prod_left_ae, hG.prod_right_ae, hFG.prod_left_ae,
    hFG.prod_right_ae, ?_, ?_, ?_⟩
  · simpa only [heq₁] using hFG.integral_prod_right
  · simpa only [heq₂] using hFG.integral_prod_left
  · simpa only [heq₁, heq₂] using (integral_integral_swap (f := fun y x => f y * g x * greenFunction V y x) hFG).symm

#print axioms weighted_transposedGreen_fubini_duality

end HarmonicBalls
