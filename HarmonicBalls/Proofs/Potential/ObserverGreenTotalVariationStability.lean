import HarmonicBalls.Proofs.Potential.SigmaFiniteSourceObserverDensity
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-! # Total variation stability of transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- The Radon–Nikodym density difference represents the signed difference of finite measures,
and its L¹ norm is the total variation mass. -/
theorem finite_measure_difference_density (ν₁ ν₂ : Measure ℂ)
    [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    let ρ := ν₁ + ν₂
    let f : ℂ → ℝ := fun y => (ν₁.rnDeriv ρ y).toReal - (ν₂.rnDeriv ρ y).toReal
    Measurable f ∧ Integrable f ρ ∧
    ρ.withDensityᵥ f = ν₁.toSignedMeasure - ν₂.toSignedMeasure ∧
    (∫ y, ‖f y‖ ∂ρ) = (ν₁.toSignedMeasure - ν₂.toSignedMeasure).totalVariation.real univ := by
  dsimp only
  let ρ := ν₁ + ν₂
  let f₁ : ℂ → ℝ := fun y => (ν₁.rnDeriv ρ y).toReal
  let f₂ : ℂ → ℝ := fun y => (ν₂.rnDeriv ρ y).toReal
  have ha₁ : ν₁ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have ha₂ : ν₂ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hi₁ : Integrable f₁ ρ := by
    simpa only [f₁, integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := ν₁) (ν := ρ) (s := univ) (measure_ne_top ν₁ univ))
  have hi₂ : Integrable f₂ ρ := by
    simpa only [f₂, integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := ν₂) (ν := ρ) (s := univ) (measure_ne_top ν₂ univ))
  have hd₁ : ρ.withDensityᵥ f₁ = ν₁.toSignedMeasure := by
    have h := withDensityᵥ_toReal (μ := ρ) (Measure.measurable_rnDeriv ν₁ ρ).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top ν₁ ρ).ne
    simpa only [f₁, Measure.withDensity_rnDeriv_eq ν₁ ρ ha₁] using h
  have hd₂ : ρ.withDensityᵥ f₂ = ν₂.toSignedMeasure := by
    have h := withDensityᵥ_toReal (μ := ρ) (Measure.measurable_rnDeriv ν₂ ρ).aemeasurable
      (Measure.lintegral_rnDeriv_lt_top ν₂ ρ).ne
    simpa only [f₂, Measure.withDensity_rnDeriv_eq ν₂ ρ ha₂] using h
  have hi : Integrable (fun y => f₁ y - f₂ y) ρ := hi₁.sub hi₂
  have hd : ρ.withDensityᵥ (fun y => f₁ y - f₂ y) = ν₁.toSignedMeasure - ν₂.toSignedMeasure := by
    rw [withDensityᵥ_sub' hi₁ hi₂, hd₁, hd₂]
  refine ⟨(Measure.measurable_rnDeriv ν₁ ρ).ennreal_toReal.sub
    (Measure.measurable_rnDeriv ν₂ ρ).ennreal_toReal, hi, hd, ?_⟩
  rw [← hd, SignedMeasure.totalVariation_eq_variation, Measure.variation_withDensityᵥ hi,
    measureReal_def, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_norm_eq_lintegral_enorm hi, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

/-- The observed L¹ distance of two transposed Green potentials is bounded by
 the total variation mass of their signed source difference. -/
theorem observer_green_totalVariation_bound
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball (0 : ℂ) R →
      ∀ (ν₁ ν₂ : Measure ℂ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂],
      (∀ᵐ y ∂ν₁, y ∈ V) → (∀ᵐ y ∂ν₂, y ∈ V) →
      (∫ x in V, ‖(∫ y, greenFunction V y x ∂ν₁) -
        (∫ y, greenFunction V y x ∂ν₂)‖ ∂μ) ≤
      C * (ν₁.toSignedMeasure - ν₂.toSignedMeasure).totalVariation.real univ := by
  obtain ⟨C, hC, hb⟩ := sigmaFinite_integrable_density_observer_bound hup hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν₁ ν₂ _ _ hν₁ hν₂
  let ρ := ν₁ + ν₂
  let f₁ : ℂ → ℝ := fun y => (ν₁.rnDeriv ρ y).toReal
  let f₂ : ℂ → ℝ := fun y => (ν₂.rnDeriv ρ y).toReal
  have ha₁ : ν₁ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have ha₂ : ν₂ ≪ ρ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hρ : ∀ᵐ y ∂ρ, y ∈ V := ae_add_measure_iff.mpr ⟨hν₁, hν₂⟩
  have hm₁ : Measurable f₁ := (Measure.measurable_rnDeriv ν₁ ρ).ennreal_toReal
  have hm₂ : Measurable f₂ := (Measure.measurable_rnDeriv ν₂ ρ).ennreal_toReal
  have hi₁ : Integrable f₁ ρ := by
    simpa only [f₁, integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := ν₁) (ν := ρ) (s := univ) (measure_ne_top ν₁ univ))
  have hi₂ : Integrable f₂ ρ := by
    simpa only [f₂, integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := ν₂) (ν := ρ) (s := univ) (measure_ne_top ν₂ univ))
  have h₁ := hb hV hsub hρ hm₁ hi₁
  have h₂ := hb hV hsub hρ hm₂ hi₂
  have hd := hb hV hsub hρ (hm₁.sub hm₂) (hi₁.sub hi₂)
  have heq : ∀ᵐ x ∂μ.restrict V,
      (∫ y, greenFunction V y x ∂ν₁) - (∫ y, greenFunction V y x ∂ν₂) =
        ∫ y, (f₁ y - f₂ y) * greenFunction V y x ∂ρ := by
    filter_upwards [h₁.2.1, h₂.2.1] with x hx₁ hx₂
    have hsource₁ : Integrable (fun y => greenFunction V y x) ν₁ :=
      (integrable_toReal_rnDeriv_mul_iff ha₁).mp hx₁
    have hsource₂ : Integrable (fun y => greenFunction V y x) ν₂ :=
      (integrable_toReal_rnDeriv_mul_iff ha₂).mp hx₂
    rw [← integral_toReal_rnDeriv_mul ha₁, ← integral_toReal_rnDeriv_mul ha₂,
      ← integral_sub hx₁ hx₂]
    apply integral_congr_ae
    filter_upwards with y
    exact (sub_mul _ _ _).symm
  calc
    _ = ∫ x in V, ‖∫ y, (f₁ y - f₂ y) * greenFunction V y x ∂ρ‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ ≤ C * ∫ y, ‖f₁ y - f₂ y‖ ∂ρ := hd.2.2.2
    _ = _ := by rw [(finite_measure_difference_density ν₁ ν₂).2.2.2]

/-- Total variation convergence of finite sources implies L¹ convergence of
 their observed Green potentials. -/
theorem tendsto_observer_green_of_totalVariation
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) {V : Set ℂ} (hV : IsOpen V)
    (hsub : V ⊆ ball (0 : ℂ) R)
    (ν : ℕ → Measure ℂ) [∀ n, IsFiniteMeasure (ν n)]
    (η : Measure ℂ) [IsFiniteMeasure η]
    (hν : ∀ n, ∀ᵐ y ∂ν n, y ∈ V) (hη : ∀ᵐ y ∂η, y ∈ V)
    (hconv : Tendsto (fun n => ((ν n).toSignedMeasure - η.toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, ‖(∫ y, greenFunction V y x ∂ν n) -
      (∫ y, greenFunction V y x ∂η)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := observer_green_totalVariation_bound hup hR
  have hl : Tendsto (fun n => C * ((ν n).toSignedMeasure - η.toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hconv
  exact squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => hb hV hsub (ν n) η (hν n) hη) hl

end HarmonicBalls
