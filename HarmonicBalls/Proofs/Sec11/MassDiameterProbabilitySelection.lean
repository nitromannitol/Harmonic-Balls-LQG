import HarmonicBalls.Proofs.Sec11.MassDiameterFullSupport

/-! # Selecting a mass-carrying class from convergence in probability -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Full support and convergence of the tile failure probabilities to zero
    give one positive threshold, one deterministic scale, and one member of
    a four-class cover with large mass on a positive-probability event. -/
theorem exists_mass_scale_class_of_full_support_and_failure_tendsto
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω)
    (S U : Set X) (C : ℕ → Fin 4 → Set X) (E : ℕ → Set Ω)
    (hAp : 0 < P A) (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set X, IsOpen V → V.Nonempty → 0 < μ ω V)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hfail : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ n i,
      0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (2 : ℝ≥0∞) * c < μ ω (C n i)} := by
  obtain ⟨c, hc, hp⟩ :=
    exists_positive_mass_threshold_of_ae_full_support P μ A S U hAp hU hUne hUS hfull
  have hsmall : ∃ n, P (E n)ᶜ < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S} :=
    ((tendsto_order.1 hfail).2 _ hp).exists
  obtain ⟨n, i, hi⟩ :=
    exists_positive_measure_scale_and_four_tile_class_of_failure_bound P μ A S C E c hcover hsmall
  exact ⟨c, hc, n, i, hi⟩

/-- The LQG volume-growth estimate supplies full support for the
    mass-carrying class selection. -/
theorem exists_lqg_mass_scale_class_of_growth_and_failure_tendsto
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set Ω) (S U : Set ℂ) (C : ℕ → Fin 4 → Set ℂ) (E : ℕ → Set Ω)
    (hAp : 0 < P A) (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hfail : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ n i,
      0 < P {ω | ω ∈ A ∧ ω ∈ E n ∧ (2 : ℝ≥0∞) * c < μ ω (C n i)} := by
  exact exists_mass_scale_class_of_full_support_and_failure_tendsto P μ A S U C E
    hAp hU hUne hUS (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ₂ hα
      Ω P hC hcirc μ hgff hμ) hcover hfail

end HarmonicBalls
