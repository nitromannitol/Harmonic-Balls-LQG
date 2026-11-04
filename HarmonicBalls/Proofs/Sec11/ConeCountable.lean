import HarmonicBalls.Proofs.Sec11.ConeAnnulus
import HarmonicBalls.Steps.Sec11.BadScales

/-! # Countably many cone mass events -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Enlarging a cone preserves its mass event. -/
theorem coneMassEvent_mono {μ : Measure ℂ} {Q Q' : Set ℂ} {M r : ℝ} {z : ℂ}
    (hQQ' : Q ⊆ Q') (h : coneMassEvent μ Q M r z) : coneMassEvent μ Q' M r z := by
  exact le_trans h (measure_mono (inter_subset_inter_right _ (Set.image_mono hQQ')))

/-- Lemma 11.7 yields simultaneous cone mass events at arbitrarily small
scales whenever a countable family of cones contains a subcone of every cone. -/
theorem ae_frequently_coneMass_of_countable_subcones
    (hmany : ManyConeBadScalesStmt.{u}) (cones : ℕ → Set ℂ)
    (hcones : ∀ i, IsCone (cones i))
    (hsub : ∀ Q : Set ℂ, IsCone Q → ∃ i, cones i ⊆ Q)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (M : ℝ) (hM : 0 < M)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ Q : Set ℂ, IsCone Q →
      ∃ᶠ n : ℕ in atTop, coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z := by
  classical
  have hone : ∀ i : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω),
      ∃ᶠ n : ℕ in atTop, coneMassEvent (μ ω) (cones i) M ((2 : ℝ)⁻¹ ^ n) z := by
    intro i
    obtain ⟨δ, hδ, h⟩ := hmany γ α₀ hγ hγ₂ hα (cones i) (hcones i) M hM
    filter_upwards [h Ω P hC hcirc μ hgff hμ] with ω hω
    filter_upwards [hω] with z hz
    exact frequently_of_positive_dyadic_block_density _ hδ.1 hz
  filter_upwards [ae_all_iff.mpr hone] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with z hz
  intro Q hQ
  obtain ⟨i, hi⟩ := hsub Q hQ
  exact (hz i).mono (fun _ h => coneMassEvent_mono hi h)

end HarmonicBalls
