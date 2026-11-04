import HarmonicBalls.Proofs.Sec11.ConeCountable
import HarmonicBalls.Steps.Sec11.ConeCofinal

/-! # Simultaneous bad scales for all cones -/

namespace HarmonicBalls

open MeasureTheory Set Filter

universe u

/-- Lemma 11.7 implies simultaneous cone-mass events at arbitrarily small
scales for every cone, using a countable family of actual subcones. -/
theorem ae_frequently_coneMass_all_cones
    (hmany : ManyConeBadScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (M : ℝ) (hM : 0 < M)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ Q : Set ℂ, IsCone Q →
      ∃ᶠ n : ℕ in atTop, coneMassEvent (μ ω) Q M ((2 : ℝ)⁻¹ ^ n) z := by
  obtain ⟨cones, hcones, hsub⟩ := exists_countable_cofinal_open_cones
  exact ae_frequently_coneMass_of_countable_subcones hmany cones (fun i => Or.inl (hcones i))
    hsub γ α₀ hγ hγ₂ hα M hM Ω P hC hcirc μ hgff hμ

end HarmonicBalls
