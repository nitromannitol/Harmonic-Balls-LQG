import HarmonicBalls.Draft.Section3

/-!
# Simultaneous compatibility at all radii

The fixed-outer-radius events of Lemma 3.5 combine over a countable cofinal
sequence, so that the comparison applies simultaneously to arbitrary radii.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Simultaneous version of Lemma 3.5 with no fixed upper radius. -/
def ClusterCompatibilityAllRadiiStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, ∀ z ∈ ball (0 : ℂ) s₁,
      ∀ s₂ : ℝ, s₁ ≤ s₂ → closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
      ∀ s : ℝ, s₁ ≤ s → cluster (μ ω) s z t = cluster (μ ω) s₂ z t

/-- A countable cofinal sequence removes the fixed-outer-radius restriction
in Lemma 3.5 without changing the order of the remaining quantifiers. -/
theorem clusterCompatibilityAllRadii_of_steps (h35 : ClusterCompatibilityStmt.{u}) :
    ClusterCompatibilityAllRadiiStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ (n : ℝ) + 1 →
      ∀ z ∈ ball (0 : ℂ) s₁, ∀ s₂ ∈ Icc s₁ ((n : ℝ) + 1),
        closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
        ∀ s ∈ Icc s₁ ((n : ℝ) + 1), cluster (μ ω) s z t = cluster (μ ω) s₂ z t := by
    intro n
    exact h35 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ ((n : ℝ) + 1) (by positivity)
  filter_upwards [ae_all_iff.2 hevent] with ω hω
  intro t ht s₁ z hz s₂ hs₂ hinside s hs
  obtain ⟨n, hn⟩ := exists_nat_gt (max s₂ s)
  have hs₂n : s₂ ≤ (n : ℝ) + 1 := by have := le_max_left s₂ s; linarith
  have hsn : s ≤ (n : ℝ) + 1 := by have := le_max_right s₂ s; linarith
  exact hω n t ht s₁ (hs₂.trans hs₂n) z hz s₂ ⟨hs₂, hs₂n⟩ hinside s ⟨hs, hsn⟩

end HarmonicBalls
