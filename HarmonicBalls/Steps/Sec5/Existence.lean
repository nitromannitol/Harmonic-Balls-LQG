import HarmonicBalls.Proofs.Sec5.LocalFamilyGluing

/-!
# Theorem 5.5 from compatible local families

The local construction step exposes the missing work in the proof of
Theorem 5.5: obtain compatible local families on intervals covering every
positive time, without assuming that the horizons increase (GRAPH G6), and
establish the full local conditions, including left continuity (GRAPH G7).
The deterministic gluing theorem handles the passage to all positive times.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Local families needed for Theorem 5.5. The horizons need only cover all
positive times and are not assumed to be monotone. The last two clauses
record the subharmonic-ball and ambient-radius compatibility assertions. -/
def LocalRegularizedClusterFamiliesStep : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ (T : ℕ → ℝ) (Λ : ℕ → ℝ → Set ℂ),
      LocalClusterFamiliesAgree T Λ ∧ (∀ t : ℝ, 0 < t → ∃ n, t < T n) ∧
      (∀ n, SatisfiesHarmonicBallConditionsOn (μ ω) (Λ n) z (T n)) ∧
      (∀ n t, t ∈ Ioo 0 (T n) → IsSubharmonicBall (μ ω) (Λ n t) z) ∧
      (∀ n t, t ∈ Ioo 0 (T n) → ∀ s : ℝ, 0 < s → closure (Λ n t) ⊆ ball 0 s →
        ∀ r : ℝ, s ≤ r → Λ n t = regularizedCluster (μ ω) r z t)

/-- Theorem 5.5 from compatible, cofinal local families. -/
theorem existenceHarmonicBalls_of_steps (hlocal : LocalRegularizedClusterFamiliesStep.{u}) :
    ExistenceHarmonicBallsStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hlocal γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro z
  obtain ⟨T, Λ, hag, hcover, hcond, hsub, hcompat⟩ := hω z
  refine ⟨glueLocalClusterFamilies T Λ, ?_, ?_, ?_⟩
  · exact glueLocalClusterFamilies_satisfiesConditions (μ ω) z T Λ hag hcover hcond
  · intro t ht
    obtain ⟨n, hn⟩ := hcover t ht
    rw [glueLocalClusterFamilies_eq T Λ hag n ht hn]
    exact hsub n t ⟨ht, hn⟩
  · intro t ht s hs hcl r hsr
    obtain ⟨n, hn⟩ := hcover t ht
    have heq := glueLocalClusterFamilies_eq T Λ hag n ht hn
    rw [heq] at hcl ⊢
    exact hcompat n t ⟨ht, hn⟩ s hs hcl r hsr

end HarmonicBalls
