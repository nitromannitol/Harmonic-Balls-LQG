import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section7
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Proposition 5.2: shrinking clusters

Lines 2107–2113 prove the intersection assertion by applying Proposition 7.1
at a sequence of radii tending to zero. This file proves that assertion
independently of the time-continuity assertion, whose printed proof only
covers clusters compactly contained in the unit ball (GRAPH G12).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

universe u

/-- The intersection assertion in Proposition 5.2. -/
def ClusterShrinksToCenterStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2),
      ⋂ t ∈ Ioi (0 : ℝ), closure (cluster (μ ω) 1 z t) = {z}

/-- The shrinking assertion of Proposition 5.2 from Proposition 7.1. -/
theorem clusterShrinksToCenter_of_upperBound (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) :
    ClusterShrinksToCenterStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
        closure (cluster (μ ω) 1 z t) ⊆ ball z (((2 : ℝ)⁻¹ ^ n / 2) / 2) := by
    intro n
    have hr : ((2 : ℝ)⁻¹ ^ n / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    have h := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ _ hr
    filter_upwards [h.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨(2 : ℝ)⁻¹ ^ m, by positivity, hm⟩
  filter_upwards [ae_all_iff.2 hevent] with ω hω
  intro z hz
  apply Subset.antisymm
  · intro x hx
    simp only [mem_iInter, mem_Ioi] at hx
    rw [mem_singleton_iff]
    by_contra hxz
    have hd : 0 < dist x z := dist_pos.mpr hxz
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hd (by norm_num : (2 : ℝ)⁻¹ < 1)
    obtain ⟨T, hT, hTbound⟩ := hω n
    have hxball := hTbound (T / 2) ⟨half_pos hT, (half_lt_self hT).le⟩ z hz (hx (T / 2) (half_pos hT))
    have hsmall : dist x z < ((2 : ℝ)⁻¹ ^ n / 2) / 2 := hxball
    have hp : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
    linarith
  · intro x hx
    rw [mem_singleton_iff] at hx
    subst x
    simp only [mem_iInter, mem_Ioi]
    intro t ht
    apply subset_closure
    apply mem_cluster_iff.mpr
    exact ⟨ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz, Or.inl rfl⟩

/-- The right-continuity assertion of Proposition 5.2, including the times at
which the cluster is not compactly contained in the unit ball (GRAPH G12). -/
def ClusterRightContinuityStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧
        ∀ t' ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z t') ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε

/-- Proposition 5.2 from Proposition 7.1 and the right-continuity assertion.
The latter remains a separate hypothesis because Proposition 7.2 covers only
clusters compactly contained in the unit ball. -/
theorem clusterContinuity_of_steps (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hcont : ClusterRightContinuityStmt.{u}) : ClusterContinuityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterShrinksToCenter_of_upperBound h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hcont γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hshrink hright
  exact fun z hz => ⟨hshrink z hz, hright z hz⟩

end HarmonicBalls
