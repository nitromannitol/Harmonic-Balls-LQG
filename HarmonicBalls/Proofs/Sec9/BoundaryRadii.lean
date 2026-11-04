import HarmonicBalls.Proofs.Sec9.WeakUniqueness
import HarmonicBalls.Proofs.Sec3.ClusterCompatibility

/-!
# Reduction of boundary nullity to integer radii

Cluster compatibility transfers boundary nullity from a larger integer radius to any radius
whose cluster is compactly contained in its disc. Only countably many fixed-radius events are
needed, each still simultaneous in mass and centre.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- Boundary nullity at each positive integer radius, on one event. -/
def ClusterBoundaryNullIntegerRadii : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n → ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) n,
    closure (cluster (μ ω) n z t) ⊆ ball 0 n → μ ω (frontier (cluster (μ ω) n z t)) = 0

/-- Cluster compatibility extends integer-radius boundary nullity to every positive radius. -/
theorem clusterBoundaryNullAllRadii_of_integerRadii
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hint : ClusterBoundaryNullIntegerRadii.{u}) :
    ClusterBoundaryNullAllRadii.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hcompat : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n →
      ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ (n : ℝ) → ∀ z ∈ ball (0 : ℂ) s₁,
        ∀ s₂ ∈ Icc s₁ (n : ℝ), closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
          ∀ s ∈ Icc s₁ (n : ℝ), cluster (μ ω) s z t = cluster (μ ω) s₂ z t := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 0 < n
    · have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      filter_upwards [clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ n hnreal] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [hint γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hcompat] with ω hω hc
  intro R t hR ht z hz hcl
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hn0real : (0 : ℝ) < n := hR.trans hn
  have hn0 : 0 < n := by exact_mod_cast hn0real
  have heq := hc n hn0 t ht R hn.le z hz R ⟨le_rfl, hn.le⟩ hcl n ⟨hn.le, le_rfl⟩
  have hnz : z ∈ ball (0 : ℂ) n := ball_subset_ball hn.le hz
  have hncl : closure (cluster (μ ω) n z t) ⊆ ball 0 n := by
    rw [heq]
    exact hcl.trans (ball_subset_ball hn.le)
  simpa only [heq] using hω n hn0 t ht z hnz hncl

/-- Weak Proposition 9.2 from volume growth and integer-radius boundary nullity. -/
theorem subharmonicBallUniquenessWeak_of_integerRadii
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hint : ClusterBoundaryNullIntegerRadii.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_boundaryNull hI2 (clusterBoundaryNullAllRadii_of_integerRadii hI2 hint)

end HarmonicBalls
