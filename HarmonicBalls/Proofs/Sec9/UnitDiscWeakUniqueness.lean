import HarmonicBalls.Proofs.Sec9.TypicalScaleUniqueness
import HarmonicBalls.Proofs.Sec9.BoundaryRadii

/-!
# Weak uniqueness for balls inside the unit disc

Domain compatibility transfers the unit-disc boundary theorem to any
ambient disc when the comparison ball is compactly contained in both.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- Boundary nullity for clusters compactly contained in both their ambient
disc and the unit disc, simultaneously for all radii and poles. -/
theorem ae_cluster_boundary_null_of_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ z ∈ ball (0 : ℂ) R,
      closure (cluster (μ ω) R z t) ⊆ ball 0 R →
      closure (cluster (μ ω) R z t) ⊆ ball 0 1 →
      μ ω (frontier (cluster (μ ω) R z t)) = 0 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hcompat : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < n →
      ∀ t : ℝ, 0 < t → ∀ s₁ : ℝ, s₁ ≤ (n : ℝ) → ∀ z ∈ ball (0 : ℂ) s₁,
        ∀ s₂ ∈ Icc s₁ (n : ℝ), closure (cluster (μ ω) s₂ z t) ⊆ ball 0 s₁ →
          ∀ s ∈ Icc s₁ (n : ℝ), cluster (μ ω) s z t = cluster (μ ω) s₂ z t := by
    rw [ae_all_iff]
    intro n
    by_cases hn : 0 < n
    · have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      filter_upwards [clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα
        Ω P hC hcirc μ hGFF hμ n hnreal] with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => (hn h).elim
  filter_upwards [hcompat, h8 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hc hb
  intro R t hR ht z hz hclR hcl1
  have hz1 : z ∈ ball (0 : ℂ) 1 := hcl1 (subset_closure (self_mem_cluster hz))
  obtain ⟨n, hn⟩ := exists_nat_gt (max R 1)
  have hRn : R ≤ (n : ℝ) := (le_max_left R 1).trans hn.le
  have h1n : (1 : ℝ) ≤ n := (le_max_right R 1).trans hn.le
  have hnpos : 0 < n := by exact_mod_cast (lt_of_lt_of_le zero_lt_one h1n)
  by_cases hR1 : R ≤ 1
  · have heq := hc n hnpos t ht R hRn z hz R ⟨le_rfl, hRn⟩ hclR 1 ⟨hR1, h1n⟩
    have hunitcl : closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
      rw [heq]
      exact hcl1
    simpa only [heq] using hb t ht z hz1 hunitcl
  · have h1R : (1 : ℝ) ≤ R := le_of_not_ge hR1
    have heq := hc n hnpos t ht 1 h1n z hz1 R ⟨h1R, hRn⟩ hcl1 1 ⟨le_rfl, h1n⟩
    have hunitcl : closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
      rw [heq]
      exact hcl1
    simpa only [heq] using hb t ht z hz1 hunitcl

/-- Weak Proposition 9.2 for subharmonic balls contained in the unit disc,
from I2 and the unit-disc boundary theorem. -/
theorem ae_subharmonicBall_weak_uniqueness_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h8 : BoundaryMeasureZeroOfCompactClusterStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure A ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ μ ω (A \ regularizedCluster (μ ω) R z t) = 0 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_boundary_null_of_unit_disc hI2 h8 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hω hopen hmass hbound
  intro A z t R ht hR hz hclR hcl1 hA hA_mass
  have hsub := hA.cluster_subset_of_volumeGrowth hω.1 hR ht (hω.2 R hR) hclR hA_mass
  have hcompact : closure (cluster (μ ω) R z t) ⊆ ball 0 R := (closure_mono hsub).trans hclR
  have hcompact1 : closure (cluster (μ ω) R z t) ⊆ ball 0 1 := (closure_mono hsub).trans hcl1
  have hzero := hbound R t hR ht z hz hcompact hcompact1
  have hcluster := (hmass R t hR ht z hz).2.2 hcompact hzero
  exact hA.weak_uniqueness_of_volumeGrowth hω.1 hR ht (hω.2 R hR) hclR hA_mass
    (hopen t R ht hR z hz).1 hcluster

/-- The localized weak uniqueness result from I2, Lemma 6.11 and Lemma 8.2. -/
theorem ae_subharmonicBall_weak_uniqueness_inside_unit_disc_of_good_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure A ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ μ ω (A \ regularizedCluster (μ ω) R z t) = 0 :=
  ae_subharmonicBall_weak_uniqueness_inside_unit_disc hI2
    (boundaryMeasureZeroOfCompactClusterStmt_of_steps (clusterOpenLaplacian_proved hI2) h611 h82)

end HarmonicBalls
