import HarmonicBalls.Proofs.Sec10.CountableDeletionCrossingBounds
import HarmonicBalls.Proofs.Sec5.CountableDiscCompatibility
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Cluster closures after countable domain deletion -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Volume growth ensures that deleting a relatively closed countable subset of
 a disc leaves the closure of each cluster unchanged. -/
theorem closure_clusterOn_disc_sdiff_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    closure (clusterOn μ (ball (0 : ℂ) R \ K) z t) = closure (cluster μ R z t) := by
  exact closure_clusterOn_relative_countable_disc_eq hμ hR hV K hD hK hz ht

/-- The punctured cluster acquires precisely the deleted points lying in the
original cluster as additional boundary points. -/
theorem frontier_clusterOn_disc_sdiff_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    frontier (clusterOn μ (ball (0 : ℂ) R \ K) z t) =
      frontier (cluster μ R z t) ∪ (cluster μ R z t ∩ K) := by
  have hc := clusterOn_relative_countable_disc_eq_sdiff hμ hR hV K hD hK hz ht
  have hcl := closure_clusterOn_relative_countable_disc_eq hμ hR hV K hD hK hz ht
  have hopen : IsOpen (cluster μ R z t) := by
    rw [(obstacleCompatibilityShiftStep_holds μ hμ R βm βp hR hV z hz.1 t ht).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hμ hR hV hz.1 ht
  have hopen' : IsOpen (clusterOn μ (ball (0 : ℂ) R \ K) z t) := by
    rw [hc]
    have heq : cluster μ R z t \ K = cluster μ R z t ∩ (ball (0 : ℂ) R \ K) := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, cluster_subset_ball hx.1, hx.2⟩
      · intro hx
        exact ⟨hx.1, hx.2.2⟩
    rw [heq]
    exact hopen.inter hD
  rw [frontier, frontier, hopen'.interior_eq, hopen.interior_eq, hcl, hc]
  ext x
  constructor
  · rintro ⟨hx, hn⟩
    by_cases hs : x ∈ cluster μ R z t
    · have hk : x ∈ K := by
        by_contra hk
        exact hn ⟨hs, hk⟩
      exact Or.inr ⟨hs, hk⟩
    · exact Or.inl ⟨hx, hs⟩
  · rintro (⟨hx, hn⟩ | ⟨hs, hk⟩)
    · exact ⟨hx, fun h => hn h.1⟩
    · exact ⟨subset_closure hs, fun h => h.2 hk⟩

/-- Countable deletion preserves the Hausdorff dimension of the frontier. -/
theorem dimH_frontier_clusterOn_disc_sdiff_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp t : ℝ} {z : ℂ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (K : Set ℂ)
    (hD : IsOpen (ball (0 : ℂ) R \ K)) (hK : (K ∩ ball (0 : ℂ) R).Countable)
    (hz : z ∈ ball (0 : ℂ) R \ K) (ht : 0 < t) :
    dimH (frontier (clusterOn μ (ball (0 : ℂ) R \ K) z t)) =
      dimH (frontier (cluster μ R z t)) := by
  have hcount : (cluster μ R z t ∩ K).Countable := hK.mono (by
    intro x hx
    exact ⟨hx.2, cluster_subset_ball hx.1⟩)
  rw [frontier_clusterOn_disc_sdiff_of_volumeGrowth hμ hR hV K hD hK hz ht,
    dimH_union, hcount.dimH_zero, max_zero]

/-- I2 gives simultaneous closure equality over discs, poles, masses, and
relatively closed countable deletions on a single almost-sure event. -/
theorem ae_closure_clusterOn_disc_sdiff_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ K : Set ℂ,
      IsOpen (ball (0 : ℂ) R \ K) → (K ∩ ball (0 : ℂ) R).Countable →
      ∀ z ∈ ball (0 : ℂ) R \ K,
      closure (clusterOn (μ ω) (ball (0 : ℂ) R \ K) z t) =
        closure (cluster (μ ω) R z t) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  intro R t hR ht K hD hK z hz
  exact closure_clusterOn_disc_sdiff_of_volumeGrowth hV.1 hR (hV.2 R hR)
    K hD hK hz ht

/-- Under I2, the frontier formula and dimension equality hold simultaneously
for all discs, poles, positive masses, and relatively closed countable deletions. -/
theorem ae_frontier_clusterOn_disc_sdiff_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ R t : ℝ, 0 < R → 0 < t → ∀ K : Set ℂ,
      IsOpen (ball (0 : ℂ) R \ K) → (K ∩ ball (0 : ℂ) R).Countable →
      ∀ z ∈ ball (0 : ℂ) R \ K,
      frontier (clusterOn (μ ω) (ball (0 : ℂ) R \ K) z t) =
        frontier (cluster (μ ω) R z t) ∪ (cluster (μ ω) R z t ∩ K) ∧
      dimH (frontier (clusterOn (μ ω) (ball (0 : ℂ) R \ K) z t)) =
        dimH (frontier (cluster (μ ω) R z t)) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  intro R t hR ht K hD hK z hz
  exact ⟨frontier_clusterOn_disc_sdiff_of_volumeGrowth hV.1 hR (hV.2 R hR)
      K hD hK hz ht,
    dimH_frontier_clusterOn_disc_sdiff_of_volumeGrowth hV.1 hR (hV.2 R hR)
      K hD hK hz ht⟩

/-- The selected-radius crossing bound applies when compact containment is
stated directly for the punctured-domain cluster. -/
theorem ae_crossings_after_countable_deletion_of_punctured_compact_containment
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ t : ℝ, 0 < t → ∀ K : Set ℂ,
        IsOpen (ball (0 : ℂ) 1 \ K) → (K ∩ ball (0 : ℂ) 1).Countable →
        ∀ z ∈ ball (0 : ℂ) 1 \ K,
        closure (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t) ⊆ ball 0 1 →
        (crossingComponents (clusterOn (μ ω) (ball (0 : ℂ) 1 \ K) z t ∩
          ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_after_countable_deletion_of_dyadic_scaling hI2 h66 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_closure_clusterOn_disc_sdiff_of_volumeGrowth hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hbound heq
  filter_upwards [hbound] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  refine ⟨ρ, hρ, ?_⟩
  intro t ht K hD hK z hz hcompact
  apply hρbound t ht K hD hK z hz
  rw [← heq 1 t zero_lt_one ht K hD hK z hz]
  exact hcompact

end HarmonicBalls
