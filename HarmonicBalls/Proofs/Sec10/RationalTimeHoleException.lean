import HarmonicBalls.Proofs.Sec10.RationalTimeHoles

/-! # Terminal exception in rational-time hole detection

If compactly contained rational-time clusters have no bounded holes, a hole
at a compactly contained time can occur only at a terminal such time.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Under rational-time hole exclusion, at most one compactly contained
positive time can have a bounded hole for each fixed pole. -/
theorem ae_subsingleton_compact_times_with_holes_of_rational_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ q : ℚ, 0 < (q : ℝ) →
        closure (cluster (μ ω) 1 z (q : ℝ)) ⊆ ball 0 1 →
        ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z (q : ℝ)))ᶜ,
          ¬ Bornology.IsBounded V) →
      {t : ℝ | 0 < t ∧ closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
        ∃ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          Bornology.IsBounded U}.Subsingleton := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_no_cluster_holes_of_rational_times hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hno
  intro z hz hrat t ht s hs
  rcases lt_trichotomy t s with hts | hts | hst
  · obtain ⟨U, hU, hUb⟩ := ht.2.2
    exact (hno z hz hrat t s ht.1 hts ht.2.1 hs.2.1 U hU hUb).elim
  · exact hts
  · obtain ⟨U, hU, hUb⟩ := hs.2.2
    exact (hno z hz hrat s t hs.1 hst hs.2.1 ht.2.1 U hU hUb).elim

/-- A compactly contained cluster with a bounded hole has no later
compactly contained time if all such rational-time clusters have no holes. -/
theorem ae_compact_time_with_hole_is_terminal_of_rational_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ q : ℚ, 0 < (q : ℝ) →
        closure (cluster (μ ω) 1 z (q : ℝ)) ⊆ ball 0 1 →
        ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z (q : ℝ)))ᶜ,
          ¬ Bornology.IsBounded V) →
      ∀ t : ℝ, 0 < t → closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        (∃ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          Bornology.IsBounded U) →
        ∀ T : ℝ, t < T → ¬ closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_no_cluster_holes_of_rational_times hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hno
  intro z hz hrat t ht hcl ⟨U, hU, hUb⟩ T htT hclT
  exact hno z hz hrat t T ht htT hcl hclT U hU hUb

/-- Under rational-time hole exclusion, for each fixed pole there are no
bounded holes at Lebesgue-almost every compactly contained positive time.
The exceptional set may depend on the pole and the field realization. -/
theorem ae_no_cluster_holes_ae_time_of_rational_times
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ q : ℚ, 0 < (q : ℝ) →
        closure (cluster (μ ω) 1 z (q : ℝ)) ⊆ ball 0 1 →
        ∀ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z (q : ℝ)))ᶜ,
          ¬ Bornology.IsBounded V) →
      ∀ᵐ t : ℝ ∂volume, 0 < t → closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
        ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
          ¬ Bornology.IsBounded U := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subsingleton_compact_times_with_holes_of_rational_times hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hsub
  intro z hz hrat
  have hnull := (hsub z hz hrat).countable.measure_zero volume
  have hae : ∀ᵐ t : ℝ ∂volume, t ∉ {t : ℝ | 0 < t ∧
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
      ∃ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
        Bornology.IsBounded U} := by
    simpa only [ae_iff, not_not, ofPred_mem_eq] using hnull
  filter_upwards [hae] with t ht
  intro htpos hcl U hU hUb
  exact ht ⟨htpos, hcl, U, hU, hUb⟩

end HarmonicBalls
