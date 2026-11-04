import HarmonicBalls.Proofs.Sec10.CountableEmptyAnnulusCriterion
import HarmonicBalls.Proofs.Sec10.HoleExtinctionEndpoint
import HarmonicBalls.Proofs.Sec6.VolumeGrowthConsequences

/-! # Hole criteria from volume growth and typical scales

The Section 6 derivation of Lemma 6.11 is used to remove it as a separate
hypothesis. That Section 6 chain remains subject to campaign audit.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

universe u

/-- Volume growth and Lemma 8.2 give right persistence of bounded holes,
including when the closed cluster meets the boundary of the unit disk. -/
theorem ae_cluster_hole_persists_of_volumeGrowth_typicalScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ,
        Bornology.IsBounded V ∧ V ⊆ U :=
  ae_cluster_hole_persists_at_boundary_contact hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82

/-- For each pole, the absence of holes at every positive time is equivalent
to their absence at every positive rational time. -/
theorem ae_cluster_no_holes_iff_no_rational_holes_of_volumeGrowth_typicalScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, ¬ Bornology.IsBounded U) ↔
      (∀ q : ℚ, 0 < (q : ℝ) → ∀ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z q))ᶜ, ¬ Bornology.IsBounded U) :=
  ae_cluster_no_holes_iff_no_rational_holes hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82

/-- A bounded hole of a compactly contained cluster has a finite lifetime,
with almost-everywhere coverage before its extinction, under volume growth
and Lemma 8.2. -/
theorem ae_cluster_hole_extinction_of_volumeGrowth_typicalScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, L ≤ s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        U ⊆ closure (cluster (μ ω) 1 z L) ∧
        μ ω (U \ ⋃ s ∈ Ico t L, cluster (μ ω) 1 z s) = 0 :=
  ae_cluster_hole_extinction_at_lifetime_endpoint hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82

/-- For each pole, the rational-time empty-annulus criterion requires only
volume growth and Lemma 8.2 in addition to the defining field assumptions. -/
theorem ae_cluster_compl_connected_iff_rational_emptyAnnulus_tests_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (D : Set ℂ) (hDdense : Dense D) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      (∀ t : ℝ, 0 < t → IsConnected (closure (cluster (μ ω) 1 z t))ᶜ) ↔
      (∀ q : ℚ, 0 < (q : ℝ) → EmptyAnnulusCrossingTest (cluster (μ ω) 1 z q) D) :=
  ae_cluster_compl_connected_iff_rational_emptyAnnulus_tests hI2
    (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
    hγ hγ2 hα P hC hcirc μ hGFF hμ D hDdense

end HarmonicBalls
