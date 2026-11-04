import HarmonicBalls.Proofs.Sec10.PoleAvoidingComponentAnnulus
import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation

/-! # Annular mass estimates across the pole

Volume growth supplies regularity of the restricted disc Green potentials.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6
open scoped ENNReal

/-- Lemma 6.8's mass bound holds for any union of annular cluster components
avoiding the pole, whether or not the annulus contains the pole. -/
theorem annulus_mass_le_odometer_of_pole_not_mem
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {w : ℂ} {r : ℝ}, 0 < r →
      annulus w (s₁ * r) (s₄ * r) ⊆ ball (0 : ℂ) 1 →
      ∀ Λ : Set ℂ, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster μ 1 z t →
      (∀ x ∈ Λ, connectedComponentIn
        (annulus w (s₁ * r) (s₄ * r) ∩ cluster μ 1 z t) x ⊆ Λ) →
      z ∉ Λ → μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≤
        ENNReal.ofReal C * ⨆ x ∈ Λ, odometerExt μ z t x := by
  obtain ⟨C, δ, hC, hδ, hmass⟩ :=
    annulus_mass_le_odometer_of_pole_not_mem_of_potential_regular hs₁ h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht w r hr hUsub Λ hΛsub hcomp hzΛ
  apply hmass hμ hV hz ht hr hUsub Λ hΛsub hcomp hzΛ
  intro c hdisc
  have hsub : ball c (2 * (δ * r)) ⊆ ball (0 : ℂ) 1 :=
    ball_subset_closedBall.trans (hdisc.trans hUsub)
  exact restricted_greenPotential_center_regular hμ (by positivity) hV hsub inter_subset_left

/-- The annular mass bound applies to a pole-avoiding component of a larger
local cluster, restricted to any annulus inside that local domain. -/
theorem component_annulus_mass_le_odometer_of_pole_not_mem
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {U D : Set ℂ}, U ⊆ ball (0 : ℂ) 1 →
      D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t) → z ∉ D →
      ∀ {w : ℂ} {r : ℝ}, 0 < r → annulus w (s₁ * r) (s₄ * r) ⊆ U →
      μ (D ∩ annulus w (s₂ * r) (s₃ * r)) ≤
        ENNReal.ofReal C * ⨆ x ∈ annulus w (s₁ * r) (s₄ * r) ∩ D, odometerExt μ z t x := by
  obtain ⟨C, δ, hC, hδ, hmass⟩ :=
    component_annulus_mass_le_odometer_of_pole_not_mem_of_potential_regular hs₁ h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht U D hUsub hD hzD w r hr hAsub
  apply hmass hμ hV hz ht hUsub hD hzD hr hAsub
  intro c hdisc
  have hsub : ball c (2 * (δ * r)) ⊆ ball (0 : ℂ) 1 :=
    ball_subset_closedBall.trans (hdisc.trans (hAsub.trans hUsub))
  exact restricted_greenPotential_center_regular hμ (by positivity) hV hsub inter_subset_left

end HarmonicBalls
