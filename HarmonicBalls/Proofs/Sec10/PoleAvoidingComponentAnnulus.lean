import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusSupremum

/-! # Annular mass of a pole-avoiding local cluster component -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6
open scoped ENNReal

/-- A local cluster component that avoids the pole obeys the annular mass
estimate on each smaller annulus. Disc-potential regularity is explicit. -/
theorem component_annulus_mass_le_odometer_of_pole_not_mem_of_potential_regular
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {βminus βplus : ℝ}, VolumeGrowth μ 1 βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) 1 → ∀ {t : ℝ}, 0 < t →
      ∀ {U D : Set ℂ}, U ⊆ ball (0 : ℂ) 1 →
      D ∈ connectedComponentsIn (U ∩ cluster μ 1 z t) → z ∉ D →
      ∀ {w : ℂ} {r : ℝ}, 0 < r → annulus w (s₁ * r) (s₄ * r) ⊆ U →
      (∀ c : ℂ, closedBall c (2 * (δ * r)) ⊆ annulus w (s₁ * r) (s₄ * r) →
        ContinuousOn (fun x => ∫ y in ball c (2 * (δ * r)) ∩ (annulus w (s₁ * r) (s₄ * r) ∩ D),
          greenFunction (ball c (2 * (δ * r))) x y ∂μ) (closedBall c (2 * (δ * r))) ∧
        HasLaplacian (fun x => ∫ y in ball c (2 * (δ * r)) ∩ (annulus w (s₁ * r) (s₄ * r) ∩ D),
          greenFunction (ball c (2 * (δ * r))) x y ∂μ) 0
          (μ.restrict (ball c (2 * (δ * r)) ∩ (annulus w (s₁ * r) (s₄ * r) ∩ D)))
          (ball c (2 * (δ * r)))) →
      μ (D ∩ annulus w (s₂ * r) (s₃ * r)) ≤
        ENNReal.ofReal C * ⨆ x ∈ annulus w (s₁ * r) (s₄ * r) ∩ D, odometerExt μ z t x := by
  obtain ⟨C, δ, hC, hδ, hmass⟩ :=
    annulus_mass_le_odometer_of_pole_not_mem_of_potential_regular hs₁ h12 h23 h34
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro μ hμ βminus βplus hV z hz t ht U D hUsub hD hzD w r hr hAsub hreg
  obtain ⟨a, ha, hDa⟩ := hD
  have hDsub : D ⊆ U ∩ cluster μ 1 z t := by
    rw [← hDa]
    exact connectedComponentIn_subset _ _
  have hcomp : ∀ x ∈ D, connectedComponentIn (U ∩ cluster μ 1 z t) x ⊆ D := by
    intro x hx
    rw [← hDa] at hx ⊢
    exact (connectedComponentIn_eq hx).symm.subset
  obtain ⟨hLsub, hLcomp⟩ := inter_union_components_of_subset hAsub hDsub hcomp
  have hmid : annulus w (s₂ * r) (s₃ * r) ⊆ annulus w (s₁ * r) (s₄ * r) := by
    intro x hx
    exact ⟨ball_subset_ball (by nlinarith) hx.1,
      fun h => hx.2 (closedBall_subset_closedBall (by nlinarith) h)⟩
  have hset : annulus w (s₂ * r) (s₃ * r) ∩ (annulus w (s₁ * r) (s₄ * r) ∩ D) =
      D ∩ annulus w (s₂ * r) (s₃ * r) := by
    ext x
    constructor
    · intro hx; exact ⟨hx.2.2, hx.1⟩
    · intro hx; exact ⟨hx.2, hmid hx.2, hx.1⟩
  have h := hmass hμ hV hz ht hr (hAsub.trans hUsub) _ hLsub hLcomp
    (fun hzL => hzD hzL.2) hreg
  rwa [hset] at h

end HarmonicBalls
