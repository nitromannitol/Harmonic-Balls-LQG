import HarmonicBalls.Proofs.Sec10.PoleAvoidingDiscPotential
import HarmonicBalls.Proofs.Sec6.AnnulusMassCover

/-! # Annular mass of pole-avoiding component unions

A fixed finite cover reduces the annular mass bound to a single disc-potential
comparison. The local components may avoid the pole even when the annulus
contains it.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6
open scoped ENNReal

/-- Restricting a union of components to a smaller domain gives a union of
components in that domain. -/
theorem inter_union_components_of_subset {U V K D : Set ℂ}
    (hVU : V ⊆ U) (hD : D ⊆ U ∩ K)
    (hcomp : ∀ x ∈ D, connectedComponentIn (U ∩ K) x ⊆ D) :
    V ∩ D ⊆ V ∩ K ∧
      ∀ x ∈ V ∩ D, connectedComponentIn (V ∩ K) x ⊆ V ∩ D := by
  refine ⟨fun x hx => ⟨hx.1, (hD hx.2).2⟩, ?_⟩
  intro x hx y hy
  refine ⟨(connectedComponentIn_subset (V ∩ K) x hy).1, ?_⟩
  exact hcomp x hx.2 (connectedComponentIn_mono x (inter_subset_inter_left K hVU) hy)

/-- A uniformly chosen finite family of discs controls annular mass by a
boundary value of the truncated odometer. Restricted disc-potential
regularity is stated explicitly. -/
theorem exists_annulus_mass_le_truncated_odometer_of_potential_regular
    {s₁ s₂ s₃ s₄ : ℝ} (h12 : s₁ < s₂) (h23 : s₂ < s₃) (h34 : s₃ < s₄)
    (hs₂ : 0 ≤ s₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ T : Finset ℂ, T.Nonempty ∧
      ∀ {μ : Measure ℂ}, IsLocallyFiniteMeasure μ →
      ∀ {R βminus βplus : ℝ}, 0 < R → VolumeGrowth μ R βminus βplus →
      ∀ {z : ℂ}, z ∈ ball (0 : ℂ) R → ∀ {t : ℝ}, 0 < t →
      ∀ {w : ℂ} {r : ℝ}, 0 < r →
      annulus w (s₁ * r) (s₄ * r) ⊆ ball (0 : ℂ) R →
      ∀ {Λ : Set ℂ}, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster μ R z t →
      (∀ x ∈ Λ, connectedComponentIn
        (annulus w (s₁ * r) (s₄ * r) ∩ cluster μ R z t) x ⊆ Λ) →
      z ∉ Λ →
      (∀ c : ℂ, closedBall c (2 * (δ * r)) ⊆ annulus w (s₁ * r) (s₄ * r) →
        ContinuousOn (fun x => ∫ y in ball c (2 * (δ * r)) ∩ Λ,
          greenFunction (ball c (2 * (δ * r))) x y ∂μ) (closedBall c (2 * (δ * r))) ∧
        HasLaplacian (fun x => ∫ y in ball c (2 * (δ * r)) ∩ Λ,
          greenFunction (ball c (2 * (δ * r))) x y ∂μ) 0
          (μ.restrict (ball c (2 * (δ * r)) ∩ Λ)) (ball c (2 * (δ * r)))) →
      ∃ y ∈ annulus w (s₁ * r) (s₄ * r),
        ((2 * Real.pi)⁻¹ * Real.log (3 / 2)) *
          (μ (annulus w (s₂ * r) (s₃ * r) ∩ Λ)).toReal ≤
            (T.card : ℝ) * Λ.indicator (odometer μ R z t) y := by
  obtain ⟨δ, hδ, T, hT, hcover⟩ := exists_uniform_annulus_mass_disc h12 h23 h34 hs₂
  refine ⟨δ, hδ, T, hT, ?_⟩
  intro μ hμ R βminus βplus hR hV z hz t ht w r hr hUsub Λ hΛsub hcomp hzΛ hregular
  obtain ⟨x, hxT, hx, hdisc, hmass⟩ := hcover w r hr μ Λ
  have hdisc' : closedBall (r • x + w) (2 * (δ * r)) ⊆
      annulus w (s₁ * r) (s₄ * r) := by
    simpa only [mul_assoc] using hdisc
  obtain ⟨hqc, hqΔ⟩ := hregular (r • x + w) hdisc'
  obtain ⟨y, hy, hbound⟩ := mass_le_truncated_odometer_of_potential_regular_of_pole_not_mem
    hμ hR hV hz ht (isOpen_ball.sdiff isClosed_closedBall) hUsub hΛsub hcomp hzΛ (mul_pos hδ hr)
    hdisc' hmass hqc hqΔ
  exact ⟨y, hdisc' (sphere_subset_closedBall hy), hbound⟩

end HarmonicBalls
