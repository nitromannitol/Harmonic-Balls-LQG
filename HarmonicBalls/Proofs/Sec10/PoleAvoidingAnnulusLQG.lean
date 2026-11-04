import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusAssembly
import HarmonicBalls.Proofs.Sec10.PoleAvoidingRiesz

/-! # LQG annular mass bounds for pole-avoiding components -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

universe u

/-- The volume-growth event gives the annular mass bound simultaneously for
all poles, times, annuli and component unions that avoid their pole. -/
theorem ae_annulus_mass_le_odometer_of_pole_not_mem
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ α₀ : ℝ}, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ},
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        ∀ r : ℝ, 0 < r → ∀ w : ℂ, annulus w (s₁ * r) (s₄ * r) ⊆ ball 0 1 →
        ∀ Λ : Set ℂ, Λ ⊆ annulus w (s₁ * r) (s₄ * r) ∩ cluster (μ ω) 1 z t →
        (∀ x ∈ Λ, connectedComponentIn
          (annulus w (s₁ * r) (s₄ * r) ∩ cluster (μ ω) 1 z t) x ⊆ Λ) →
        z ∉ Λ → (μ ω) (annulus w (s₂ * r) (s₃ * r) ∩ Λ) ≤
          ENNReal.ofReal C * ⨆ x ∈ Λ, odometerExt (μ ω) z t x := by
  obtain ⟨C, hC, hmass⟩ := annulus_mass_le_odometer_of_pole_not_mem hs₁ h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [hV] with ω hω
  intro z hz t ht r hr w hUsub Λ hΛsub hcomp hzΛ
  exact hmass hω.1 (hω.2 1 zero_lt_one) hz ht hr hUsub Λ hΛsub hcomp hzΛ

/-- On the same volume-growth event, annular mass is controlled for every
pole-avoiding local cluster component and every annulus inside its domain. -/
theorem ae_component_annulus_mass_le_odometer_of_pole_not_mem
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {s₁ s₂ s₃ s₄ : ℝ} (hs₁ : 0 < s₁) (h12 : s₁ < s₂)
    (h23 : s₂ < s₃) (h34 : s₃ < s₄) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ α₀ : ℝ}, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ},
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        ∀ U D : Set ℂ, U ⊆ ball 0 1 →
        D ∈ connectedComponentsIn (U ∩ cluster (μ ω) 1 z t) → z ∉ D →
        ∀ r : ℝ, 0 < r → ∀ w : ℂ, annulus w (s₁ * r) (s₄ * r) ⊆ U →
        (μ ω) (D ∩ annulus w (s₂ * r) (s₃ * r)) ≤
          ENNReal.ofReal C * ⨆ x ∈ annulus w (s₁ * r) (s₄ * r) ∩ D,
            odometerExt (μ ω) z t x := by
  obtain ⟨C, hC, hmass⟩ := component_annulus_mass_le_odometer_of_pole_not_mem hs₁ h12 h23 h34
  refine ⟨C, hC, ?_⟩
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  filter_upwards [hV] with ω hω
  intro z hz t ht U D hUsub hD hzD r hr w hAsub
  exact hmass hω.1 (hω.2 1 zero_lt_one) hz ht hUsub hD hzD hr hAsub

end HarmonicBalls
