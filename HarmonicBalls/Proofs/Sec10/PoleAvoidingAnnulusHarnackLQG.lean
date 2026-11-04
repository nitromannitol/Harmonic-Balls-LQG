import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusHarnack
import HarmonicBalls.Proofs.Sec10.PoleAvoidingAnnulusLQG

/-! # LQG component Harnack bounds at all scales -/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6
open scoped ENNReal

universe u

/-- The volume-growth event supplies the scaled component Harnack bound
simultaneously for all admissible poles, times, scales and components. -/
theorem ae_component_middle_annulus_odometer_le_of_outer_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∃ C : ℝ, 0 < C ∧ ∀ {γ α₀ : ℝ}, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ},
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∃ βminus : ℝ, ∀ᵐ ω ∂P,
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ U D : Set ℂ,
        U ⊆ ball (0 : ℂ) 1 →
        D ∈ connectedComponentsIn (U ∩ cluster (μ ω) 1 z t) → z ∉ D →
        ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, annulus x₀ (ρ / 4) ρ ⊆ U →
        ∀ C₁m C₁p α : ℝ, 0 < C₁m → 0 ≤ α →
        annulusBallMassSize (μ ω) βminus ρ x₀ /
            (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∈
          Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
        (μ ω) (D ∩ annulus x₀ (ρ / 2) ρ) ≤
          ENNReal.ofReal α * (μ ω) (annulus x₀ (ρ / 2) ρ) →
        α < C₁m * (8 : ℝ) ^ (-βminus) →
        ⨆ x ∈ annulus x₀ (ρ / 2) (7 / 8 * ρ) ∩ D, odometerExt (μ ω) z t x ≤
          ENNReal.ofReal C * annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) ρ := by
  obtain ⟨C, hC, hbound⟩ := exists_component_middle_annulus_odometer_bound_of_outer_mass
  refine ⟨C, hC, ?_⟩
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα₀ hGFF hμ
  refine ⟨βm, ?_⟩
  filter_upwards [hV] with ω hω
  intro z hz t ht U D hUsub hD hzD ρ hρ x₀ hA C₁m C₁p α h1m hα0 hv1 hmass hα
  exact hbound hω.1 (hω.2 1 zero_lt_one) hz ht hUsub hD hzD hρ hA h1m hα0 hv1 hmass hα

end HarmonicBalls
