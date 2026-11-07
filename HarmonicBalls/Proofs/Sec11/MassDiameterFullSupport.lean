import HarmonicBalls.Proofs.Sec11.MassDiameterPositiveThreshold
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Full support and positive mass thresholds -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- A positive-probability event contains a positive-probability subevent on
    which a set containing a nonempty open set has a fixed positive mass
    threshold. -/
theorem exists_positive_mass_threshold_of_ae_full_support
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (A : Set Ω) (S U : Set X)
    (hA : 0 < P A) (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set X, IsOpen V → V.Nonempty → 0 < μ ω V) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      0 < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
  have hmass : ∀ᵐ ω ∂P, 0 < μ ω S := by
    filter_upwards [hfull] with ω hω
    exact (hω U hU hUne).trans_le (measure_mono hUS)
  have heq : A =ᵐ[P] {ω | ω ∈ A ∧ 0 < μ ω S} := by
    filter_upwards [hmass] with ω hω
    simp [hω]
  exact exists_positive_mass_threshold P μ A S (by rwa [← measure_congr heq])

/-- LQG volume growth gives a fixed positive mass threshold on any
    positive-probability event for a set containing a nonempty open set. -/
theorem exists_positive_lqg_mass_threshold_of_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set Ω) (S U : Set ℂ) (hA : 0 < P A)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      0 < P {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S} := by
  exact exists_positive_mass_threshold_of_ae_full_support P μ A S U hA hU hUne hUS
    (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ₂ hα
      Ω P hC hcirc μ hgff hμ)

#print axioms exists_positive_mass_threshold_of_ae_full_support
#print axioms exists_positive_lqg_mass_threshold_of_growth
end HarmonicBalls
