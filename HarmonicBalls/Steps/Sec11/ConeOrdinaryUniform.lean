import HarmonicBalls.Steps.Sec11.ConeOrdinaryLaw
import HarmonicBalls.Steps.Sec11.ConeUnitPositive
import HarmonicBalls.Proofs.Sec9.AffineInvarianceAssembly

/-! # Uniform probabilities for ordinary whole-plane cone events -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- All ordinary whole-plane realizations, centers and inverse-dyadic radii
have the same cone-event probability as a fixed unit-scale realization. -/
theorem cone_ordinary_event_probability_eq_reference
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} {γ : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hG' : IsWholePlaneGFF P' hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) (M : ℝ) (n : ℕ) (z : ℂ) :
    P {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z} =
      P' {ω | coneMassEvent (μ' ω) Q M 1 0} := by
  rw [cone_event_probability_translate hG hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc) Q hQ M (dyadicScale n) z,
    cone_event_probability_dyadic hγ hG hμ
      (wholePlaneGFFAffineInvariance_proved P hC hcirc) Q hQ M n]
  exact cone_event_probability_eq_across_spaces hG hG' hμ hμ' Q hQ M 1 0


universe u

/-- A positive unit-scale probability gives a uniform positive lower bound
for ordinary cone events across realizations, centers and dyadic radii. -/
theorem cone_ordinary_event_uniform_positive
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG' : IsWholePlaneGFF P' hC' hcirc') (hE' : LQGMeasureExistence P' γ 0 hC' hcirc')
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ (n : ℕ) (z : ℂ), p ≤ P {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z} := by
  refine ⟨P' {ω | coneMassEvent (μ' ω) Q M 1 0}, ?_, ?_⟩
  · exact cone_unit_event_positive hS hgrowth hγ hγ2 (by unfold lqgQ; positivity) hG' hE' hμ' Q hQ hM
  · intro Ω _ P hC hcirc μ hG hμ n z
    exact le_of_eq (cone_ordinary_event_probability_eq_reference hγ hG hG' hμ hμ' Q hQ M n z).symm

end HarmonicBalls
