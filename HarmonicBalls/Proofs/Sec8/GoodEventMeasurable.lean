import HarmonicBalls.Proofs.Sec8.BallMassCountable
import HarmonicBalls.Proofs.Sec6.GoodAnnulusSpatialMap

/-! # Reduction of good-annulus event measurability

Translation and dilation reduce the measurability of the good-annulus event
at any positive radius and any center to the unit annulus at the origin.
-/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Pullback to the unit annulus at the origin transports the good event. -/
theorem isGoodAnnulus_unit_normalize (μ : Measure ℂ) {r : ℝ} (hr : 0 < r)
    (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus ((μ.map (fun x : ℂ => x + -z)).map
      (fun x : ℂ => r⁻¹ • x)) 1 0 a b ↔ IsGoodAnnulus μ r z a b := by
  rw [Section6.isGoodAnnulus_map_inv_smul_iff hr]
  simpa using Section6.isGoodAnnulus_map_add_iff (-z) μ r z a b

/-- If the unit good-annulus event is measurable, then so is every
positive-radius good-annulus event. -/
theorem measurableSet_isGoodAnnulus_of_unit (a b : ℝ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b})
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} := by
  let F : Measure ℂ → Measure ℂ := fun μ =>
    (μ.map (fun x : ℂ => x + -z)).map (fun x : ℂ => r⁻¹ • x)
  have hF : Measurable F :=
    (Measure.measurable_map _ (by fun_prop)).comp (Measure.measurable_map _ (by fun_prop))
  have heq : {μ : Measure ℂ | IsGoodAnnulus μ r z a b} =
      F ⁻¹' {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b} := by
    ext μ
    exact (isGoodAnnulus_unit_normalize μ hr z a b).symm
  rw [heq]
  exact hunit.preimage hF

/-- The very-good event at the origin is measurable once the unit
good-annulus event is measurable. -/
theorem measurableSet_isVeryGoodAnnulus_zero_of_unit_good (β ρ : ℝ) (hρ : 0 < ρ)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hunit : MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ 1 0 a b}) :
    MeasurableSet {μ : Measure ℂ |
      IsVeryGoodAnnulus μ β ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} := by
  apply measurableSet_isVeryGoodAnnulus_zero_of_good_events β ρ hρ N₀
    a b C₁m C₁p C₂m C₂p C₃
  intro n j k l
  apply measurableSet_isGoodAnnulus_of_unit a b hunit
  positivity

open Classical in
/-- Stationarity of the joint indicators requires only measurability of the
unit good event and the staged LQG invariance inputs. -/
theorem identDistrib_lqg_veryGoodComparable_sequence_of_unit_good
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  apply identDistrib_lqg_veryGoodComparable_sequence_of_good_events hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m
  intro s n j k l
  apply measurableSet_isGoodAnnulus_of_unit a b hunit
  exact mul_pos (dyadicScale_pos s) (by positivity)

open Classical in
/-- Local measure representatives up to scale give germ-local versions of
the indicators when the unit good-annulus event is measurable. -/
theorem ae_local_veryGoodComparable_indicators_of_unit_good
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        (μ ω).restrict (ball 0 ε) = c • (ν ω).restrict (ball 0 ε)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  apply ae_local_veryGoodComparable_indicators_of_local_measures P germ μ β 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ m
  · intro n
    exact measurableSet_isVeryGoodAnnulus_zero_of_unit_good β (dyadicScale n)
      (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ hunit
  · exact hrep

end HarmonicBalls
