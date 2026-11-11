import HarmonicBalls.Proofs.Sec8.UnitBallRootedFrequency
import HarmonicBalls.Proofs.Sec8.RootedObservedFrequency

/-! # Unit-ball observed frequency certificates

Convergence of local mass approximations under the normalized rooted law
produces a frequency certificate on regular-measure typical points in the
unit ball. The imported Section 8 development uses Leonardo Bonanno's
whole-plane GFF formalization and ergodic theorem.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- Convergent observed normalized-mass approximations give a measurable
unit-ball frequency certificate. The convergence premise remains explicit. -/
theorem IsWholePlaneGFF.exists_unitBall_observed_frequency_certificate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0)
    (ε : ℝ) (hε : 0 < ε)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (f : S → ℕ → (RawMeanZeroTest → ℝ) × ℂ → ℝ) (hf : ∀ V n, Measurable (f V n))
    (hlim : ∀ V, TendstoInMeasure
      (P ⊗ₘ weightedRestrictionKernel P ν (hh.aemeasurable_lqgMeasure hν)
        (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
      (fun n x => f V n ((fun φ : RawMeanZeroTest => hC x.1 φ.1), x.2)) atTop
      (fun x => (normalizedRestriction
        ((ν x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) V.val).toReal))
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a) :
    ∃ E : Set ((RawMeanZeroTest → ℝ) × ℂ), MeasurableSet E ∧
      ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 1 →
        (((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E ↔
          ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
            (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X : Ω → RawMeanZeroTest → ℝ := fun ω φ => hC ω φ.1
  have hX : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hh.measurable_pairing φ.1 φ.2.1
  have hνmeas := hh.aemeasurable_lqgMeasure hν
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  have hfin : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (ν ω) := hω
    simpa only [withDensity_const, one_smul] using
      (measure_ball_ne_top : ν ω (ball (0 : ℂ) 1) ≠ ∞)
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hmass, hfin] with ω hω hfω
    exact ⟨by simpa only [withDensity_const, one_smul] using hω, hfω⟩
  obtain ⟨E, hE, hEae⟩ := exists_observed_frequency_event_weightedRestriction_compProd
    P ν hνmeas hloc (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const hmass'
    X hX ε hε S hcount hgen hpi hsets f hf hlim β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    (measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0 a b ha)
  refine ⟨E, hE, ?_⟩
  apply ae_ae_of_rooted_weighted_restriction P ν
    (weightedRestrictionKernel P ν hνmeas (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const) (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const ?_ hfin
    (ae_weightedRestrictionKernel_eq P ν hνmeas (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const) _ Measure.AbsolutelyContinuous.rfl hEae
  filter_upwards with ω
  filter_upwards with z
  exact one_ne_zero

end HarmonicBalls
