import HarmonicBalls.Proofs.Potential.UnboundedGreenMinorantFamily
import HarmonicBalls.Proofs.Sec5.FamilyUniqueness
import HarmonicBalls.Proofs.Sec5.RegularizedFamilyHarmonicBridge

/-! # Full subharmonic tests for the LQG measure

On a common field event, bounded-domain witnesses suffice for the frozen
subharmonic-ball condition and for regularized cluster families.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- On one field event the full and bounded-domain test conditions agree for
all bounded open sets and their centres. -/
theorem IsWholePlaneGFF.ae_subMeanValue_all_iff_bounded
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ : Set ℂ) (z : ℂ),
      IsOpen Λ → Bornology.IsBounded Λ → z ∈ Λ →
      ((∀ f ∈ subharmonicBallTestClass Λ z, HasSubMeanValueProperty (μ ω) Λ z f) ↔
        (∀ f ∈ boundedSubharmonicBallTestClass Λ z, HasSubMeanValueProperty (μ ω) Λ z f)) := by
  filter_upwards [hh.ae_bounded_subharmonic_representatives hγ hγ2 hαQ hμ] with ω hrep
  intro Λ z hΛ hΛb hz
  exact subMeanValue_all_iff_bounded_of_representatives (hrep Λ z hΛ hΛb hz)

/-- The full subharmonic-ball predicate retains its open, centre, and mass
conditions when its tests are restricted to bounded-domain witnesses. -/
theorem IsWholePlaneGFF.ae_isSubharmonicBall_iff_bounded_tests
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ : Set ℂ) (z : ℂ), Bornology.IsBounded Λ →
      (IsSubharmonicBall (μ ω) Λ z ↔
        IsOpen Λ ∧ z ∈ Λ ∧ 0 < μ ω Λ ∧ μ ω Λ < ⊤ ∧
          ∀ f ∈ boundedSubharmonicBallTestClass Λ z, HasSubMeanValueProperty (μ ω) Λ z f) := by
  filter_upwards [hh.ae_subMeanValue_all_iff_bounded hγ hγ2 hαQ hμ] with ω htest
  intro Λ z hΛb
  constructor
  · rintro ⟨hΛ, hz, hp, hf, hall⟩
    exact ⟨hΛ, hz, hp, hf, (htest Λ z hΛ hΛb hz).1 hall⟩
  · rintro ⟨hΛ, hz, hp, hf, hall⟩
    exact ⟨hΛ, hz, hp, hf, (htest Λ z hΛ hΛb hz).2 hall⟩

/-- Bounded tests at every positive time give the full subharmonic-ball
clause of a regularized cluster family on one field event. -/
theorem IsWholePlaneGFF.ae_regularizedClusterFamily_of_bounded_tests
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ : ℝ → Set ℂ) (z : ℂ),
      SatisfiesHarmonicBallConditions (μ ω) Λ z →
      (∀ t : ℝ, 0 < t → ∀ f ∈ boundedSubharmonicBallTestClass (Λ t) z,
          HasSubMeanValueProperty (μ ω) (Λ t) z f) →
      (∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r →
        Λ t = regularizedCluster (μ ω) r z t) →
      IsRegularizedClusterFamily (μ ω) Λ z := by
  filter_upwards [hh.ae_isSubharmonicBall_iff_bounded_tests hγ hγ2 hαQ hμ] with ω hball
  intro Λ z hconditions htest hcompat
  refine ⟨hconditions, ?_, hcompat⟩
  intro t ht
  apply (hball (Λ t) z (hconditions.isBounded t ht)).2
  refine ⟨(hconditions.isRegularOpen t ht).isOpen, hconditions.mem t ht, ?_, ?_, htest t ht⟩
  · rw [hconditions.measure_eq t ht]
    exact ENNReal.ofReal_pos.mpr ht
  · rw [hconditions.measure_eq t ht]
    exact ENNReal.ofReal_lt_top

/-- A family with bounded tests agrees at positive times with a regularized
cluster family for the same field. -/
theorem IsWholePlaneGFF.ae_regularizedClusterFamily_eqOn_of_bounded_tests
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ Λ' : ℝ → Set ℂ) (z : ℂ),
      SatisfiesHarmonicBallConditions (μ ω) Λ z →
      (∀ t : ℝ, 0 < t → ∀ f ∈ boundedSubharmonicBallTestClass (Λ t) z,
          HasSubMeanValueProperty (μ ω) (Λ t) z f) →
      (∀ t : ℝ, 0 < t → ∀ s : ℝ, 0 < s → closure (Λ t) ⊆ ball 0 s → ∀ r : ℝ, s ≤ r →
        Λ t = regularizedCluster (μ ω) r z t) →
      IsRegularizedClusterFamily (μ ω) Λ' z → EqOn Λ Λ' (Ioi 0) := by
  filter_upwards [hh.ae_regularizedClusterFamily_of_bounded_tests hγ hγ2 hαQ hμ] with ω hfamily
  intro Λ Λ' z hconditions htest hcompat hother
  exact (hfamily Λ z hconditions htest hcompat).eqOn hother

/-- Bounded tests give the harmonic-ball family condition used in the
existence and uniqueness statement. -/
theorem IsWholePlaneGFF.ae_harmonicBallFamily_of_bounded_tests
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (Λ : ℝ → Set ℂ) (z : ℂ),
      SatisfiesHarmonicBallConditions (μ ω) Λ z →
      (∀ t : ℝ, 0 < t → ∀ f ∈ boundedSubharmonicBallTestClass (Λ t) z,
        HasSubMeanValueProperty (μ ω) (Λ t) z f) →
      IsHarmonicBallFamily (μ ω) Λ z := by
  filter_upwards [hh.ae_isSubharmonicBall_iff_bounded_tests hγ hγ2 hαQ hμ] with ω hball
  intro Λ z hconditions htest
  refine ⟨?_, hconditions⟩
  intro t ht
  have hfull : IsSubharmonicBall (μ ω) (Λ t) z := by
    apply (hball (Λ t) z (hconditions.isBounded t ht)).2
    refine ⟨(hconditions.isRegularOpen t ht).isOpen, hconditions.mem t ht, ?_, ?_, htest t ht⟩
    · rw [hconditions.measure_eq t ht]
      exact ENNReal.ofReal_pos.mpr ht
    · rw [hconditions.measure_eq t ht]
      exact ENNReal.ofReal_lt_top
  exact hfull.isHarmonicBallGen

end HarmonicBalls
