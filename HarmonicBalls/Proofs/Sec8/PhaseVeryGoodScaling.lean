import HarmonicBalls.Proofs.Sec8.PhaseJointMeasurable
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling

/-! # Scaling the phase-shifted very-good event

These identities retain the lattice phase when a very-good annulus is
recentered and normalized to unit radius. -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- The three very-good criteria, with a common spatial lattice phase. -/
def PhaseVeryGoodAnnulus (μ : Measure ℂ) (β ρ : ℝ) (x : ℂ) (N : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) : Prop :=
  annulusBallMassSize μ β ρ x / μ (annulus x (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) ∧
  annulusGreenPotentialSup μ x (ρ / 4) (2 * ρ) / μ (annulus x (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) ∧
  PhaseVeryGoodCriterionThree μ ρ x N a b C₃ (fun _ => phase)

/-- The shifted event is jointly measurable in measure, centre, and phase. -/
theorem measurableSet_phaseVeryGoodAnnulus
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c phase : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (hphase : Measurable phase)
    (β ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {x : A |
      PhaseVeryGoodAnnulus (μ x) β ρ (c x) N a b C₁m C₁p C₂m C₂p C₃ (phase x)} := by
  simpa only [PhaseVeryGoodAnnulus] using
    measurableSet_phaseVeryGoodAnnulus_joint hμ hfinite hc hphase β ρ hρ N
      a b C₁m C₁p C₂m C₂p C₃ hunit

/-- Translating the phase by an outer-scale lattice vector does not change
the shifted event. -/
theorem phaseVeryGoodAnnulus_outer_period (μ : Measure ℂ) (β ρ : ℝ) (x : ℂ)
    (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) {t : ℂ}
    (ht : t ∈ Section6.scaledLattice (ρ / 100)) :
    PhaseVeryGoodAnnulus μ β ρ x N a b C₁m C₁p C₂m C₂p C₃ phase ↔
      PhaseVeryGoodAnnulus μ β ρ x N a b C₁m C₁p C₂m C₂p C₃ (phase + t) := by
  simp only [PhaseVeryGoodAnnulus,
    phaseVeryGoodCriterionThree_outer_period μ ρ x N a b C₃ (fun _ => phase) ht]

/-- Zero phase gives the printed absolute lattice. -/
theorem phaseVeryGoodAnnulus_zero (μ : Measure ℂ) (β ρ : ℝ) (x : ℂ) (N : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    PhaseVeryGoodAnnulus μ β ρ x N a b C₁m C₁p C₂m C₂p C₃ 0 ↔
      IsVeryGoodAnnulus μ β ρ x N a b C₁m C₁p C₂m C₂p C₃ := by
  rw [PhaseVeryGoodAnnulus, phaseVeryGoodCriterionThree_zero, Section6.isVeryGoodAnnulus_iff]

/-- Multiplication of the measure by a positive finite constant does not
change the shifted event. -/
theorem phaseVeryGoodAnnulus_smul (μ : Measure ℂ) (β ρ : ℝ) (x : ℂ) (N : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) {d : ℝ≥0∞}
    (hd : d ≠ 0) (hdt : d ≠ ∞) :
    PhaseVeryGoodAnnulus (d • μ) β ρ x N a b C₁m C₁p C₂m C₂p C₃ phase ↔
      PhaseVeryGoodAnnulus μ β ρ x N a b C₁m C₁p C₂m C₂p C₃ phase := by
  simp only [PhaseVeryGoodAnnulus, PhaseVeryGoodCriterionThree,
    annulusBallMassSize_smul μ β ρ x hd hdt, annulusGreenPotentialSup_smul,
    Measure.smul_apply, smul_eq_mul, ENNReal.mul_div_mul_left _ _ hd hdt,
    isGoodAnnulus_smul μ _ _ _ _ hd hdt]

/-- Spatial dilation transports the common phase along with the scale. -/
theorem phaseVeryGoodAnnulus_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (β ρ : ℝ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) :
    PhaseVeryGoodAnnulus (μ.map (fun z : ℂ => k⁻¹ • z)) β ρ 0 N
        a b C₁m C₁p C₂m C₂p C₃ phase ↔
      PhaseVeryGoodAnnulus μ β (k * ρ) 0 N a b C₁m C₁p C₂m C₂p C₃ (k • phase) := by
  simp only [PhaseVeryGoodAnnulus, annulusBallMassRatioSize_map_inv_smul μ hk,
    annulusGreenPotentialRatio_map_inv_smul μ hk,
    phaseVeryGoodCriterionThree_map_inv_smul μ hk, smul_zero]

/-- The scalar in the normalized pullback does not alter the shifted event. -/
theorem phaseVeryGoodAnnulus_normalizedPullback (μ : Measure ℂ) (hcirc : ℝ → ℂ → ℝ)
    (γ α k β ρ : ℝ) (x : ℂ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (phase : ℂ) :
    PhaseVeryGoodAnnulus (normalizedPullbackMeasure γ α k hcirc μ) β ρ x N
        a b C₁m C₁p C₂m C₂p C₃ phase ↔
      PhaseVeryGoodAnnulus (μ.map (fun z : ℂ => k⁻¹ • z)) β ρ x N
        a b C₁m C₁p C₂m C₂p C₃ phase := by
  unfold normalizedPullbackMeasure
  apply phaseVeryGoodAnnulus_smul
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  · exact ENNReal.ofReal_ne_top

/-- An absolute-lattice event at `z` is exactly the unit-scale event after
recentering and normalization, with phase `-ρ⁻¹ • z`. -/
theorem isVeryGoodAnnulus_iff_normalized_shifted_phase (μ : Measure ℂ)
    (hcirc : ℝ → ℂ → ℝ) (γ α β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ)
    (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus μ β ρ z N a b C₁m C₁p C₂m C₂p C₃ ↔
      PhaseVeryGoodAnnulus
        (normalizedPullbackMeasure γ α ρ hcirc (μ.map (fun w : ℂ => w - z)))
        β 1 0 N a b C₁m C₁p C₂m C₂p C₃ (-(ρ⁻¹ • z)) := by
  rw [phaseVeryGoodAnnulus_normalizedPullback, phaseVeryGoodAnnulus_map_inv_smul _ hρ]
  simp only [mul_one, smul_neg, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
  exact isVeryGoodAnnulus_iff_centered_shifted_phase μ β ρ z N a b C₁m C₁p C₂m C₂p C₃

/-- On successive dyadic scales the normalized phase doubles. -/
theorem normalizedPhase_dyadic_succ (z : ℂ) (n : ℕ) :
    -((dyadicScale (n + 1))⁻¹ • z) = (2 : ℝ) • (-((dyadicScale n)⁻¹ • z)) := by
  simp only [dyadicScale, pow_succ, mul_inv_rev, inv_inv, smul_neg, smul_smul]

end HarmonicBalls
