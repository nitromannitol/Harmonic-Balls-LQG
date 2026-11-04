import HarmonicBalls.Defs.Annuli
import HarmonicBalls.Proofs.Sec8.AnnulusComparisonStationarity

/-! # Invariance of good annuli under a change of mass normalization

The good and very-good conditions depend on the LQG measure only through
ratios. These deterministic identities isolate the multiplicative part of the
normalized-pullback transport used in Lemma 8.3.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- Multiplying a measure by a nonzero finite constant preserves the good
annulus event. -/
theorem isGoodAnnulus_smul (μ : Measure ℂ) (r : ℝ) (z : ℂ) (a b : ℝ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    IsGoodAnnulus (c • μ) r z a b ↔ IsGoodAnnulus μ r z a b := by
  unfold IsGoodAnnulus
  simp only [Measure.smul_apply, smul_eq_mul,
    mul_left_comm (ENNReal.ofReal a) c, ENNReal.mul_le_mul_iff_right hc hct]

/-- The ball-mass size scales linearly with the measure. -/
theorem annulusBallMassSize_smul (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    annulusBallMassSize (c • μ) βminus ρ x₀ = c * annulusBallMassSize μ βminus ρ x₀ := by
  simp only [annulusBallMassSize, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_iInf_of_ne hc hct, mul_div_assoc]

/-- The Green-potential supremum scales linearly with the measure. -/
theorem annulusGreenPotentialSup_smul (μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ)
    (c : ℝ≥0∞) :
    annulusGreenPotentialSup (c • μ) x₀ a b = c * annulusGreenPotentialSup μ x₀ a b := by
  simp only [annulusGreenPotentialSup, setLIntegral_smul_measure, smul_eq_mul, ENNReal.mul_iSup]

/-- Very-good annuli are invariant under a nonzero finite change of mass
normalization. -/
theorem isVeryGoodAnnulus_smul (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞) :
    IsVeryGoodAnnulus (c • μ) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  simp only [IsVeryGoodAnnulus, annulusBallMassSize_smul μ βminus ρ x₀ hc hct,
    annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_div_mul_left _ _ hc hct, isGoodAnnulus_smul μ _ _ _ _ hc hct]

/-- The random normalizing factor in the pullback does not affect the
very-good event; only geometric dilation remains. -/
theorem isVeryGoodAnnulus_normalizedPullback (μ : Measure ℂ) (hcirc : ℝ → ℂ → ℝ)
    (γ α₀ k βminus ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus (normalizedPullbackMeasure γ α₀ k hcirc μ)
        βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x))
        βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  unfold normalizedPullbackMeasure
  apply isVeryGoodAnnulus_smul
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  · exact ENNReal.ofReal_ne_top

universe u

open Classical in
/-- Stationarity of the joint indicators follows from geometric dyadic
transport of the very-good event. The random mass normalization is handled
by `isVeryGoodAnnulus_normalizedPullback`. -/
theorem identDistrib_lqg_veryGoodComparable_sequence_of_dyadic_transport
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (βminus : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hmeas : ∀ n, MeasurableSet {ν : Measure ℂ |
      IsVeryGoodAnnulus ν βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃})
    (htransport : ∀ᵐ ω ∂P, ∀ n,
      IsVeryGoodAnnulus ((μ ω).map (fun x : ℂ => (dyadicScale 1)⁻¹ • x))
        βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus (μ ω) βminus (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  apply identDistrib_lqg_veryGoodComparable_sequence_of_transport hγ hγ2 hα hGFF hμ hAff hCC
    βminus N₀ a b C₁m C₁p C₂m C₂p C₃ m hmeas
  filter_upwards [htransport] with ω hω n
  exact (isVeryGoodAnnulus_normalizedPullback (μ ω) (hcirc ω) γ α₀ (dyadicScale 1)
    βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃).trans (hω n)

end HarmonicBalls
