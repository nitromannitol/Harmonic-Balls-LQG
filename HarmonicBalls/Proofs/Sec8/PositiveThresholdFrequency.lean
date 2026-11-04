import HarmonicBalls.Proofs.Sec8.PositiveThresholdLocalVersions
import HarmonicBalls.Proofs.Sec8.PositiveThresholdStationarity
import HarmonicBalls.Proofs.Sec8.LQGFrequencyFromRatios

/-! # Positive-threshold good-scale frequency

The pointwise ergodic theorem used through `LQGFrequencyFromRatios` is from
Leonardo Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

universe u

open Classical MarkovProcess in
/-- The good-scale frequency bound at a positive mass threshold follows from
a one-scale failure estimate, local normalized measure versions, and germ
triviality. Point avoidance is only required on the unit annulus. -/
theorem ae_eventually_lqg_goodScaleCount_of_positive_threshold
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ ε₀ : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 ε))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hε : 0 ≤ ε₀) (hεζ : ε₀ < ζ)
    (hfail : P {ω | ¬ (IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal ε₀) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) β 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let A : Set Ω := {ω | IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m}
  have hd := identDistrib_lqg_veryGoodComparable_of_unit_point_avoidance hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha hpolar
  have hF := (measurable_pi_apply (0 : ℕ)).comp_aemeasurable hd.aemeasurable_fst
  have hAn : NullMeasurableSet A P := by
    convert hF.nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ)) using 1
    ext ω
    simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    split_ifs <;> simp_all
  have hq : 1 - ζ < (P A).toReal := probability_gt_of_small_failure P A hAn hε hεζ hfail
  have hfullae := hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hlocal := ae_local_veryGoodComparable_indicators_of_positive_threshold P germ μ β N₀
    a b C₁m C₁p C₂m C₂p C₃ m ha hpolar hfullae hloc hrep
  apply ae_eventually_veryGoodComparableScaleCount_of_identDistrib P μ β 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ m ζ germ r hr hcofinal hrmono hgmono hlocal htrivial
  · simpa only [Nat.add_comm] using hd
  · exact hq

end HarmonicBalls
