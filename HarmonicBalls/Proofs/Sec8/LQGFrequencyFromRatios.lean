import HarmonicBalls.Proofs.Sec8.AEStationaryFrequency
import HarmonicBalls.Proofs.Sec8.LocalMeasureExtension
import HarmonicBalls.Proofs.Sec8.JointGoodScaleProbability

/-! # Good-scale frequencies from normalized local masses

The pointwise ergodic theorem used through `AEStationaryFrequency` is from
Leonardo Bonanno's LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- A null-measurable event has probability greater than `1 - ζ` if its
failure probability is bounded by a smaller nonnegative number. -/
theorem probability_gt_of_small_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : NullMeasurableSet A P) {ε ζ : ℝ}
    (hε : 0 ≤ ε) (hεζ : ε < ζ) (hfail : P Aᶜ ≤ ENNReal.ofReal ε) :
    1 - ζ < (P A).toReal := by
  have hsum : P.real A + P.real Aᶜ = 1 := by
    rw [measureReal_add_measureReal_compl₀ hA, probReal_univ]
  have hbound : P.real Aᶜ ≤ ε := by
    change (P Aᶜ).toReal ≤ ε
    have ht := (ENNReal.toReal_le_toReal (measure_ne_top P Aᶜ) ENNReal.ofReal_ne_top).2 hfail
    simpa [ENNReal.toReal_ofReal hε] using ht
  change 1 - ζ < P.real A
  linarith

universe u

open Classical MarkovProcess in
/-- The LQG good-scale bound follows from the one-scale failure estimate,
normalized local mass measurability and germ triviality. -/
theorem ae_eventually_lqg_goodScaleCount_of_mass_ratios
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ ε₀ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (germ : ℝ → MeasurableSpace Ω) (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hcofinal : ∀ ε, 0 < ε → ∃ n, r n ≤ ε)
    (hrmono : Antitone r) (hgmono : Monotone germ)
    (hratio : ∀ ε, 0 < ε → ∀ V : Set ℂ, IsOpen V →
      @Measurable Ω ℝ≥0∞ (germ ε) _
        (fun ω => μ ω (V ∩ ball 0 ε) / μ ω (ball 0 ε)))
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
  have hd := identDistrib_lqg_veryGoodComparable_of_ae_point_avoidance hfull hγ hγ2 hα
    hGFF hμ hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha hpolar
  have hF := (measurable_pi_apply (0 : ℕ)).comp_aemeasurable hd.aemeasurable_fst
  have hAn : NullMeasurableSet A P := by
    convert hF.nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ)) using 1
    ext ω
    simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    split_ifs <;> simp_all
  have hq : 1 - ζ < (P A).toReal := probability_gt_of_small_failure P A hAn hε hεζ hfail
  have hfullae := hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hatomae := hatom hGFF hγ hγ2 hα μ hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hlocal := ae_local_veryGoodComparable_indicators_of_mass_ratios P germ μ β N₀
    a b C₁m C₁p C₂m C₂p C₃ m ha hpolar hfullae hatomae hloc hratio
  exact ae_eventually_lqg_veryGoodComparableScaleCount_of_local_versions hfull hγ hγ2 hα
    hGFF hμ hatom hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha hpolar
    germ r hr hcofinal hrmono hgmono hlocal htrivial hq

end HarmonicBalls
