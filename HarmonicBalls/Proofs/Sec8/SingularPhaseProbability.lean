import HarmonicBalls.Proofs.Sec8.SingularPhaseCriterionComparison
import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodProbability
import HarmonicBalls.Proofs.Sec8.JointGoodScaleProbability
import HarmonicBalls.Proofs.Sec6.SingularSizeWindowProbability

/-! # Uniform phase bounds for a logarithmically singular field -/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Singular Weyl weighting transports the regular-field phase-uniform
criterion and size estimates to a singular reference field. -/
theorem exists_singular_phaseVeryGoodComparable_probability_of_weight
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    {a b c : ℝ} (hc : 0 < c)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCα : LQGMeasureCoordChange P γ α hC hcirc)
    (hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ)
    (hprev : PolyHighProb P fun ε => {ω | ∀ z ∈ Section6.prevalenceGrid ε,
      c * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (ν ω) r z a b}.ncard : ℝ)})
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
      ∀ N : ℕ, N₀ ≤ N → ∀ phase : ℂ,
      P {ω | ¬ (PhaseVeryGoodAnnulus (μ ω) β 1 0 N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c phase ∧
        AnnulusBallComparison (μ ω) 0 0 m)} ≤ δ + δ + δ + δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, hw⟩ :=
    Section6.exists_singular_veryGood_size_windows_uniform hgrowth P hγ hγ2 hβ
      hgff hν hAff hCC₀ hweight hδ
  obtain ⟨N₀, hN₀, hthree⟩ := exists_phaseVeryGoodCriterionThree_probability
    P hγ hγ2 hc hgff hν hAff hCC₀ hprev hunit hδ
  obtain ⟨m, hm, hcomp⟩ := exists_lqg_annulusBallComparison_uniform_threshold
    hfull γ α hγ hγ2 hα hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, N₀, hN₀, m, hm, ?_⟩
  intro N hN phase
  have hd := origin_separated_from_scaled_annulus (ρ := 1) (by norm_num)
  have hcriterion := (measure_not_phaseVeryGoodCriterionThree_le_of_singular_weight P
    (x₀ := 0) (N₀ := N) (phase := fun _ => phase) (by norm_num) hd
    (hN₀.trans hN) hweight).trans (hthree N hN 0 (fun _ => phase))
  have hgood : P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 0 N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c phase} ≤ δ + δ + δ := by
    calc
      _ ≤ _ := measure_not_phaseVeryGoodAnnulus_le P μ β 1 0 N _ b C₁m C₁p C₂m C₂p c phase
      _ ≤ δ + δ + δ := add_le_add (add_le_add (hw 1 (by norm_num) 0 hd).1
        (hw 1 (by norm_num) 0 hd).2) hcriterion
  calc
    _ ≤ P {ω | ¬ PhaseVeryGoodAnnulus (μ ω) β 1 0 N
          (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b C₁m C₁p C₂m C₂p c phase} +
        P {ω | ¬ AnnulusBallComparison (μ ω) 0 0 m} := by
      convert measure_union_le (μ := P) _ _ using 1
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_union, not_and_or]
    _ ≤ δ + δ + δ + δ := add_le_add hgood
      (hcomp Ω P hC hcirc μ hgff hμ hAff hCCα 0)

end HarmonicBalls
