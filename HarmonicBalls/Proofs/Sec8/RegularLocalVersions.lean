import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureVersion
import HarmonicBalls.Proofs.Sec8.VeryGoodLocality

/-! # Local good-scale versions from regular measure representatives -/

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

open Classical MarkovProcess in
/-- A locally proportional regular measure representative supplies measurable
versions of the joint indicators, using only Borel versions valid on regular
measures. Point avoidance is an explicit hypothesis. -/
theorem ae_local_veryGoodComparable_indicators_of_regular_local_measures
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (βminus : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      (∀ᵐ ω ∂P, (∀ x : ℂ, ν ω {x} = 0) ∧ IsLocallyFiniteMeasure (ν ω) ∧
        ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν ω U) ∧
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        (μ ω).restrict (ball 0 ε) = c • (ν ω).restrict (ball 0 ε)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  have hchoose : ∀ n : ℕ, ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ ν : Measure ℂ,
      (∀ x : ℂ, ν {x} = 0) → IsLocallyFiniteMeasure ν →
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν U) →
      (ν ∈ G ↔ IsVeryGoodAnnulus ν βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃) :=
    fun n => exists_measurable_isVeryGoodAnnulus_on_fullSupport βminus (dyadicScale n)
      (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ ha hpolar
  choose G hG hGrep using hchoose
  intro ε hε
  obtain ⟨ν, hν, hregular, hνrep⟩ := hrep ε hε
  obtain ⟨K, hK⟩ := eventually_ball_six_dyadic_subset (0 : ℂ) hε
  let Y : ℕ → Ω → ℝ := fun n ω =>
    if ν ω ∈ G n ∧ AnnulusBallComparison (ν ω) n 0 m then 1 else 0
  refine ⟨K, Y, ?_, ?_⟩
  · intro n _
    let : MeasurableSpace Ω := germ ε
    have hE : MeasurableSet {ω : Ω | ν ω ∈ G n ∧ AnnulusBallComparison (ν ω) n 0 m} :=
      ((hG n).inter (measurableSet_annulusBallComparison n 0 m)).preimage hν
    exact measurable_const.piecewise hE measurable_const
  · intro n hn
    filter_upwards [hregular, hνrep] with ω hr ⟨c, hc, hct, heq⟩
    have hi := veryGoodComparable_congr_of_restrict_eq_smul_on (μ ω) (ν ω) βminus 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ m n (ball 0 ε) (hK n hn) hc hct heq
    simp only [Y, hGrep n (ν ω) hr.1 hr.2.1 hr.2.2, hi]

end HarmonicBalls
