import HarmonicBalls.Proofs.Sec8.GoodAnnulusLocality
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling
import HarmonicBalls.Proofs.Sec8.AEGermTriviality

/-! # Spatial locality of very-good annuli

The ball-mass size, Green-potential supremum, and good-annulus count only
inspect the measure inside the regions appearing in their definitions.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The ball-mass size is unchanged if all the balls used in its definition
are contained in the restriction set. -/
theorem annulusBallMassSize_restrict (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ)
    (U : Set ℂ) (hball : ∀ z ∈ annulus x₀ (ρ / 2) ρ, ∀ r ∈ Ioo 0 (ρ / 4),
      ball z r ⊆ U) :
    annulusBallMassSize (μ.restrict U) βminus ρ x₀ = annulusBallMassSize μ βminus ρ x₀ := by
  unfold annulusBallMassSize
  apply iInf_congr
  intro z
  apply iInf_congr
  intro hz
  apply iInf_congr
  intro r
  apply iInf_congr
  intro hr
  rw [Measure.restrict_apply isOpen_ball.measurableSet, inter_eq_left.mpr (hball z hz r hr)]

/-- The Green-potential supremum is determined by the measure on its annulus. -/
theorem annulusGreenPotentialSup_restrict (μ : Measure ℂ) (x₀ : ℂ) (a b : ℝ)
    (U : Set ℂ) (hAU : annulus x₀ a b ⊆ U) :
    annulusGreenPotentialSup (μ.restrict U) x₀ a b = annulusGreenPotentialSup μ x₀ a b := by
  simp only [annulusGreenPotentialSup, Measure.restrict_restrict_of_subset hAU]

/-- The very-good condition is local to any set containing every region used
by the three criteria. -/
theorem isVeryGoodAnnulus_restrict_of_subsets (μ : Measure ℂ) (βminus ρ : ℝ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (U : Set ℂ)
    (hA : annulus x₀ (ρ / 4) (2 * ρ) ⊆ U)
    (hball : ∀ z ∈ annulus x₀ (ρ / 2) ρ, ∀ r ∈ Ioo 0 (ρ / 4), ball z r ⊆ U)
    (hgood : ∀ n : ℕ, ∀ z ∈ annulus x₀ (ρ / 2) ρ,
      ∀ r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ),
        annulus z (3 * r) (5 * r) ⊆ U) :
    IsVeryGoodAnnulus (μ.restrict U) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  have hcount (n : ℕ) (z : ℂ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) :
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ.restrict U) r z a b} =
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b} := by
    ext r
    simp only [mem_ofPred_eq]
    by_cases hr : r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ)
    · rw [isGoodAnnulus_restrict μ r z a b U (hgood n z hz r hr)]
    · simp [hr]
  have hmass : (μ.restrict U) (annulus x₀ (ρ / 4) (2 * ρ)) =
      μ (annulus x₀ (ρ / 4) (2 * ρ)) := by
    have hAm : MeasurableSet (annulus x₀ (ρ / 4) (2 * ρ)) :=
      (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    rw [Measure.restrict_apply hAm, inter_eq_left.mpr hA]
  have hcriterion :
      (∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        (∃ j k : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ.restrict U) r z a b}.ncard : ℝ)) ↔
      (∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
        (∃ j k : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b}.ncard : ℝ)) := by
    constructor <;> intro H n hn z hz hl
    · simpa only [hcount n z hz] using H n hn z hz hl
    · simpa only [hcount n z hz] using H n hn z hz hl
  unfold IsVeryGoodAnnulus
  rw [annulusBallMassSize_restrict μ βminus ρ x₀ U hball,
    annulusGreenPotentialSup_restrict μ x₀ (ρ / 4) (2 * ρ) U hA, hmass, hcriterion]

/-- Every measure-dependent region in the very-good condition at scale `ρ`
is contained in the disk of radius `6ρ`. -/
theorem isVeryGoodAnnulus_restrict_ball_six (μ : Measure ℂ) (βminus ρ : ℝ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (hρ : 0 < ρ) :
    IsVeryGoodAnnulus (μ.restrict (ball x₀ (6 * ρ))) βminus ρ x₀ N₀
        a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  apply isVeryGoodAnnulus_restrict_of_subsets
  · exact Set.sdiff_subset.trans (ball_subset_ball (by linarith))
  · intro z hz r hr y hy
    have hz' : dist z x₀ < ρ := hz.1
    have hy' : dist y z < r := hy
    have htri := dist_triangle y z x₀
    change dist y x₀ < 6 * ρ
    linarith [hr.2]
  · intro n z hz r hr y hy
    have hz' : dist z x₀ < ρ := hz.1
    have hy' : dist y z < 5 * r := hy.1
    have hdyad : dyadicScale n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hsqrt : Real.sqrt (dyadicScale n) ≤ 1 := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hdyad
    have hrad : r ≤ ρ := hr.2.trans (by nlinarith)
    have htri := dist_triangle y z x₀
    change dist y x₀ < 6 * ρ
    linarith

/-- Annulus-ball comparison is determined by the measure in its outer ball. -/
theorem annulusBallComparison_restrict (μ : Measure ℂ) (n : ℕ) (z : ℂ) (m : ℝ)
    (U : Set ℂ) (hball : ball z (dyadicScale n) ⊆ U) :
    AnnulusBallComparison (μ.restrict U) n z m ↔ AnnulusBallComparison μ n z m := by
  have hA : annulus z (dyadicScale (n + 1)) (dyadicScale n) ⊆ U :=
    Set.sdiff_subset.trans hball
  have hAm : MeasurableSet (annulus z (dyadicScale (n + 1)) (dyadicScale n)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  simp only [AnnulusBallComparison, Measure.restrict_apply isOpen_ball.measurableSet,
    Measure.restrict_apply hAm, inter_eq_left.mpr hball, inter_eq_left.mpr hA]

/-- The joint very-good and comparison event at dyadic scale `n` is determined
by the measure in the concentric ball of radius `6 * dyadicScale n`. -/
theorem veryGoodComparable_restrict_ball_six (μ : Measure ℂ) (βminus : ℝ) (z : ℂ)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (n : ℕ) :
    (IsVeryGoodAnnulus (μ.restrict (ball z (6 * dyadicScale n))) βminus
        (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison (μ.restrict (ball z (6 * dyadicScale n))) n z m) ↔
    (IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison μ n z m) := by
  apply and_congr
  · exact isVeryGoodAnnulus_restrict_ball_six μ βminus (dyadicScale n) z N₀
      a b C₁m C₁p C₂m C₂p C₃ (dyadicScale_pos n)
  · apply annulusBallComparison_restrict
    apply ball_subset_ball
    have := dyadicScale_pos n
    linarith

/-- If two measures agree on the relevant disk up to a finite nonzero scalar,
then the joint very-good and comparison event agrees. -/
theorem veryGoodComparable_congr_of_restrict_eq_smul (μ ν : Measure ℂ) (βminus : ℝ)
    (z : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (n : ℕ)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞)
    (h : μ.restrict (ball z (6 * dyadicScale n)) =
      c • ν.restrict (ball z (6 * dyadicScale n))) :
    (IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison μ n z m) ↔
    (IsVeryGoodAnnulus ν βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison ν n z m) := by
  rw [← veryGoodComparable_restrict_ball_six μ βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m n,
    h, isVeryGoodAnnulus_smul _ _ _ _ _ _ _ _ _ _ _ _ hc hct,
    annulusBallComparison_smul _ _ _ _ hc hct]
  exact veryGoodComparable_restrict_ball_six ν βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m n

/-- Agreement up to scale on a region containing the relevant disk implies
agreement of the joint event. -/
theorem veryGoodComparable_congr_of_restrict_eq_smul_on (μ ν : Measure ℂ) (βminus : ℝ)
    (z : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (n : ℕ) (U : Set ℂ)
    (hU : ball z (6 * dyadicScale n) ⊆ U) {c : ℝ≥0∞} (hc : c ≠ 0) (hct : c ≠ ∞)
    (h : μ.restrict U = c • ν.restrict U) :
    (IsVeryGoodAnnulus μ βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison μ n z m) ↔
    (IsVeryGoodAnnulus ν βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison ν n z m) := by
  apply veryGoodComparable_congr_of_restrict_eq_smul μ ν βminus z N₀
    a b C₁m C₁p C₂m C₂p C₃ m n hc hct
  have h' := congrArg (fun η : Measure ℂ => η.restrict (ball z (6 * dyadicScale n))) h
  simpa only [Measure.restrict_restrict_of_subset hU, Measure.restrict_smul] using h'

open Classical in
/-- A germ-measurable measure representative, agreeing locally up to a finite
nonzero scalar, gives germ-measurable versions of all sufficiently small
joint indicators. -/
theorem ae_local_veryGoodComparable_indicators_of_measure_representative
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (germ : MeasurableSpace Ω)
    (μ ν : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (K : ℕ)
    (hν : @Measurable Ω (Measure ℂ) germ _ ν)
    (hmeas : ∀ n, MeasurableSet {η : Measure ℂ |
      IsVeryGoodAnnulus η βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃})
    (hrep : ∀ n, K ≤ n → ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      (μ ω).restrict (ball z (6 * dyadicScale n)) =
        c • (ν ω).restrict (ball z (6 * dyadicScale n))) :
    ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ germ _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  let Y : ℕ → Ω → ℝ := fun n ω =>
    if IsVeryGoodAnnulus (ν ω) βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
      AnnulusBallComparison (ν ω) n z m then 1 else 0
  refine ⟨Y, ?_, ?_⟩
  · intro n _
    let : MeasurableSpace Ω := germ
    have hE : MeasurableSet {ω : Ω |
        IsVeryGoodAnnulus (ν ω) βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (ν ω) n z m} :=
      ((hmeas n).inter (measurableSet_annulusBallComparison n z m)).preimage hν
    exact measurable_const.piecewise hE measurable_const
  · intro n hn
    filter_upwards [hrep n hn] with ω hω
    obtain ⟨c, hc, hct, heq⟩ := hω
    have hiff := veryGoodComparable_congr_of_restrict_eq_smul (μ ω) (ν ω) βminus z N₀
      a b C₁m C₁p C₂m C₂p C₃ m n hc hct heq
    simp only [Y, hiff]

open Classical in
/-- A single local representative on a region containing all sufficiently
small test disks supplies all of their germ-measurable indicator versions. -/
theorem ae_local_veryGoodComparable_indicators_of_local_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (germ : MeasurableSpace Ω)
    (μ ν : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (K : ℕ) (U : Set ℂ)
    (hν : @Measurable Ω (Measure ℂ) germ _ ν)
    (hU : ∀ n, K ≤ n → ball z (6 * dyadicScale n) ⊆ U)
    (hmeas : ∀ n, MeasurableSet {η : Measure ℂ |
      IsVeryGoodAnnulus η βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃})
    (hrep : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      (μ ω).restrict U = c • (ν ω).restrict U) :
    ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ germ _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  refine @ae_local_veryGoodComparable_indicators_of_measure_representative Ω mΩ P germ μ ν βminus z
    N₀ a b C₁m C₁p C₂m C₂p C₃ m K hν hmeas ?_
  intro n hn
  filter_upwards [hrep] with ω ⟨c, hc, hct, heq⟩
  refine ⟨c, hc, hct, ?_⟩
  have h' := congrArg (fun η : Measure ℂ => η.restrict (ball z (6 * dyadicScale n))) heq
  simpa only [Measure.restrict_restrict_of_subset (hU n hn), Measure.restrict_smul] using h'

/-- The disks needed by the joint event eventually fit in any positive disk. -/
theorem eventually_ball_six_dyadic_subset (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, ∀ n, K ≤ n → ball z (6 * dyadicScale n) ⊆ ball z ε := by
  obtain ⟨K, hK⟩ := dyadicScale_germ_cofinal.2 (ε / 6) (by linarith)
  refine ⟨K, fun n hn => ball_subset_ball ?_⟩
  have h := dyadicScale_germ_cofinal.1 hn
  linarith

open Classical in
/-- Local measure representatives modulo a finite nonzero scalar provide the
almost-sure germ-locality hypothesis of the stationary frequency theorem. -/
theorem ae_local_veryGoodComparable_indicators_of_local_measures
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (βminus : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hmeas : ∀ n, MeasurableSet {η : Measure ℂ |
      IsVeryGoodAnnulus η βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃})
    (hrep : ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        (μ ω).restrict (ball z ε) = c • (ν ω).restrict (ball z ε)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) βminus (dyadicScale n) z N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n z m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  intro ε hε
  obtain ⟨ν, hν, hνrep⟩ := hrep ε hε
  obtain ⟨K, hK⟩ := eventually_ball_six_dyadic_subset z hε
  refine ⟨K, ?_⟩
  exact @ae_local_veryGoodComparable_indicators_of_local_measure Ω mΩ P (germ ε)
    μ ν βminus z N₀ a b C₁m C₁p C₂m C₂p C₃ m K (ball z ε) hν hK hmeas hνrep

end HarmonicBalls
