import HarmonicBalls.Proofs.Sec8.VeryGoodLocality
import HarmonicBalls.Proofs.Sec8.OrdinaryFieldNormalizedRestriction
import HarmonicBalls.Proofs.Sec6.CriterionThreeLocalComparison

/-! # Size-annulus locality of very-good annuli

The imported Section 8 locality development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The very-good condition is local to any set containing the regions used
by the size criteria and the good annuli tested at scales at least `N₀`. -/
theorem isVeryGoodAnnulus_restrict_of_fine_subsets (μ : Measure ℂ) (βminus ρ : ℝ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (U : Set ℂ)
    (hA : annulus x₀ (ρ / 4) (2 * ρ) ⊆ U)
    (hball : ∀ z ∈ annulus x₀ (ρ / 2) ρ, ∀ r ∈ Ioo 0 (ρ / 4), ball z r ⊆ U)
    (hgood : ∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus x₀ (ρ / 2) ρ,
      ∀ r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ),
        annulus z (3 * r) (5 * r) ⊆ U) :
    IsVeryGoodAnnulus (μ.restrict U) βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  have hcount (n : ℕ) (hn : N₀ ≤ n) (z : ℂ) (hz : z ∈ annulus x₀ (ρ / 2) ρ) :
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus (μ.restrict U) r z a b} =
      {r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧ IsGoodAnnulus μ r z a b} := by
    ext r
    simp only [mem_ofPred_eq]
    by_cases hr : r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ)
    · rw [isGoodAnnulus_restrict μ r z a b U (hgood n hn z hz r hr)]
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
    · simpa only [hcount n hn z hz] using H n hn z hz hl
    · simpa only [hcount n hn z hz] using H n hn z hz hl
  unfold IsVeryGoodAnnulus
  rw [annulusBallMassSize_restrict μ βminus ρ x₀ U hball,
    annulusGreenPotentialSup_restrict μ x₀ (ρ / 4) (2 * ρ) U hA, hmass, hcriterion]

/-- At sufficiently fine scales, all three criteria only inspect the size
annulus, even for the absolute lattice used in the definition. -/
theorem isVeryGoodAnnulus_restrict_size_annulus (μ : Measure ℂ) (βminus ρ : ℝ)
    (x₀ : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hρ : 0 < ρ) (hN₀ : 9 ≤ N₀) :
    IsVeryGoodAnnulus (μ.restrict (annulus x₀ (ρ / 4) (2 * ρ))) βminus ρ x₀ N₀
        a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  apply isVeryGoodAnnulus_restrict_of_fine_subsets
  · exact subset_rfl
  · intro z hz r hr y hy
    have hzouter : dist z x₀ < ρ := hz.1
    have hzinner : ρ / 2 < dist z x₀ := lt_of_not_ge hz.2
    have hyz : dist y z < r := hy
    have htri₁ := dist_triangle y z x₀
    have htri₂ := dist_triangle z y x₀
    rw [dist_comm z y] at htri₂
    constructor
    · change dist y x₀ < 2 * ρ
      linarith [hr.2]
    · change ¬ dist y x₀ ≤ ρ / 4
      linarith [hr.2]
  · intro n hn z hz r hr
    have hsqrt := sqrt_dyadicScale_le_one_twentieth (hN₀.trans hn)
    have hbound : 5 * r ≤ ρ / 4 := by
      have h := mul_le_mul_of_nonneg_right hsqrt hρ.le
      linarith [hr.2]
    exact goodAnnulus_subset_size_annulus hρ hz hbound

/-- At sufficiently fine scales, normalizing the restriction to the size
annulus preserves the very-good event whenever its mass is finite and nonzero. -/
theorem isVeryGoodAnnulus_normalizedRestriction_size_annulus
    (μ : Measure ℂ) (βminus ρ : ℝ) (x₀ : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (hρ : 0 < ρ) (hN₀ : 9 ≤ N₀)
    (hzero : μ (annulus x₀ (ρ / 4) (2 * ρ)) ≠ 0)
    (htop : μ (annulus x₀ (ρ / 4) (2 * ρ)) ≠ ∞) :
    IsVeryGoodAnnulus (normalizedRestriction μ (annulus x₀ (ρ / 4) (2 * ρ)))
        βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ βminus ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  unfold normalizedRestriction
  rw [isVeryGoodAnnulus_smul _ _ _ _ _ _ _ _ _ _ _ _
    (ENNReal.inv_ne_zero.mpr htop) (ENNReal.inv_ne_top.mpr hzero)]
  exact isVeryGoodAnnulus_restrict_size_annulus μ βminus ρ x₀ N₀
    a b C₁m C₁p C₂m C₂p C₃ hρ hN₀

end HarmonicBalls.Section6
