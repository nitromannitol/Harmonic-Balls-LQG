import HarmonicBalls.FirstPass.S8c.GoodSet
import HarmonicBalls.Proofs.Sec8.PhaseFrequencyLocality
import HarmonicBalls.Proofs.Sec8.PhaseCriterionTranslation

/-! # Locality of the good event at the root (FIRST-PASS fp-S8c-8-2-local, step G: locality identity)

For a root `z` and a radius `r > 0`, the eventual very-good count of `μ` at `z` (lattice anchored at the original origin,
as printed in (VG-iii), `Defs/Annuli.lean`) equals, eventually in `N`, the eventual phase count of the normalised
recentred restriction `massNormalize r (recenteredRestriction μ r z)` at the origin with lattice phase `-z`.
Route: per-scale translation (`isVeryGoodAnnulus_iff_centered_shifted_phase`, exact), then restriction locality
(`eventually_phaseVeryGoodComparable_iff_of_restrict_eq_smul`) applied to the translated measure and its normalised
restriction to `ball 0 r`, with the scalar `μ(ball z (r/2))` (positive and finite).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

section Translation

theorem isVeryGoodAnnulus_iff_phaseVeryGoodAnnulus_map (μ : Measure ℂ) (β ρ : ℝ) (z : ℂ) (N : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus μ β ρ z N a b C₁m C₁p C₂m C₂p C₃ ↔
      PhaseVeryGoodAnnulus (μ.map (fun w : ℂ => w - z)) β ρ 0 N a b C₁m C₁p C₂m C₂p C₃ (-z) := by
  unfold PhaseVeryGoodAnnulus
  exact isVeryGoodAnnulus_iff_centered_shifted_phase μ β ρ z N a b C₁m C₁p C₂m C₂p C₃

/-- The very-good count at the root `z` is the phase count of the translated measure at the origin, exactly. -/
theorem veryGoodComparableScaleCount_eq_map (μ : Measure ℂ) (β : ℝ) (z : ℂ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (N : ℕ) :
    veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N =
      {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ.map (fun w : ℂ => w - z)) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (-z) ∧
        AnnulusBallComparison (μ.map (fun w : ℂ => w - z)) n 0 m}.ncard := by
  unfold veryGoodComparableScaleCount
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, isVeryGoodAnnulus_iff_phaseVeryGoodAnnulus_map,
    annulusBallComparison_map_sub μ z n m]

end Translation

section Locality

/-- The eventual very-good count at the root `z` equals, eventually in `N`, the eventual phase count of the
normalised recentred restriction at the origin with lattice phase `-z`. -/
theorem veryGoodComparableScaleCount_eventually_iff_recentredGood (μ : Measure ℂ)
    [IsLocallyFiniteMeasure μ] (z : ℂ) (r : ℝ) (hr : 0 < r) (hpos : 0 < μ (ball z (r / 2)))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) :
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) ↔
    ((z, massNormalize r (recenteredRestriction μ r z)) ∈
      recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ) := by
  have hpre0 : (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) r = ball z r := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have hpreh : (fun w : ℂ => w - z) ⁻¹' ball (0 : ℂ) (r / 2) = ball z (r / 2) := by
    ext w
    simp [mem_ball, dist_eq_norm]
  have hball : μ (ball z (r / 2)) ≠ ∞ := measure_ball_lt_top.ne
  have hballr : μ (ball z r) ≠ ∞ := measure_ball_lt_top.ne
  -- the recentred restriction is the translated measure restricted to `ball 0 r`
  have hLeq : recenteredRestriction μ r z = (μ.map (fun w : ℂ => w - z)).restrict (ball 0 r) := by
    unfold recenteredRestriction
    rw [Measure.restrict_map (measurable_sub_const z) measurableSet_ball, hpre0]
  have hLball : (recenteredRestriction μ r z) (ball 0 (r / 2)) = μ (ball z (r / 2)) := by
    rw [hLeq, Measure.restrict_apply measurableSet_ball,
      Set.inter_eq_left.mpr (ball_subset_ball (by linarith)),
      Measure.map_apply (measurable_sub_const z) measurableSet_ball, hpreh]
  have hLfin : IsFiniteMeasure (recenteredRestriction μ r z) := by
    rw [hLeq]
    refine isFiniteMeasure_restrict.mpr ?_
    rw [Measure.map_apply (measurable_sub_const z) measurableSet_ball, hpre0]
    exact hballr
  have hνfin : IsFiniteMeasure (massNormalize r (recenteredRestriction μ r z)) := by
    refine ⟨?_⟩
    unfold massNormalize
    rw [Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top ?_ (measure_lt_top _ _)
    rw [ENNReal.inv_lt_top, hLball]
    exact hpos
  have hfp : finitePart (massNormalize r (recenteredRestriction μ r z)) =
      massNormalize r (recenteredRestriction μ r z) :=
    finitePart_eq_of_locallyFinite _
  -- the restricted normalised measure carries the same shape up to the scalar `μ(ball z (r/2))`
  have hLr : (recenteredRestriction μ r z).restrict (ball 0 r) = recenteredRestriction μ r z := by
    rw [hLeq, Measure.restrict_restrict measurableSet_ball, inter_self]
  have heq : (μ.map (fun w : ℂ => w - z)).restrict (ball 0 r) =
      μ (ball z (r / 2)) • (massNormalize r (recenteredRestriction μ r z)).restrict (ball 0 r) := by
    rw [← hLeq]
    unfold massNormalize
    rw [Measure.restrict_smul, hLr, hLball, smul_smul,
      ENNReal.mul_inv_cancel hpos.ne' hball, one_smul]
  obtain ⟨K, hK⟩ := eventually_phaseVeryGoodComparable_iff_of_restrict_eq_smul
    (μ := μ.map (fun w : ℂ => w - z)) (ν := massNormalize r (recenteredRestriction μ r z))
    hr hpos.ne' hball heq β N₀ a b C₁m C₁p C₂m C₂p C₃ m
  have hG : ∀ n : ℕ, recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n
      (z, massNormalize r (recenteredRestriction μ r z)) ↔
      (PhaseVeryGoodAnnulus (massNormalize r (recenteredRestriction μ r z)) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (-z) ∧
        AnnulusBallComparison (massNormalize r (recenteredRestriction μ r z)) n 0 m) := by
    intro n
    simp only [recentredScalePred, hfp]
  have hcountEq : ∀ N : ℕ, K ≤ N →
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ.map (fun w : ℂ => w - z)) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (-z) ∧
        AnnulusBallComparison (μ.map (fun w : ℂ => w - z)) n 0 m}).ncard =
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n
          (z, massNormalize r (recenteredRestriction μ r z))}).ncard := by
    intro N hN
    congr 1
    ext n
    simp only [Set.mem_ofPred_eq, hG n]
    constructor
    · rintro ⟨hn, h⟩
      have hKn : K ≤ n := by
        have := (Set.mem_Icc.mp hn).1
        omega
      exact ⟨hn, ((hK n hKn (-z)).1 h)⟩
    · rintro ⟨hn, h⟩
      have hKn : K ≤ n := by
        have := (Set.mem_Icc.mp hn).1
        omega
      exact ⟨hn, ((hK n hKn (-z)).2 h)⟩
  have hev : ∀ᶠ N : ℕ in atTop,
      ((1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) ↔
      ((1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          recentredScalePred β N₀ a b C₁m C₁p C₂m C₂p C₃ m n
            (z, massNormalize r (recenteredRestriction μ r z))}.ncard : ℝ)) := by
    rw [Filter.eventually_atTop]
    refine ⟨K, fun N hN => ?_⟩
    rw [veryGoodComparableScaleCount_eq_map, hcountEq N hN]
  exact Filter.eventually_congr hev

end Locality

#print axioms veryGoodComparableScaleCount_eventually_iff_recentredGood

end HarmonicBalls
