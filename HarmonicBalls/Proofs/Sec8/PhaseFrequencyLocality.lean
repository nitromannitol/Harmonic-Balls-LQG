import HarmonicBalls.Proofs.Sec8.PhaseVeryGoodLocality

/-! # Locality of phase-shifted block frequency

The imported Section 8 path development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace HarmonicBalls

/-- If two measures agree up to a finite nonzero factor on a neighborhood of
zero, their phase-shifted good-scale predicates agree at all small scales. -/
theorem eventually_phaseVeryGoodComparable_iff_of_restrict_eq_smul
    {μ ν : Measure ℂ} {ε : ℝ} (hε : 0 < ε) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ∞)
    (heq : μ.restrict (ball 0 ε) = c • ν.restrict (ball 0 ε))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) :
    ∃ K, ∀ n, K ≤ n → ∀ phase : ℂ,
      (PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison μ n 0 m) ↔
      (PhaseVeryGoodAnnulus ν β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison ν n 0 m) := by
  obtain ⟨K, hK⟩ := eventually_ball_six_dyadic_subset (0 : ℂ) hε
  refine ⟨K, ?_⟩
  intro n hn phase
  let U := ball (0 : ℂ) (6 * dyadicScale n)
  have hrestrict : μ.restrict U = c • ν.restrict U := by
    have h := congrArg (fun η : Measure ℂ => η.restrict U) heq
    have hsub : U ⊆ ball (0 : ℂ) ε := hK n hn
    rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub,
      Measure.restrict_restrict_of_subset hsub] at h
    exact h
  have hball : ball (0 : ℂ) (dyadicScale n) ⊆ U :=
    ball_subset_ball (by have := dyadicScale_pos n; linarith)
  have hg (η : Measure ℂ) :
      PhaseVeryGoodAnnulus (η.restrict U) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ phase ↔
        PhaseVeryGoodAnnulus η β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ phase :=
    phaseVeryGoodAnnulus_restrict_ball_six η β (dyadicScale n) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ phase (dyadicScale_pos n)
  constructor <;> intro h
  · have hμ : PhaseVeryGoodAnnulus (μ.restrict U) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison (μ.restrict U) n 0 m :=
      ⟨(hg μ).2 h.1, (annulusBallComparison_restrict μ n 0 m U hball).2 h.2⟩
    rw [hrestrict, phaseVeryGoodAnnulus_smul _ _ _ _ _ _ _ _ _ _ _ _ _ hc hct,
      annulusBallComparison_smul _ _ _ _ hc hct] at hμ
    exact ⟨(hg ν).1 hμ.1, (annulusBallComparison_restrict ν n 0 m U hball).1 hμ.2⟩
  · have hν : PhaseVeryGoodAnnulus (ν.restrict U) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison (ν.restrict U) n 0 m :=
      ⟨(hg ν).2 h.1, (annulusBallComparison_restrict ν n 0 m U hball).2 h.2⟩
    have hμ : PhaseVeryGoodAnnulus (μ.restrict U) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ phase ∧ AnnulusBallComparison (μ.restrict U) n 0 m := by
      rw [hrestrict, phaseVeryGoodAnnulus_smul _ _ _ _ _ _ _ _ _ _ _ _ _ hc hct,
        annulusBallComparison_smul _ _ _ _ hc hct]
      exact hν
    exact ⟨(hg μ).1 hμ.1, (annulusBallComparison_restrict μ n 0 m U hball).1 hμ.2⟩

/-- Phase block frequency depends only on the measure near zero, up to a
finite nonzero constant. The phase may vary arbitrarily with the scale. -/
theorem phaseVeryGoodComparable_blockFrequency_iff_of_restrict_eq_smul
    {μ ν : Measure ℂ} {ε : ℝ} (hε : 0 < ε) {c : ℝ≥0∞}
    (hc : c ≠ 0) (hct : c ≠ ∞)
    (heq : μ.restrict (ball 0 ε) = c • ν.restrict (ball 0 ε))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (phase : ℕ → ℂ) :
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (phase n) ∧
        AnnulusBallComparison μ n 0 m}.ncard : ℝ)) ↔
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (phase n) ∧
        AnnulusBallComparison ν n 0 m}.ncard : ℝ)) := by
  obtain ⟨K, hK⟩ := eventually_phaseVeryGoodComparable_iff_of_restrict_eq_smul
    hε hc hct heq β N₀ a b C₁m C₁p C₂m C₂p C₃ m
  have hsets (N : ℕ) (hN : K ≤ N) :
      {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (phase n) ∧
        AnnulusBallComparison μ n 0 m} =
      {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (phase n) ∧
        AnnulusBallComparison ν n 0 m} := by
    ext n
    simp only [mem_ofPred_eq]
    by_cases hn : n ∈ Icc (N + 1) (2 * N)
    · have hkn : K ≤ n := le_trans hN (le_trans (Nat.le_succ N) hn.1)
      simp only [hn, true_and, hK n hkn (phase n)]
    · simp only [hn, false_and]
  constructor <;> intro h
  · filter_upwards [h, eventually_ge_atTop K] with N hN hKN
    rwa [hsets N hKN] at hN
  · filter_upwards [h, eventually_ge_atTop K] with N hN hKN
    rwa [hsets N hKN]

/-- The phase-frequency event is unchanged by normalizing on any positive
finite-mass neighborhood of zero. -/
theorem phaseVeryGoodComparable_blockFrequency_iff_normalizedRestriction
    (μ : Measure ℂ) {ε : ℝ} (hε : 0 < ε)
    (hzero : μ (ball 0 ε) ≠ 0) (htop : μ (ball 0 ε) ≠ ∞)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (phase : ℕ → ℂ) :
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ (phase n) ∧
        AnnulusBallComparison μ n 0 m}.ncard : ℝ)) ↔
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (normalizedRestriction μ (ball 0 ε)) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (phase n) ∧
        AnnulusBallComparison (normalizedRestriction μ (ball 0 ε)) n 0 m}.ncard : ℝ)) := by
  exact phaseVeryGoodComparable_blockFrequency_iff_of_restrict_eq_smul hε hzero htop
    (restrict_eq_smul_normalizedRestriction μ isOpen_ball.measurableSet hzero htop)
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ phase

end HarmonicBalls
