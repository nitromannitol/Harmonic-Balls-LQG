import HarmonicBalls.FirstPass.S8c.GoodSet
import HarmonicBalls.Proofs.Sec8.PhaseFrequencyLocality

/-! # The phase-sensitive tail of Lemma 8.2: named open step and reference-side locality

`LocalPhaseTailStep` is the Draft-shaped existential form of the phase tail (7),
with the constants of (6)-(8). It is a NEW step (this paper's Lemma 8.2 argument, which uses the
Section 6 probability bounds and the ergodicity of doubling times dilation); it is NOT frozen and NOT proved here.

`phaseCount_eventually_iff_normalized` is the reference-side locality: the eventual phase count of `ν` at the origin
equals that of its normalised restriction `massNormalize r (ν|_{B_r(0)})` (the reference observation V_j of
`FirstPass/S8c/LocalObservation.lean`), with the same phase.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- NEW, OPEN (not frozen): the phase-sensitive tail of Lemma 8.2 in the existential form of G-8-2 section 3.
For each `γ` and `βminus > (2+γ)²/2` there are `C₃`, and for `ζ > 0`, `b ∈ (0,1)`, the threshold `a = a_*` and
constants `C₁^±, C₂^±`, a start `N₁ ≥ 9`, and for each `N₀ ≥ N₁` a constant `m > 0`, such that for every whole-plane
GFF and every insertion-`γ` LQG measure `ν` on the same space, almost surely for Lebesgue-almost every phase `w`
(here the product `volume × P`, the phase being the first coordinate), the very-good frequency with threshold `a` and
phase `w` holds eventually. The constants are those of (6)-(8): `a_* = a / ((401^{γ²})²)`, the same `b`, `C₃`, size
constants, `N₀`, `m`. Equations (5)-(10) of the derivation of Lemma 8.2. -/
def LocalPhaseTailStep : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ βminus : ℝ, (2 + γ) ^ 2 / 2 < βminus →
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
  ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
  ∃ N₁ : ℕ, 9 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ν : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc ν →
    ∀ᵐ x ∂((volume : Measure ℂ).prod P), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν x.2) βminus (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ x.1 ∧
        AnnulusBallComparison (ν x.2) n 0 m}.ncard : ℝ)

/-- The normalised restriction of a locally finite measure to `ball 0 r` is a finite measure, when the mass of
`ball 0 (r/2)` is positive. -/
theorem isFiniteMeasure_massNormalize_restrict (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] {r : ℝ}
    (hr : 0 < r) (hpos : 0 < ν (ball 0 (r / 2))) :
    IsFiniteMeasure (massNormalize r (ν.restrict (ball 0 r))) := by
  have hballr : ν (ball 0 r) ≠ ∞ := measure_ball_lt_top.ne
  have hLfin : IsFiniteMeasure (ν.restrict (ball 0 r)) := isFiniteMeasure_restrict.mpr hballr
  refine ⟨?_⟩
  unfold massNormalize
  rw [Measure.smul_apply, smul_eq_mul]
  refine ENNReal.mul_lt_top ?_ (measure_lt_top _ _)
  rw [ENNReal.inv_lt_top, Measure.restrict_apply measurableSet_ball,
    Set.inter_eq_left.mpr (ball_subset_ball (by linarith))]
  exact hpos

/-- Reference-side locality: the eventual phase count of `ν` at the origin is the eventual phase count of its
normalised restriction to `ball 0 r`, for every phase `w`. -/
theorem phaseCount_eventually_iff_normalized (ν : Measure ℂ) [IsLocallyFiniteMeasure ν] (r : ℝ)
    (hr : 0 < r) (hpos : 0 < ν (ball 0 (r / 2))) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (w : ℂ) :
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ w ∧
        AnnulusBallComparison ν n 0 m}.ncard : ℝ)) ↔
    (∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (massNormalize r (ν.restrict (ball 0 r))) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ w ∧
        AnnulusBallComparison (massNormalize r (ν.restrict (ball 0 r))) n 0 m}.ncard : ℝ)) := by
  have hball : ν (ball 0 (r / 2)) ≠ ∞ := measure_ball_lt_top.ne
  have hLball : (ν.restrict (ball 0 r)) (ball 0 (r / 2)) = ν (ball 0 (r / 2)) := by
    rw [Measure.restrict_apply measurableSet_ball,
      Set.inter_eq_left.mpr (ball_subset_ball (by linarith))]
  have hLr : (ν.restrict (ball 0 r)).restrict (ball 0 r) = ν.restrict (ball 0 r) := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_self]
  have heq : ν.restrict (ball 0 r) =
      ν (ball 0 (r / 2)) • (massNormalize r (ν.restrict (ball 0 r))).restrict (ball 0 r) := by
    unfold massNormalize
    rw [Measure.restrict_smul, hLr, hLball, smul_smul,
      ENNReal.mul_inv_cancel hpos.ne' hball, one_smul]
  obtain ⟨K, hK⟩ := eventually_phaseVeryGoodComparable_iff_of_restrict_eq_smul
    (μ := ν) (ν := massNormalize r (ν.restrict (ball 0 r))) hr hpos.ne' hball heq β N₀
    a b C₁m C₁p C₂m C₂p C₃ m
  have hev : ∀ᶠ N : ℕ in atTop,
      ((1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ w ∧
          AnnulusBallComparison ν n 0 m}.ncard : ℝ)) ↔
      ((1 - ζ) * (N : ℝ) ≤
        ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (massNormalize r (ν.restrict (ball 0 r))) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ w ∧
          AnnulusBallComparison (massNormalize r (ν.restrict (ball 0 r))) n 0 m}.ncard : ℝ)) := by
    rw [Filter.eventually_atTop]
    refine ⟨K, fun N hN => ?_⟩
    have hS : {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ w ∧
        AnnulusBallComparison ν n 0 m} =
        {n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
          PhaseVeryGoodAnnulus (massNormalize r (ν.restrict (ball 0 r))) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ w ∧
          AnnulusBallComparison (massNormalize r (ν.restrict (ball 0 r))) n 0 m} := by
      ext n
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hn, h⟩
        have hKn : K ≤ n := by
          have := (Set.mem_Icc.mp hn).1
          omega
        exact ⟨hn, (hK n hKn w).1 h⟩
      · rintro ⟨hn, h⟩
        have hKn : K ≤ n := by
          have := (Set.mem_Icc.mp hn).1
          omega
        exact ⟨hn, (hK n hKn w).2 h⟩
    rw [hS]
  exact Filter.eventually_congr hev


end HarmonicBalls
