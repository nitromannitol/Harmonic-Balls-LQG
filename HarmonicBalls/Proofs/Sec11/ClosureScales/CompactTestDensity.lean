import Mathlib

/-!
# Lemma l:r6-transfer, step 3b: a countable family of compactly supported tests

Source: `notes/sec11-proof/sec11-proof-r7.tex`, Lemma `l:r6-transfer`, the measure part (lines 560-600). The LQG measure
is the vague limit of the LQG approximations, and vague convergence is tested against compactly supported continuous
functions. This file gives a countable family `Ψ` of compactly supported continuous tests such that every continuous
`ψ` vanishing outside a closed ball is uniformly approximated, on the next larger closed ball, by a member of `Ψ`
that vanishes outside that larger ball. The family is the countable determining family used for the good set and for
the Riesz functional in the measure part; it is built from a countable dense subset of `C(ℂ, ℝ)` and radial cutoffs.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric

/-- The cutoff `χ_R(z) = max 0 (min 1 (R + 1 - |z|))`: equal to `1` on the closed ball of radius `R`, zero outside the
closed ball of radius `R + 1`, with values in `[0, 1]`. -/
noncomputable def cutoffBall (R : ℕ) (z : ℂ) : ℝ :=
  max 0 (min 1 ((R : ℝ) + 1 - ‖z‖))

theorem continuous_cutoffBall (R : ℕ) : Continuous (cutoffBall R) := by
  unfold cutoffBall
  fun_prop

theorem cutoffBall_nonneg (R : ℕ) (z : ℂ) : 0 ≤ cutoffBall R z :=
  le_max_left _ _

theorem cutoffBall_le_one (R : ℕ) (z : ℂ) : cutoffBall R z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem cutoffBall_eq_one {R : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (R : ℝ)) : cutoffBall R z = 1 := by
  unfold cutoffBall
  have h1 : (1 : ℝ) ≤ (R : ℝ) + 1 - ‖z‖ := by linarith
  rw [min_eq_left h1]
  exact max_eq_right zero_le_one

theorem cutoffBall_eq_zero {R : ℕ} {z : ℂ} (hz : (R : ℝ) + 1 ≤ ‖z‖) : cutoffBall R z = 0 := by
  unfold cutoffBall
  have h1 : (R : ℝ) + 1 - ‖z‖ ≤ 0 := by linarith
  rw [min_eq_right (h1.trans zero_le_one), max_eq_left h1]

/-- **A countable determining family of tests.** There is a countable set `Ψ` of compactly supported continuous
functions such that, for every continuous `ψ` vanishing outside the closed ball of radius `R` (`R : ℕ`) and every
`ε > 0`, some `g ∈ Ψ` vanishes outside the closed ball of radius `R + 1` and satisfies `|g - ψ| < ε` on it. -/
theorem exists_countable_compactSupport_approx :
    ∃ Ψ : Set (ℂ → ℝ), Ψ.Countable ∧ (∀ g ∈ Ψ, Continuous g ∧ HasCompactSupport g) ∧
      ∀ (ψ : ℂ → ℝ), Continuous ψ → ∀ R : ℕ, (∀ z : ℂ, (R : ℝ) < ‖z‖ → ψ z = 0) →
        ∀ ε : ℝ, 0 < ε → ∃ g ∈ Ψ, (∀ z : ℂ, (R : ℝ) + 1 < ‖z‖ → g z = 0) ∧
          ∀ z : ℂ, ‖z‖ ≤ (R : ℝ) + 1 → |g z - ψ z| < ε := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(ℂ, ℝ)
  let Ψ : Set (ℂ → ℝ) :=
    (fun p : ℕ × C(ℂ, ℝ) => fun z => cutoffBall p.1 z * p.2 z) '' (univ ×ˢ D)
  have hΨc : Ψ.Countable := (countable_univ.prod hDc).image _
  have hΨ : ∀ g ∈ Ψ, Continuous g ∧ HasCompactSupport g := by
    rintro _ ⟨⟨R, d⟩, -, rfl⟩
    refine ⟨(continuous_cutoffBall R).mul d.continuous, ?_⟩
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1)) fun z hz => ?_
    have hz' : (R : ℝ) + 1 < ‖z‖ := by
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact hz
    simp only [cutoffBall_eq_zero hz'.le, zero_mul]
  refine ⟨Ψ, hΨc, hΨ, ?_⟩
  intro ψ hψ R hψR ε hε
  set K : Set ℂ := closedBall (0 : ℂ) ((R : ℝ) + 1) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let ψc : C(ℂ, ℝ) := ⟨ψ, hψ⟩
  let U : Set C(ℂ, ℝ) := {d | dist (d.restrict K) (ψc.restrict K) < ε}
  have hU : IsOpen U :=
    isOpen_lt ((ContinuousMap.continuous_restrict K).dist continuous_const) continuous_const
  have hψU : ψc ∈ U := by
    show dist (ψc.restrict K) (ψc.restrict K) < ε
    rw [dist_self]
    exact hε
  obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open hU ⟨ψc, hψU⟩
  refine ⟨fun z => cutoffBall R z * d z, ⟨(R, d), ⟨mem_univ _, hdD⟩, rfl⟩, ?_, ?_⟩
  · intro z hz
    have hz' : (R : ℝ) + 1 < ‖z‖ := hz
    simp only [cutoffBall_eq_zero hz'.le, zero_mul]
  · intro z hz
    show |cutoffBall R z * d z - ψ z| < ε
    have hzK : z ∈ K := by
      rw [hK, mem_closedBall, dist_zero_right]
      exact hz
    have h1 := ContinuousMap.dist_apply_le_dist (f := d.restrict K) (g := ψc.restrict K) (⟨z, hzK⟩ : K)
    have hdist : dist (d z) (ψ z) < ε := lt_of_le_of_lt h1 (show dist (d.restrict K) (ψc.restrict K) < ε from hdU)
    rcases le_or_gt ‖z‖ (R : ℝ) with hzR | hzR
    · rw [cutoffBall_eq_one hzR, one_mul]
      rw [Real.dist_eq] at hdist
      exact hdist
    · have hψz : ψ z = 0 := hψR z hzR
      rw [Real.dist_eq, hψz, sub_zero] at hdist
      have ht : 0 ≤ cutoffBall R z := cutoffBall_nonneg R z
      have ht1 : cutoffBall R z ≤ 1 := cutoffBall_le_one R z
      rw [hψz, sub_zero, abs_mul, abs_of_nonneg ht]
      calc cutoffBall R z * |d z| ≤ 1 * |d z| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
        _ = |d z| := one_mul _
        _ < ε := hdist

end HarmonicBalls
