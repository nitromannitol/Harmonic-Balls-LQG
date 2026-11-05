import HarmonicBalls.Defs.Obstacle
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # The translated-ball misprint in Proposition 5.2

The paper's printed ball is centered at the pole. For a nonzero pole,
the printed inclusion fails even at the reference time, independently of
any obstacle-problem or LQG assumptions. The frozen statement uses the
origin-centered ball, as explained in its docstring.
-/

namespace HarmonicBalls

open Metric Set MeasureTheory
open scoped Pointwise InnerProductSpace

/-- A nonempty bounded planar set cannot be contained in its own Minkowski
sum with every sufficiently small ball centered at a nonzero point. -/
theorem exists_small_ball_not_containing_closure_add
    {A : Set ℂ} (hA : A.Nonempty) (hAb : Bornology.IsBounded A)
    {z : ℂ} (hz : z ≠ 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ¬ closure A ⊆ A + ball z ε := by
  have hcomp : IsCompact (closure A) := hAb.isCompact_closure
  have hcont : Continuous (fun w : ℂ => ⟪z, w⟫_ℝ) :=
    continuous_const.inner continuous_id
  obtain ⟨x, hx, hxmin⟩ := hcomp.exists_isMinOn (hA.mono subset_closure) hcont.continuousOn
  have hopen : IsOpen {w : ℂ | 0 < ⟪z, w⟫_ℝ} := isOpen_lt continuous_const hcont
  have hzpos : z ∈ {w : ℂ | 0 < ⟪z, w⟫_ℝ} := real_inner_self_pos.mpr hz
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hopen z hzpos
  refine ⟨ε₀, hε₀, fun ε hε hsubset => ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hsubset hx
  have hbpos : 0 < ⟪z, b⟫_ℝ := hball (ball_subset_ball hε.2.le hb)
  have hmin := hxmin (subset_closure ha)
  change a + b = x at hab
  change ⟪z, x⟫_ℝ ≤ ⟪z, a⟫_ℝ at hmin
  rw [← hab, inner_add_right] at hmin
  linarith

/-- For every nonzero interior pole and every time, the inclusion printed in
Proposition 5.2 fails at the reference time for all sufficiently small radii. -/
theorem cluster_translated_ball_inclusion_fails
    (μ : Measure ℂ) {r : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r)
    (hz0 : z ≠ 0) (t : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀,
      ¬ closure (cluster μ r z t) ⊆ cluster μ r z t + ball z ε :=
  exists_small_ball_not_containing_closure_add ⟨z, self_mem_cluster hz⟩
    (isBounded_ball.subset cluster_subset_ball) hz0

/-- The right-continuity formula printed in Proposition 5.2 is false at
any nonzero interior pole and any reference time, already for `s = t`. -/
theorem cluster_printed_right_continuity_false
    (μ : Measure ℂ) {r : ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) r)
    (hz0 : z ≠ 0) (t : ℝ) :
    ¬ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Ioo 0 ε₀, ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ),
        closure (cluster μ r z s) ⊆ cluster μ r z t + ball z ε := by
  obtain ⟨ε₁, hε₁, hfail⟩ := cluster_translated_ball_inclusion_fails μ hz hz0 t
  rintro ⟨ε₀, hε₀, hright⟩
  let ε := min ε₀ ε₁ / 2
  have hε : 0 < ε := half_pos (lt_min hε₀ hε₁)
  have hε₀' : ε < ε₀ := by dsimp [ε]; linarith [min_le_left ε₀ ε₁]
  have hε₁' : ε < ε₁ := by dsimp [ε]; linarith [min_le_right ε₀ ε₁]
  obtain ⟨δ, hδ, hsub⟩ := hright ε ⟨hε, hε₀'⟩
  exact hfail ε ⟨hε, hε₁'⟩ (hsub t ⟨le_rfl, le_add_of_nonneg_right hδ.le⟩)

end HarmonicBalls
