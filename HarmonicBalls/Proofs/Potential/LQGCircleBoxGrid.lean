import HarmonicBalls.Proofs.Potential.LQGFineScaleGrid

/-! # Finite grids in the unit square

Coordinate projection produces finite square grids with dyadic mesh.
-/

noncomputable section
open Metric Set LatticeProb.LQG

namespace HarmonicBalls

private def clampUnit (x : ℝ) : ℝ := max 0 (min 1 x)

private theorem abs_sub_clampUnit_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : ℝ) :
    |u - clampUnit x| ≤ |u - x| := by
  unfold clampUnit
  rcases le_total x 0 with hx | hx
  · rw [min_eq_right (by linarith), max_eq_left hx]
    rw [sub_zero, abs_of_nonneg hu0, abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total x 1 with hx1 | hx1
    · rw [min_eq_right hx1, max_eq_right hx]
    · rw [min_eq_left hx1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith

private def clampSquare (z : ℂ) : ℂ := ⟨clampUnit z.re, clampUnit z.im⟩

/-- The unit square has finite dyadic grids with coordinatewise mesh and
quadratic cardinality growth. -/
theorem exists_unit_square_dyadic_grids :
    ∃ S : ℕ → Finset ℂ, ∀ k,
      ((S k).card : ℝ) ≤ 676 * (4 : ℝ) ^ k ∧
      (∀ x ∈ S k, 0 ≤ x.re ∧ x.re ≤ 1 ∧ 0 ≤ x.im ∧ x.im ≤ 1) ∧
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ z.im → z.im ≤ 1 →
        ∃ x ∈ S k, |z.re - x.re| < dyadicScale (k + 1) ∧
          |z.im - x.im| < dyadicScale (k + 1) := by
  classical
  obtain ⟨T, hT⟩ := exists_dyadic_ball_grids 3 (by norm_num)
  refine ⟨fun k => (T (k + 1)).image clampSquare, fun k => ⟨?_, ?_, ?_⟩⟩
  · have hc : (((T (k + 1)).image clampSquare).card : ℝ) ≤ (T (k + 1)).card := by
      exact_mod_cast Finset.card_image_le
    calc
      _ ≤ ((T (k + 1)).card : ℝ) := hc
      _ ≤ (4 * 3 + 1) ^ 2 * (4 : ℝ) ^ (k + 1) := (hT (k + 1)).1
      _ = 676 * (4 : ℝ) ^ k := by rw [pow_succ]; ring
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
    simp only [clampSquare, clampUnit]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _),
      le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · intro z hz0 hz1 hw0 hw1
    have hz : z ∈ ball (0 : ℂ) 3 := by
      rw [mem_ball, dist_zero_right]
      have h := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_nonneg hz0, abs_of_nonneg hw0] at h
      linarith
    obtain ⟨x, hx, hdist⟩ := (hT (k + 1)).2 z hz
    refine ⟨clampSquare x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_, ?_⟩
    · have h := Complex.abs_re_le_norm (z - x)
      rw [Complex.sub_re, ← dist_eq_norm] at h
      exact (abs_sub_clampUnit_le hz0 hz1 x.re).trans_lt (h.trans_lt hdist)
    · have h := Complex.abs_im_le_norm (z - x)
      rw [Complex.sub_im, ← dist_eq_norm] at h
      exact (abs_sub_clampUnit_le hw0 hw1 x.im).trans_lt (h.trans_lt hdist)

end HarmonicBalls
