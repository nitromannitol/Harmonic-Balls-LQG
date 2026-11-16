import HarmonicBalls.Proofs.Potential.LQGFineScaleGrid
import LatticeProb.Gauss.CircleAverageModulusUniform

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

/-- Copies of a unit-square grid placed in finitely many rescaled boxes. -/
def circleBoxGrid (ε : ℝ) (L : ℕ) (S : Finset ℂ) : Finset ℂ :=
  ((Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L) ×ˢ S).image
    (fun p => LatticeProb.Gauss.circleBoxCentre ε p.1.1 p.1.2 + (ε : ℂ) * p.2)

/-- The number of grid points is bounded by the number of boxes times the
number of points in the unit-square grid. -/
theorem circleBoxGrid_card_le (ε : ℝ) (L : ℕ) (S : Finset ℂ) :
    (circleBoxGrid ε L S).card ≤ (2 * L + 1) ^ 2 * S.card := by
  classical
  have hcard : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  unfold circleBoxGrid
  calc
    _ ≤ ((Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L) ×ˢ S).card :=
      Finset.card_image_le
    _ = (2 * L + 1) ^ 2 * S.card := by
      rw [Finset.card_product, Finset.card_product, Int.card_Icc, hcard]
      ring

/-- A square-grid point in any listed box is in the corresponding global grid. -/
theorem mem_circleBoxGrid {ε : ℝ} {L : ℕ} {S : Finset ℂ}
    {m n : ℤ} (hm : m ∈ Finset.Icc (-(L : ℤ)) L)
    (hn : n ∈ Finset.Icc (-(L : ℤ)) L) {u : ℂ} (hu : u ∈ S) :
    LatticeProb.Gauss.circleBoxCentre ε m n + (ε : ℂ) * u ∈ circleBoxGrid ε L S := by
  classical
  exact Finset.mem_image.mpr ⟨((m, n), u),
    Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨hm, hn⟩, hu⟩, rfl⟩

/-- A bounded family of dyadic boxes has a common spatial grid with at most
exponential cardinality growth and coordinatewise coverage inside each box. -/
theorem exists_compact_circle_box_grids (R : ℝ) :
    ∃ S : ℕ → Finset ℂ, ∀ k,
      ((S k).card : ℝ) ≤ (676 * (2 * max R 0 + 3) ^ 2) * (16 : ℝ) ^ k ∧
      ∀ m n : ℤ,
        m ∈ Finset.Icc (-(⌈max R 0 * 2 ^ k⌉₊ : ℤ)) ⌈max R 0 * 2 ^ k⌉₊ →
        n ∈ Finset.Icc (-(⌈max R 0 * 2 ^ k⌉₊ : ℤ)) ⌈max R 0 * 2 ^ k⌉₊ →
        ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ z.im → z.im ≤ 1 →
        ∃ u : ℂ, 0 ≤ u.re ∧ u.re ≤ 1 ∧ 0 ≤ u.im ∧ u.im ≤ 1 ∧
          |z.re - u.re| < dyadicScale (k + 1) ∧
          |z.im - u.im| < dyadicScale (k + 1) ∧
          LatticeProb.Gauss.circleBoxCentre (dyadicScale k) m n +
            (dyadicScale k : ℂ) * u ∈ S k := by
  classical
  obtain ⟨U, hU⟩ := exists_unit_square_dyadic_grids
  let L : ℕ → ℕ := fun k => ⌈max R 0 * 2 ^ k⌉₊
  refine ⟨fun k => circleBoxGrid (dyadicScale k) (L k) (U k), fun k => ⟨?_, ?_⟩⟩
  · have hR : 0 ≤ max R 0 := le_max_right _ _
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hL : 2 * (L k : ℝ) + 1 ≤ (2 * max R 0 + 3) * 2 ^ k := by
      have hc := Nat.ceil_lt_add_one (show 0 ≤ max R 0 * 2 ^ k by positivity)
      change (⌈max R 0 * 2 ^ k⌉₊ : ℝ) < max R 0 * 2 ^ k + 1 at hc
      dsimp only [L]
      nlinarith
    have hL2 : (2 * (L k : ℝ) + 1) ^ 2 ≤ (2 * max R 0 + 3) ^ 2 * (4 : ℝ) ^ k := by
      calc
        _ ≤ ((2 * max R 0 + 3) * 2 ^ k) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hL 2
        _ = (2 * max R 0 + 3) ^ 2 * (4 : ℝ) ^ k := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
          norm_num
    have hc : ((circleBoxGrid (dyadicScale k) (L k) (U k)).card : ℝ) ≤
        (2 * (L k : ℝ) + 1) ^ 2 * ((U k).card : ℝ) := by
      exact_mod_cast circleBoxGrid_card_le (dyadicScale k) (L k) (U k)
    calc
      _ ≤ (2 * (L k : ℝ) + 1) ^ 2 * ((U k).card : ℝ) := hc
      _ ≤ ((2 * max R 0 + 3) ^ 2 * (4 : ℝ) ^ k) * (676 * (4 : ℝ) ^ k) :=
        mul_le_mul hL2 (hU k).1 (by positivity) (by positivity)
      _ = (676 * (2 * max R 0 + 3) ^ 2) * (16 : ℝ) ^ k := by
        rw [show (16 : ℝ) = 4 * 4 by norm_num, mul_pow]
        ring
  · intro m n hm hn z hz0 hz1 hw0 hw1
    obtain ⟨u, hu, hre, him⟩ := (hU k).2.2 z hz0 hz1 hw0 hw1
    obtain ⟨hu0, hu1, hv0, hv1⟩ := (hU k).2.1 u hu
    exact ⟨u, hu0, hu1, hv0, hv1, hre, him, mem_circleBoxGrid hm hn hu⟩

end HarmonicBalls
