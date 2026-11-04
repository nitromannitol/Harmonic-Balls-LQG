import HarmonicBalls.Proofs.Sec6.PlanarHarnackReverse

/-! # Harmonic comparison across intersecting discs -/

namespace HarmonicBalls.Section6

open Metric Set InnerProductSpace

/-- A chain of intersecting discs compares their centre values with factor
`16` per overlap. -/
theorem harmonic_le_of_intersecting_disc_chain {U : Set ℂ} {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f U) (hnonneg : ∀ z ∈ U, 0 ≤ f z)
    {δ : ℝ} (hδ : 0 < δ) (p : ℕ → ℂ) (n : ℕ)
    (hdisc : ∀ i ≤ n, closedBall (p i) (2 * δ) ⊆ U)
    (hstep : ∀ i < n, (ball (p i) δ ∩ ball (p (i + 1)) δ).Nonempty) :
    f (p n) ≤ (16 : ℝ) ^ n * f (p 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn := ih (fun i hi => hdisc i (le_trans hi (Nat.le_succ n)))
      (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    obtain ⟨w, hw1, hw2⟩ := hstep n (Nat.lt_succ_self n)
    have hd1 := hdisc n (Nat.le_succ n)
    have hd2 := hdisc (n + 1) (le_refl _)
    have hw1' : w ∈ closedBall (p n) ((2 * δ) / 2) := by
      apply mem_closedBall.mpr
      have := mem_ball.mp hw1
      linarith
    have hw2' : w ∈ closedBall (p (n + 1)) ((2 * δ) / 2) := by
      apply mem_closedBall.mpr
      have := mem_ball.mp hw2
      linarith
    have h1 := harmonic_le_four_mul_center (by positivity : 0 < 2 * δ) (hf.mono hd1)
      (fun z hz => hnonneg z (hd1 (sphere_subset_closedBall hz))) hw1'
    have h2 := harmonic_center_le_four_mul (by positivity : 0 < 2 * δ) (hf.mono hd2)
      (fun z hz => hnonneg z (hd2 (sphere_subset_closedBall hz))) hw2'
    have hlocal : f (p (n + 1)) ≤ 16 * f (p n) := by linarith
    calc
      f (p (n + 1)) ≤ 16 * f (p n) := hlocal
      _ ≤ 16 * ((16 : ℝ) ^ n * f (p 0)) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = (16 : ℝ) ^ (n + 1) * f (p 0) := by rw [pow_succ]; ring

/-- The same comparison holds for points in the first and last discs. -/
theorem harmonic_le_of_intersecting_disc_chain_endpoints {U : Set ℂ} {f : ℂ → ℝ}
    (hf : HarmonicOnNhd f U) (hnonneg : ∀ z ∈ U, 0 ≤ f z)
    {δ : ℝ} (hδ : 0 < δ) (p : ℕ → ℂ) (n : ℕ)
    (hdisc : ∀ i ≤ n, closedBall (p i) (2 * δ) ⊆ U)
    (hstep : ∀ i < n, (ball (p i) δ ∩ ball (p (i + 1)) δ).Nonempty)
    {x y : ℂ} (hx : x ∈ ball (p n) δ) (hy : y ∈ ball (p 0) δ) :
    f x ≤ (16 : ℝ) ^ (n + 1) * f y := by
  have hchain := harmonic_le_of_intersecting_disc_chain hf hnonneg hδ p n hdisc hstep
  have hx' : x ∈ closedBall (p n) ((2 * δ) / 2) := by
    apply mem_closedBall.mpr
    have := mem_ball.mp hx
    linarith
  have hy' : y ∈ closedBall (p 0) ((2 * δ) / 2) := by
    apply mem_closedBall.mpr
    have := mem_ball.mp hy
    linarith
  have hdN := hdisc n (le_refl _)
  have hd0 := hdisc 0 (Nat.zero_le n)
  have h1 := harmonic_le_four_mul_center (by positivity : 0 < 2 * δ) (hf.mono hdN)
    (fun z hz => hnonneg z (hdN (sphere_subset_closedBall hz))) hx'
  have h2 := harmonic_center_le_four_mul (by positivity : 0 < 2 * δ) (hf.mono hd0)
    (fun z hz => hnonneg z (hd0 (sphere_subset_closedBall hz))) hy'
  have hpow : 0 ≤ (16 : ℝ) ^ n := by positivity
  calc
    f x ≤ 4 * f (p n) := h1
    _ ≤ 4 * ((16 : ℝ) ^ n * f (p 0)) := mul_le_mul_of_nonneg_left hchain (by norm_num)
    _ ≤ 4 * ((16 : ℝ) ^ n * (4 * f y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hpow) (by norm_num)
    _ = (16 : ℝ) ^ (n + 1) * f y := by rw [pow_succ]; ring

end HarmonicBalls.Section6
