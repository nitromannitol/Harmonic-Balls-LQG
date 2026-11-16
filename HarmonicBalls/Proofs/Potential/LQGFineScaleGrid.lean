import LatticeProb.LQG.GMCDilatedGrid

/-! # Summability for fine-scale grids

A geometric estimate for grids whose scale index dominates their spatial index.
-/

open Filter

namespace HarmonicBalls

/-- A two-index geometric series remains summable when its second index is
restricted to lie above a sufficiently steep linear threshold. -/
theorem summable_fine_scale_grid {A t : ℝ} {m : ℕ} (hA : 0 ≤ A)
    (ht : 0 ≤ t) (ht1 : t < 1) (hdecay : A * t ^ m < 1) :
    Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then A ^ p.1 * (t ^ 2) ^ p.2 else 0 := by
  have hr : 0 ≤ A * t ^ m := mul_nonneg hA (pow_nonneg ht _)
  have hsum : Summable fun p : ℕ × ℕ => (A * t ^ m) ^ p.1 * t ^ p.2 :=
    (summable_geometric_of_lt_one hr hdecay).mul_of_nonneg
      (summable_geometric_of_lt_one ht ht1)
      (fun _ => pow_nonneg hr _) (fun _ => pow_nonneg ht _)
  refine Summable.of_norm_bounded hsum fun ⟨j, n⟩ => ?_
  by_cases h : m * j ≤ n
  · simp only [h, ↓reduceIte, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (pow_nonneg hA _) (pow_nonneg (sq_nonneg t) _))]
    have hpow : t ^ n ≤ t ^ (m * j) := pow_le_pow_of_le_one ht ht1.le h
    calc A ^ j * (t ^ 2) ^ n = A ^ j * (t ^ n * t ^ n) := by rw [pow_two, mul_pow]
      _ ≤ A ^ j * (t ^ (m * j) * t ^ n) := by gcongr
      _ = (A * t ^ m) ^ j * t ^ n := by rw [mul_pow, ← pow_mul]; ring
  · simp only [h, ↓reduceIte, norm_zero]
    exact mul_nonneg (pow_nonneg hr _) (pow_nonneg ht _)



/-- A sufficiently steep threshold yields summability for every nonnegative
spatial growth factor and every geometric decay factor below one. -/
theorem exists_summable_fine_scale_grid {A t : ℝ} (hA : 0 ≤ A)
    (ht : 0 ≤ t) (ht1 : t < 1) :
    ∃ m : ℕ, Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then A ^ p.1 * (t ^ 2) ^ p.2 else 0 := by
  have hlim : Tendsto (fun m : ℕ => A * t ^ m) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ht ht1).const_mul A
  obtain ⟨m, hm⟩ := (eventually_atTop.1 (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)))
  exact ⟨m, summable_fine_scale_grid hA ht ht1 (hm m le_rfl)⟩

/-- A summable bound on fine-scale increment probabilities yields simultaneous
control over all sufficiently fine grid points. -/
theorem ae_eventually_fine_scale_grid_abs_lt {Ω : Type*} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} {X : ℕ → ℕ → ℕ → Ω → ℝ}
    {N : ℕ → ℕ → ℕ} {b δ : ℕ → ℕ → ℝ} {m : ℕ}
    (hδ : ∀ j n, 0 < δ j n)
    (hX : ∀ j n i, m * j ≤ n → i ≤ N j n → MeasureTheory.Integrable (X j n i) P)
    (hb : ∀ j n i, m * j ≤ n → i ≤ N j n →
      ∫ ω, |X j n i ω| ∂P ≤ b j n)
    (hsum : Summable fun p : ℕ × ℕ =>
      if m * p.1 ≤ p.2 then ((N p.1 p.2 : ℝ) + 1) * (b p.1 p.2 / δ p.1 p.2) else 0) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, m * j ≤ n → ∀ i ≤ N j n, |X j n i ω| < δ j n := by
  let Y : ℕ → ℕ → ℕ → Ω → ℝ := fun j n i ω => if m * j ≤ n then X j n i ω else 0
  let c : ℕ → ℕ → ℝ := fun j n => if m * j ≤ n then b j n else 0
  have hY : ∀ j n i, i ≤ N j n → MeasureTheory.Integrable (Y j n i) P := by
    intro j n i hi
    by_cases h : m * j ≤ n
    · simpa [Y, h] using hX j n i h hi
    · simp [Y, h]
  have hYb : ∀ j n i, i ≤ N j n → ∫ ω, |Y j n i ω| ∂P ≤ c j n := by
    intro j n i hi
    by_cases h : m * j ≤ n
    · simpa [Y, c, h] using hb j n i h hi
    · simp [Y, c, h]
  have hsum' : Summable fun p : ℕ × ℕ =>
      ((N p.1 p.2 : ℝ) + 1) * (c p.1 p.2 / δ p.1 p.2) := by
    convert hsum using 1
    funext p
    by_cases h : m * p.1 ≤ p.2 <;> simp [c, h]
  have he := LatticeProb.LQG.GMCScaleGrid.ae_eventually_forall_forall_abs_lt
    hδ hY hYb hsum'
  filter_upwards [he] with ω hω
  filter_upwards [hω] with j hj n hn i hi
  simpa [Y, hn] using hj n i hi

end HarmonicBalls
