import HarmonicBalls.Draft.Section11

/-!
# Nearly minimizing paths

The strict pinch inequalities can be combined with nearly minimizing paths,
avoiding an assumption that a length metric has geodesics.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- A length metric admits paths whose length is arbitrarily close to the
distance between their endpoints. -/
theorem IsEuclideanLengthMetric.exists_pathLength_lt
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (w z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Path w z, pathLength D p < ENNReal.ofReal (D w z + ε) := by
  have hlt : ENNReal.ofReal (D w z) < ENNReal.ofReal (D w z + ε) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnonneg w z)).2 (by linarith)
  rw [hD.ofReal_eq_internalMetric] at hlt
  obtain ⟨p, hp⟩ := iInf_lt_iff.mp hlt
  obtain ⟨_, hp⟩ := iInf_lt_iff.mp hp
  exact ⟨p, hp⟩

/-- A path's length dominates the sum of distances through any point on it. -/
theorem IsEuclideanLengthMetric.ofReal_two_segment_le_pathLength
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {w z : ℂ} (p : Path w z)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (D w (p.extend t) + D (p.extend t) z) ≤ pathLength D p := by
  let u : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then t else 1
  have hu : Monotone u := by
    apply monotone_nat_of_le_succ
    intro n
    rcases n with _ | _ | n
    · simpa [u] using ht.1
    · simpa [u] using ht.2
    · simp [u]
  have humem : ∀ n, u n ∈ Icc (0 : ℝ) 1 := by
    intro n
    rcases n with _ | _ | n
    · simp [u]
    · simpa [u] using ht
    · simp [u]
  have hle := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p.extend (q.2.1 (i + 1)))
      (p.extend (q.2.1 i)))) ⟨2, ⟨u, hu, humem⟩⟩
  change _ ≤ pathLength D p at hle
  norm_num [u, Finset.sum_range_succ, p.extend_zero, p.extend_one] at hle
  rw [ENNReal.ofReal_add (hnonneg w (p.extend t)) (hnonneg (p.extend t) z)]
  simpa only [hD.symm (p.extend t) w, hD.symm z (p.extend t)] using hle

end HarmonicBalls
