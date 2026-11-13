import HarmonicBalls.FirstPass.S11r.CurveLengthPieces

/-!
# Fine chains for an internal metric

Step 9 (i) of the local agreement route for the rooted identity (20). For an arbitrary `e : ℂ → ℂ → ℝ`, a path-connected
set `D ⊆ ℂ` and a finite constant `a`, the function `a · D_e(·, ·; D)` (`D_e(·, ·; D)` the internal metric of `e` on `D`)
has fine chains on `D`: for `x, y ∈ D` and `ε > 0` there is a compact `K ⊆ D` such that for every mesh `δ > 0` some chain
`x = m 0, m 1, …, m N = y` in `K` with steps of Euclidean size `< δ` has
`∑ a · D_e(m i, m (i+1); D) ≤ a · D_e(x, y; D) + ε`. The conclusion is the unfolded form of the fine chain property used
by the gluing step (`HasFineChains` of the library module on local agreement along chains).

Proof: take a path `P` in `D` from `x` to `y` whose `e`-length is within `ε / a` of the internal metric (any path when the
internal metric is infinite, from path-connectedness), `K = P([0, 1])`, and `m i = P(i / N)` with `N` large (uniform
continuity of `P` on `[0, 1]`). Each step is bounded by the `e`-length of `P` on `[i / N, (i + 1) / N]`
(`internalMetric_le_curveLength_of_subset`), and these lengths add up to at most the length of `P`
(`curveLength_add_le_general`). No metric axioms on `e` are used.

* `sum_curveLength_le_of_monotone`: superadditivity of the `e`-length along a monotone sequence of times;
* `exists_fine_chain_of_path`: chains along a given path, with the sum bounded by its `e`-length;
* `internalMetric_fineChains`: the fine chain property of `a · D_e(·, ·; D)`.
-/

namespace HarmonicBalls

open Set Finset Metric
open scoped ENNReal

/-- **Superadditivity along a monotone sequence of times.** For any `D : ℂ → ℂ → ℝ`, a curve `p` and monotone times
`t 0 ≤ t 1 ≤ …`, the `D`-lengths of `p` on the intervals `[t i, t (i + 1)]`, `i < n`, add up to at most the `D`-length of
`p` on `[t 0, t n]`. -/
theorem sum_curveLength_le_of_monotone (D : ℂ → ℂ → ℝ) (p : ℝ → ℂ) {t : ℕ → ℝ} (ht : Monotone t) (n : ℕ) :
    ∑ i ∈ range n, curveLength D p (t i) (t (i + 1)) ≤ curveLength D p (t 0) (t n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    calc ∑ i ∈ range n, curveLength D p (t i) (t (i + 1)) + curveLength D p (t n) (t (n + 1))
        ≤ curveLength D p (t 0) (t n) + curveLength D p (t n) (t (n + 1)) := by gcongr
      _ ≤ curveLength D p (t 0) (t (n + 1)) :=
          curveLength_add_le_general D p (ht (Nat.zero_le n)) (ht (Nat.le_succ n))

/-- The extension of a path in `D` stays in `D` at every time of `[0, 1]`. -/
theorem path_extend_mem_of_mem_Icc {D : Set ℂ} {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ D) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : P.extend τ ∈ D := by
  have h := hP ⟨τ, hτ⟩
  rw [← Path.extend_extends' P ⟨τ, hτ⟩] at h
  exact h

/-- **Fine chains along a path.** For a path `P` in `D` from `x` to `y` and a mesh `δ > 0` there is a chain
`x = m 0, …, m N = y` of points of `P([0, 1])` with steps `< δ` such that the internal metrics `D_e(m i, m (i+1); D)` add
up to at most the `e`-length of `P`. -/
theorem exists_fine_chain_of_path (e : ℂ → ℂ → ℝ) {D : Set ℂ} {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ D)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∃ m : ℕ → ℂ, m 0 = x ∧ m N = y ∧ (∀ i ≤ N, m i ∈ P.extend '' Icc 0 1) ∧
      (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
      ∑ i ∈ range N, internalMetric e D (m i) (m (i + 1)) ≤ pathLength e P := by
  have huc : UniformContinuousOn P.extend (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous P.continuous_extend.continuousOn
  obtain ⟨η, hη, hηd⟩ := Metric.uniformContinuousOn_iff.1 huc δ hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  let t : ℕ → ℝ := fun i => (i : ℝ) / ((n : ℝ) + 1)
  have ht : Monotone t := fun i j hij => by
    simp only [t]
    gcongr
  have htI : ∀ i ≤ n + 1, t i ∈ Icc (0 : ℝ) 1 := fun i hi =>
    ⟨div_nonneg (Nat.cast_nonneg i) hNpos.le, (div_le_one hNpos).2 (by exact_mod_cast hi)⟩
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t (n + 1) = 1 := by
    simp only [t]
    push_cast
    exact div_self hNpos.ne'
  refine ⟨n + 1, fun i => P.extend (t i), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ht0, Path.extend_zero]
  · simp only [ht1, Path.extend_one]
  · intro i hi
    exact ⟨t i, htI i hi, rfl⟩
  · intro i hi
    refine hηd _ (htI i hi.le) _ (htI (i + 1) hi) ?_
    have hdiff : t i - t (i + 1) = -(1 / ((n : ℝ) + 1)) := by
      simp only [t]
      push_cast
      ring
    rw [Real.dist_eq, hdiff, abs_neg, abs_of_pos (by positivity)]
    exact hn
  · calc ∑ i ∈ range (n + 1), internalMetric e D (P.extend (t i)) (P.extend (t (i + 1)))
        ≤ ∑ i ∈ range (n + 1), curveLength e P.extend (t i) (t (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_range] at hi
          refine internalMetric_le_curveLength_of_subset e P.continuous_extend (ht (Nat.le_succ i)) ?_
          intro τ hτ
          exact path_extend_mem_of_mem_Icc P hP
            ⟨(htI i hi.le).1.trans hτ.1, hτ.2.trans (htI (i + 1) (Nat.succ_le_of_lt hi)).2⟩
      _ ≤ curveLength e P.extend (t 0) (t (n + 1)) := sum_curveLength_le_of_monotone e P.extend ht (n + 1)
      _ = pathLength e P := by
          rw [ht0, ht1]
          rfl

/-- **Fine chains for an internal metric.** For any `e : ℂ → ℂ → ℝ`, a path-connected `D ⊆ ℂ` and a finite constant
`a`, the function `a · D_e(·, ·; D)` has fine chains on `D`: for `x, y ∈ D` and `ε > 0` there is a compact `K ⊆ D` such
that every mesh `δ > 0` admits a chain from `x` to `y` in `K` with steps `< δ` whose `a · D_e`-sum is at most
`a · D_e(x, y; D) + ε`. -/
theorem internalMetric_fineChains (e : ℂ → ℂ → ℝ) {D : Set ℂ} (hD : IsPathConnected D) {a : ℝ≥0∞}
    (ha : a ≠ ⊤) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ ε : ℝ≥0∞, 0 < ε → ∃ K ⊆ D, IsCompact K ∧ ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∃ m : ℕ → ℂ,
      m 0 = x ∧ m N = y ∧ (∀ i ≤ N, m i ∈ K) ∧ (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
        ∑ i ∈ Finset.range N, a * internalMetric e D (m i) (m (i + 1)) ≤
          a * internalMetric e D x y + ε := by
  intro x hx y hy ε hε
  have hP : ∃ P : Path x y, (∀ t, P t ∈ D) ∧ a * pathLength e P ≤ a * internalMetric e D x y + ε := by
    by_cases ha0 : a = 0
    · obtain J := hD.joinedIn x hx y hy
      exact ⟨J.somePath, J.somePath_mem, by simp [ha0]⟩
    by_cases hE : internalMetric e D x y = ⊤
    · obtain J := hD.joinedIn x hx y hy
      exact ⟨J.somePath, J.somePath_mem, by simp [hE, ENNReal.mul_top ha0]⟩
    have hε' : 0 < ε / a := ENNReal.div_pos_iff.2 ⟨hε.ne', ha⟩
    have hlt : (⨅ (P : Path x y) (_ : ∀ t, P t ∈ D), pathLength e P) <
        internalMetric e D x y + ε / a := ENNReal.lt_add_right hE hε'.ne'
    rw [iInf_lt_iff] at hlt
    obtain ⟨P, hlt⟩ := hlt
    rw [iInf_lt_iff] at hlt
    obtain ⟨hPD, hlt⟩ := hlt
    refine ⟨P, hPD, ?_⟩
    calc a * pathLength e P ≤ a * (internalMetric e D x y + ε / a) := by gcongr
      _ = a * internalMetric e D x y + ε := by rw [mul_add, ENNReal.mul_div_cancel ha0 ha]
  obtain ⟨P, hPD, hPl⟩ := hP
  refine ⟨P.extend '' Icc 0 1, ?_, isCompact_Icc.image P.continuous_extend, fun δ hδ => ?_⟩
  · rintro _ ⟨τ, hτ, rfl⟩
    exact path_extend_mem_of_mem_Icc P hPD hτ
  obtain ⟨N, m, h0, hN, hK, hd, hs⟩ := exists_fine_chain_of_path e P hPD hδ
  refine ⟨N, m, h0, hN, hK, hd, ?_⟩
  calc ∑ i ∈ Finset.range N, a * internalMetric e D (m i) (m (i + 1))
      = a * ∑ i ∈ Finset.range N, internalMetric e D (m i) (m (i + 1)) := by rw [Finset.mul_sum]
    _ ≤ a * pathLength e P := by gcongr
    _ ≤ a * internalMetric e D x y + ε := hPl

end HarmonicBalls
