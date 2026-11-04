import HarmonicBalls.Steps.Sec11.CompactBoundaryClearance
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-! # Partitions of a path with boundary clearance -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- Along a fixed path, Euclidean-close times have uniformly close images in
any metric inducing the Euclidean topology. -/
theorem IsEuclideanLengthMetric.path_uniform_distance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y : ℂ} (p : Path x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist s t < δ → D (p.extend s) (p.extend t) < ε := by
  let f : ℝ × ℝ → ℝ := fun st => D (p.extend st.1) (p.extend st.2)
  have hf : Continuous f := hD.continuous_pair.comp
    ((p.continuous_extend.comp continuous_fst).prodMk (p.continuous_extend.comp continuous_snd))
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, hbound⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst
  have hdist : dist (s, t) (s, s) < δ := by
    simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm] using hst
  have h := hbound (s, t) ⟨hs, ht⟩ (s, s) ⟨hs, hs⟩ hdist
  simp only [f, hD.self_eq_zero, Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-- A path has a finite monotone partition whose successive points are
arbitrarily close in the ambient length metric. -/
theorem IsEuclideanLengthMetric.exists_short_path_partition
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {x y : ℂ} (p : Path x y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (u : ℕ → ℝ), Monotone u ∧ (∀ i, u i ∈ Icc (0 : ℝ) 1) ∧
      u 0 = 0 ∧ u n = 1 ∧ ∀ i < n, D (p.extend (u i)) (p.extend (u (i + 1))) < ε := by
  obtain ⟨δ, hδ, hclose⟩ := hD.path_uniform_distance p hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  let n : ℕ := m + 1
  have hn : (0 : ℝ) < n := by dsimp [n]; positivity
  have hstep : 1 / (n : ℝ) < δ := by simpa only [n, Nat.cast_add, Nat.cast_one] using hm
  let u : ℕ → ℝ := fun i => min ((i : ℝ) / (n : ℝ)) 1
  have hu : Monotone u := by
    intro i j hij
    apply min_le_min_right
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) hn.le
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := by
    intro i
    exact ⟨le_min (div_nonneg (Nat.cast_nonneg _) hn.le) (by norm_num), min_le_right _ _⟩
  have hformula (i : ℕ) (hi : i ≤ n) : u i = (i : ℝ) / n := by
    apply min_eq_left
    apply (div_le_one hn).2
    exact_mod_cast hi
  refine ⟨n, u, hu, humem, ?_, ?_, ?_⟩
  · simp only [u, Nat.cast_zero, zero_div, min_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
  · rw [hformula n (le_refl _), div_self (ne_of_gt hn)]
  · intro i hi
    have hi' : i + 1 ≤ n := Nat.succ_le_of_lt hi
    have hdist : dist (u i) (u (i + 1)) = 1 / (n : ℝ) := by
      rw [hformula i hi.le, hformula (i + 1) hi', Real.dist_eq]
      have hsub : (i : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n = -(1 / (n : ℝ)) := by
        push_cast
        ring
      rw [hsub, abs_neg, abs_of_nonneg (by positivity)]
    exact hclose (u i) (humem i) (u (i + 1)) (humem (i + 1)) (hdist ▸ hstep)

/-- Every path inside an open set yields a finite chain of clearance edges
whose cost is at most the path length. -/
theorem IsEuclideanLengthMetric.exists_clearance_chain_of_path
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} (hU : IsOpen U) {x y : ℂ} (p : Path x y) (hp : ∀ t, p t ∈ U) :
    ∃ (n : ℕ) (v : ℕ → ℂ), v 0 = x ∧ v n = y ∧
      (∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
        ∀ z ∉ U, δ ≤ D (v i) z) ∧
      (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) ≤ pathLength D p := by
  obtain ⟨δ, hδ, hclear⟩ := hD.path_uniform_boundary_clearance hU p hp
  obtain ⟨n, u, hu, humem, hu0, hun, hshort⟩ := hD.exists_short_path_partition p hδ
  let v : ℕ → ℂ := fun i => p.extend (u i)
  refine ⟨n, v, ?_, ?_, ?_, ?_⟩
  · simp only [v, hu0, p.extend_zero]
  · simp only [v, hun, p.extend_one]
  · intro i hi
    refine ⟨δ, hshort i hi, ?_⟩
    intro z hz
    have h := hclear ⟨u i, humem i⟩ z hz
    simpa only [v, Path.extend_apply _ (humem i)] using h
  · have hlen := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
      ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p.extend (q.2.1 (i + 1)))
        (p.extend (q.2.1 i)))) ⟨n, ⟨u, hu, humem⟩⟩
    change _ ≤ pathLength D p at hlen
    apply le_trans _ hlen
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg ENNReal.ofReal (hD.symm _ _)

end HarmonicBalls
