import HarmonicBalls.Steps.Sec11.PathClearancePartition
import HarmonicBalls.Steps.Sec11.BoundaryClearanceChains
import HarmonicBalls.Steps.Sec11.PinchLocalContraction

/-! # Contraction through short paths

Internal distances can be compared using a metric comparison only on
sufficiently short edges of each individual path.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- If the new distance is at most a constant times the old distance on
sufficiently short edges of a path, then the new internal distance between
its endpoints is bounded by that constant times the old path length. -/
theorem IsEuclideanLengthMetric.internalMetric_le_const_mul_pathLength_of_short_edges
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {U : Set ℂ} (hU : IsOpen U) {c : ℝ} (hc : 0 < c)
    {x y : ℂ} (p : Path x y) (hp : ∀ t, p t ∈ U)
    (hshort : ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      D (p.extend s) (p.extend t) < r →
        E (p.extend s) (p.extend t) ≤ c * D (p.extend s) (p.extend t)) :
    internalMetric E U x y ≤ ENNReal.ofReal c * pathLength D p := by
  obtain ⟨r, hr, hcomp⟩ := hshort
  obtain ⟨δ, hδ, hclear⟩ := hE.path_uniform_boundary_clearance hU p hp
  let ε := min r (δ / (c + 1))
  have hε : 0 < ε := lt_min hr (div_pos hδ (by positivity))
  obtain ⟨n, u, hn, hu, humem, hu0, hun, hstep⟩ := hD.exists_short_path_partition p hε
  let v : ℕ → ℂ := fun i => p.extend (u i)
  have hcompstep : ∀ i < n, E (v i) (v (i + 1)) ≤ c * D (v i) (v (i + 1)) := by
    intro i hi
    apply hcomp (u i) (humem i) (u (i + 1)) (humem (i + 1))
    exact (hstep i hi).trans_le (min_le_left _ _)
  have hchain : ∀ i < n, ∃ d : ℝ, E (v i) (v (i + 1)) < d ∧
      ∀ z ∉ U, d ≤ E (v i) z := by
    intro i hi
    refine ⟨δ, ?_, ?_⟩
    · have hbound := (hstep i hi).trans_le (min_le_right r (δ / (c + 1)))
      have hc1 : 0 < c + 1 := by positivity
      have hb := (lt_div_iff₀ hc1).mp hbound
      have hn0 := hEnonneg (v i) (v (i + 1))
      have h := hcompstep i hi
      nlinarith
    · intro z hz
      have h := hclear ⟨u i, humem i⟩ z hz
      simpa only [v, Path.extend_apply _ (humem i)] using h
  have hv0 : v 0 = x := by simp only [v, hu0, p.extend_zero]
  have hvn : v n = y := by simp only [v, hun, p.extend_one]
  have hv0U : v 0 ∈ U := by rw [hv0]; exact p.source ▸ hp 0
  have hEsum := hE.internalMetric_le_sum_of_boundary_clearance hEnonneg hU v hv0U n hchain
  have hDsum : (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) ≤
      pathLength D p := by
    have hlen := le_iSup (fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc 0 1} =>
      ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p.extend (q.2.1 (i + 1)))
        (p.extend (q.2.1 i)))) ⟨n, ⟨u, hu, humem⟩⟩
    change _ ≤ pathLength D p at hlen
    apply le_trans _ hlen
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg ENNReal.ofReal (hD.symm _ _)
  calc
    internalMetric E U x y = internalMetric E U (v 0) (v n) := by rw [hv0, hvn]
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (E (v i) (v (i + 1))) := by
      simpa only using hEsum
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal c * ENNReal.ofReal (D (v i) (v (i + 1))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← ENNReal.ofReal_mul hc.le]
      exact ENNReal.ofReal_le_ofReal (hcompstep i (Finset.mem_range.mp hi))
    _ = ENNReal.ofReal c * ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) := by
      rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal c * pathLength D p := by gcongr

private theorem mul_iInf_of_pos_finite {ι : Sort*} (a : ℝ≥0∞)
    (ha : 0 < a) (hat : a ≠ ∞) (F : ι → ℝ≥0∞) :
    a * (⨅ i, F i) = ⨅ i, a * F i := by
  classical
  by_cases h : Nonempty ι
  · let : Nonempty ι := h
    exact ENNReal.mul_iInf (fun h _ => (hat h).elim)
  · let : IsEmpty ι := not_nonempty_iff.mp h
    simp only [iInf_of_empty, ENNReal.mul_top (ne_of_gt ha)]

/-- If every path has sufficiently short edges on which the ambient distance
is contracted, then the internal distance is contracted. The edge threshold
may depend on the path. -/
theorem IsEuclideanLengthMetric.internalMetric_le_const_mul_of_short_edges
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {U : Set ℂ} (hU : IsOpen U) {c : ℝ} (hc : 0 < c)
    (hshort : ∀ {x y : ℂ} (p : Path x y), (∀ t, p t ∈ U) →
      ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        D (p.extend s) (p.extend t) < r →
          E (p.extend s) (p.extend t) ≤ c * D (p.extend s) (p.extend t))
    (x y : ℂ) : internalMetric E U x y ≤ ENNReal.ofReal c * internalMetric D U x y := by
  let a : ℝ≥0∞ := ENNReal.ofReal c
  have ha : 0 < a := ENNReal.ofReal_pos.mpr hc
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  change internalMetric E U x y ≤ a * internalMetric D U x y
  calc
    internalMetric E U x y ≤ ⨅ (p : Path x y) (_ : ∀ t, p t ∈ U), a * pathLength D p := by
      apply le_iInf
      intro p
      apply le_iInf
      intro hp
      exact hD.internalMetric_le_const_mul_pathLength_of_short_edges hE hEnonneg hU hc p hp
        (hshort p hp)
    _ = a * internalMetric D U x y := by
      unfold internalMetric
      rw [mul_iInf_of_pos_finite a ha hat]
      apply iInf_congr
      intro p
      exact (mul_iInf_of_pos_finite a ha hat _).symm

/-- Pathwise short-edge contraction yields contraction of the pinch internal
diameter, without an all-pairs ambient-distance hypothesis. -/
theorem IsEuclideanLengthMetric.internalDiam_le_const_mul_of_short_edges
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {c δ : ℝ} (hc : 0 < c) (A : Set ℂ)
    (hshort : ∀ {x y : ℂ} (p : Path x y), (∀ t, p t ∈ thickening δ A) →
      ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        D (p.extend s) (p.extend t) < r →
          E (p.extend s) (p.extend t) ≤ c * D (p.extend s) (p.extend t)) :
    internalDiam E δ A ≤ ENNReal.ofReal c * internalDiam D δ A := by
  unfold internalDiam
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro x
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro hx
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro y
  rw [ENNReal.mul_iSup]
  apply iSup_mono
  intro hy
  exact hD.internalMetric_le_const_mul_of_short_edges hE hEnonneg isOpen_thickening hc hshort x y

/-- Short-edge contraction and a nondecreasing sphere gap imply strict E3
when the original diameter has the required strict margin. -/
theorem IsEuclideanLengthMetric.pinchThirdEvent_of_short_edges
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {c δ : ℝ} (hc : 0 < c) (V W : Set ℂ)
    (hshort : ∀ {x y : ℂ} (p : Path x y),
      (∀ t, p t ∈ thickening δ (thickening (3 * δ) W \ V)) →
      ∃ r : ℝ, 0 < r ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        D (p.extend s) (p.extend t) < r →
          E (p.extend s) (p.extend t) ≤ c * D (p.extend s) (p.extend t))
    (hgap : ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ))) ≤
      ENNReal.ofReal (setDist E (sphere 0 (2 * δ)) (sphere 0 (3 * δ))))
    (hstrict : ENNReal.ofReal c * internalDiam D δ (thickening (3 * δ) W \ V) <
      ENNReal.ofReal (setDist D (sphere 0 (2 * δ)) (sphere 0 (3 * δ)))) :
    pinchThirdEvent E V W δ := by
  exact (hD.internalDiam_le_const_mul_of_short_edges hE hEnonneg hc _ hshort).trans_lt
    (hstrict.trans_le hgap)

end HarmonicBalls
