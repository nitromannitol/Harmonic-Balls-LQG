import HarmonicBalls.Defs.LQGMetric

/-!
# First pass, Section 11: positivity of set distances for a Euclidean length metric (fp-S11h, owner n2)

Deterministic input for step B of Lemma 11.17 (corrected paper lines 3726-3756): the quantity `a₂ = D(∂B_{2δ}, ∂B_{3δ})`
of the third event `pinchThirdEvent` is positive. The metric is any `IsEuclideanLengthMetric D` (Fact 2.2 I,
`Defs/LQGMetric.lean:81`), so the statement holds for every realization of the field. The proof uses only the metric
axioms (symmetry, triangle inequality, separation, the Euclidean topology through `isOpen_iff`) and compactness.
-/

open Set Metric Filter Topology

namespace HarmonicBalls

variable {D : ℂ → ℂ → ℝ}

/-- For a Euclidean length metric, the sublevel set `{w | D(w, z) < r}` is Euclidean open. -/
theorem isOpen_setOf_dist_lt_of_isEuclideanLengthMetric (hD : IsEuclideanLengthMetric D) (z : ℂ) (r : ℝ) :
    IsOpen {w : ℂ | D w z < r} := by
  rw [hD.isOpen_iff]
  intro w hw
  have hw' : D w z < r := hw
  refine ⟨r - D w z, sub_pos.2 hw', ?_⟩
  intro v hv
  show D v z < r
  have h1 := hD.triangle v w z
  have h2 := hD.symm v w
  linarith

/-- The metric `(x, y) ↦ D(x, y)` is continuous on `ℂ × ℂ` for a Euclidean length metric. -/
theorem continuous_uncurry_of_isEuclideanLengthMetric (hD : IsEuclideanLengthMetric D) :
    Continuous (fun p : ℂ × ℂ => D p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x0, y0⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by positivity
  have h1 : {x : ℂ | D x x0 < ε / 2} ∈ 𝓝 x0 := by
    refine (isOpen_setOf_dist_lt_of_isEuclideanLengthMetric hD x0 (ε / 2)).mem_nhds ?_
    show D x0 x0 < ε / 2
    rw [hD.self_eq_zero]
    exact hε2
  have h2 : {y : ℂ | D y y0 < ε / 2} ∈ 𝓝 y0 := by
    refine (isOpen_setOf_dist_lt_of_isEuclideanLengthMetric hD y0 (ε / 2)).mem_nhds ?_
    show D y0 y0 < ε / 2
    rw [hD.self_eq_zero]
    exact hε2
  filter_upwards [prod_mem_nhds h1 h2] with p hp
  obtain ⟨x, y⟩ := p
  have hx : D x x0 < ε / 2 := hp.1
  have hy : D y y0 < ε / 2 := hp.2
  have ha := hD.triangle x x0 y
  have hb := hD.triangle x0 y0 y
  have hc := hD.triangle x0 x y0
  have hd := hD.triangle x y y0
  have s1 := hD.symm x0 x
  have s2 := hD.symm y0 y
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- For nonempty disjoint compact sets `A, B` in the plane and a Euclidean length metric `D`, the set distance
`setDist D A B` is positive: it is attained at a pair `(x₀, y₀) ∈ A × B` with `D(x₀, y₀) > 0`. -/
theorem setDist_pos_of_isEuclideanLengthMetric (hD : IsEuclideanLengthMetric D) {A B : Set ℂ}
    (hA : IsCompact A) (hB : IsCompact B) (hAne : A.Nonempty) (hBne : B.Nonempty) (hAB : Disjoint A B) :
    0 < setDist D A B := by
  have hcont := continuous_uncurry_of_isEuclideanLengthMetric hD
  have himg : image2 D A B = (fun p : ℂ × ℂ => D p.1 p.2) '' (A ×ˢ B) := by
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hK : IsCompact (image2 D A B) := by
    rw [himg]
    exact (hA.prod hB).image hcont
  have hne : (image2 D A B).Nonempty := hAne.image2 hBne
  obtain ⟨x0, hx0, y0, hy0, hval⟩ := mem_image2.1 (hK.sInf_mem hne)
  have hnn : 0 ≤ D x0 y0 := by
    have h1 := hD.triangle x0 y0 x0
    have h2 := hD.symm y0 x0
    have h3 := hD.self_eq_zero x0
    linarith
  rw [setDist, ← hval]
  refine lt_of_le_of_ne hnn ?_
  intro h0
  have hxy : x0 = y0 := hD.eq_of_eq_zero x0 y0 h0.symm
  exact Set.disjoint_left.1 hAB hx0 (by rw [hxy]; exact hy0)

/-- For `0 < r < s`, the distance between the Euclidean circles `∂B_r` and `∂B_s` is positive for a Euclidean length
metric. This is the quantity `D(∂B_{2δ}, ∂B_{3δ})` of `pinchThirdEvent` (`Draft/Section11.lean`). -/
theorem setDist_sphere_pos_of_isEuclideanLengthMetric (hD : IsEuclideanLengthMetric D) {r s : ℝ} (hr : 0 < r)
    (hrs : r < s) : 0 < setDist D (sphere (0 : ℂ) r) (sphere (0 : ℂ) s) := by
  refine setDist_pos_of_isEuclideanLengthMetric hD (isCompact_sphere _ _) (isCompact_sphere _ _) ?_ ?_ ?_
  · exact ⟨(r : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hr.le]⟩
  · exact ⟨(s : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (hr.trans hrs).le]⟩
  · refine Set.disjoint_left.2 fun x hx hy => ?_
    exact (ne_of_lt hrs) ((mem_sphere_zero_iff_norm.1 hx).symm.trans (mem_sphere_zero_iff_norm.1 hy))

#print axioms setDist_sphere_pos_of_isEuclideanLengthMetric

end HarmonicBalls
