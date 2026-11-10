import HarmonicBalls.Defs.LQGMetric

/-!
# Sign and diagonal of a decoded length metric (fp-S11r-rooted-local-ident-c, ruling (c))

The frozen local clauses are stated in `ENNReal`: `ENNReal.ofReal (m x y) = ENNReal.ofReal b * ENNReal.ofReal (D x y)`.
`ENNReal.ofReal` forgets the sign of `m`. Here `D` is a Euclidean length metric, `m` is continuous on an open window, and
the `ENNReal` identity holds on a dense family of pairs. Then `m = b · D` as real numbers on the whole window (Armitage-Gardiner:
off the diagonal `D > 0` forces `m > 0`; on the diagonal continuity forces `m = 0`).

* `eq_const_mul_of_ofReal_eq`: the pointwise version (copy of `FirstPassS11at.eq_const_mul_of_ofReal_eq`, which lies
  downstream of this file and cannot be imported here; the two copies are equal in statement).
* `eq_const_mul_of_dense_family`: the `ENNReal` identity on a dense countable family implies it on the window
  (closure argument, `Set.EqOn.of_subset_closure`), then the pointwise version applies.
-/

open Filter Topology

namespace HarmonicBalls

/-- Sign and diagonal fixing for a decoded length metric. If `D` is a Euclidean length metric, `m` is continuous in its
second variable on the open set `O`, and `m` equals `b · D` in `ENNReal` on `O × O`, then `m = b · D` on `O × O` as real
numbers. -/
theorem eq_const_mul_of_ofReal_eq {D m : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {O : Set ℂ} (hO : IsOpen O)
    {b : ℝ} (hb : 0 < b) (hcont : ∀ x ∈ O, ContinuousAt (fun y => m x y) x)
    (hid : ∀ x ∈ O, ∀ y ∈ O, ENNReal.ofReal (m x y) = ENNReal.ofReal b * ENNReal.ofReal (D x y)) :
    ∀ x ∈ O, ∀ y ∈ O, m x y = b * D x y := by
  have hnonneg : ∀ x y, 0 ≤ D x y := fun x y => by
    have h1 := hD.triangle x y x
    have h2 := hD.symm y x
    have h3 := hD.self_eq_zero x
    linarith
  have hoff : ∀ x ∈ O, ∀ y ∈ O, x ≠ y → m x y = b * D x y := by
    intro x hx y hy hxy
    have hpos : 0 < D x y :=
      lt_of_le_of_ne (hnonneg x y) (fun h => hxy (hD.eq_of_eq_zero x y h.symm))
    have h1 : ENNReal.ofReal (m x y) = ENNReal.ofReal (b * D x y) := by
      rw [hid x hx y hy, ENNReal.ofReal_mul hb.le]
    have hmpos : 0 < m x y :=
      ENNReal.ofReal_pos.1 (by rw [h1]; exact ENNReal.ofReal_pos.2 (mul_pos hb hpos))
    exact (ENNReal.ofReal_eq_ofReal_iff hmpos.le (mul_nonneg hb.le (hnonneg x y))).1 h1
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    have h0 : ENNReal.ofReal (m x x) = 0 := by
      rw [hid x hx x hx, hD.self_eq_zero x, ENNReal.ofReal_zero, mul_zero]
    have hle : m x x ≤ 0 := ENNReal.ofReal_eq_zero.1 h0
    have hge : 0 ≤ m x x := by
      have ht : Tendsto (fun y => m x y) (𝓝[≠] x) (𝓝 (m x x)) :=
        (hcont x hx).mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto ht ?_
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hO.mem_nhds hx),
        (eventually_mem_nhdsWithin : ∀ᶠ y in 𝓝[≠] x, y ∈ ({x}ᶜ : Set ℂ))] with y hyO hyne
      show 0 ≤ m x y
      have hne : x ≠ y := fun h => hyne (Set.mem_singleton_iff.2 h.symm)
      rw [hoff x hx y hyO hne]
      exact mul_nonneg hb.le (hnonneg x y)
    rw [le_antisymm hle hge, hD.self_eq_zero x, mul_zero]
  · exact hoff x hx y hy hxy

/-- Dense-family version of the sign fixing. Let `X : ℕ → ℂ` be a family dense in the open window `O` (each point of `O`
is a limit of members of `X` lying in `O`). If `m` is jointly continuous on `O × O`, `D` is jointly continuous on `O × O`
and `D` is a Euclidean length metric, and `ofReal (m (X i) (X j)) = ofReal b * ofReal (D (X i) (X j))` for all `i, j` with
`X i, X j ∈ O`, then `m x y = b * D x y` as real numbers for all `x, y ∈ O`. -/
theorem eq_const_mul_of_dense_family {D m : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {O : Set ℂ} (hO : IsOpen O)
    {b : ℝ} (hb : 0 < b) {X : ℕ → ℂ}
    (hdense : ∀ x ∈ O, ∀ ε > 0, ∃ i, X i ∈ O ∧ dist (X i) x < ε)
    (hm : ContinuousOn (fun p : ℂ × ℂ => m p.1 p.2) (O ×ˢ O))
    (hDc : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (O ×ˢ O))
    (hfam : ∀ i j, X i ∈ O → X j ∈ O →
      ENNReal.ofReal (m (X i) (X j)) = ENNReal.ofReal b * ENNReal.ofReal (D (X i) (X j))) :
    ∀ x ∈ O, ∀ y ∈ O, m x y = b * D x y := by
  set T : Set (ℂ × ℂ) := {p | ∃ i j, X i ∈ O ∧ X j ∈ O ∧ p = (X i, X j)} with hT
  have hTsub : T ⊆ O ×ˢ O := by
    rintro p ⟨i, j, hi, hj, rfl⟩
    exact ⟨hi, hj⟩
  have hclos : O ×ˢ O ⊆ closure T := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨i, hi, hxi⟩ := hdense x hx (ε / 2) (half_pos hε)
    obtain ⟨j, hj, hyj⟩ := hdense y hy (ε / 2) (half_pos hε)
    refine ⟨(X i, X j), ⟨i, j, hi, hj, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    dsimp only
    rw [dist_comm] at hxi hyj
    exact max_lt (by linarith) (by linarith)
  have hEq : Set.EqOn (fun p : ℂ × ℂ => ENNReal.ofReal (m p.1 p.2))
      (fun p : ℂ × ℂ => ENNReal.ofReal b * ENNReal.ofReal (D p.1 p.2)) T := by
    rintro p ⟨i, j, hi, hj, rfl⟩
    exact hfam i j hi hj
  have hf : ContinuousOn (fun p : ℂ × ℂ => ENNReal.ofReal (m p.1 p.2)) (O ×ˢ O) :=
    ENNReal.continuous_ofReal.comp_continuousOn hm
  have hg : ContinuousOn (fun p : ℂ × ℂ => ENNReal.ofReal b * ENNReal.ofReal (D p.1 p.2)) (O ×ˢ O) :=
    (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn hDc)
  have hE := Set.EqOn.of_subset_closure hEq hf hg hTsub hclos
  have hid : ∀ x ∈ O, ∀ y ∈ O, ENNReal.ofReal (m x y) = ENNReal.ofReal b * ENNReal.ofReal (D x y) :=
    fun x hx y hy => hE (show (x, y) ∈ O ×ˢ O from ⟨hx, hy⟩)
  have hcont : ∀ x ∈ O, ContinuousAt (fun y => m x y) x := by
    intro x hx
    have h1 : ContinuousAt (fun p : ℂ × ℂ => m p.1 p.2) (x, x) :=
      hm.continuousAt ((hO.prod hO).mem_nhds (show (x, x) ∈ O ×ˢ O from ⟨hx, hx⟩))
    exact h1.comp (continuousAt_const.prodMk continuousAt_id)
  exact eq_const_mul_of_ofReal_eq hD hO hb hcont hid

end HarmonicBalls
