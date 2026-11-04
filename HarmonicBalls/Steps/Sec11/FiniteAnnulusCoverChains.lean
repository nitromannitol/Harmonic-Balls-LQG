import HarmonicBalls.Steps.Sec11.ExponentialAnnulusCorridors

/-! # Finite chains of annular pieces

Local internal diameter bounds on a finite overlapping chain give a bound for
its union in an enclosing corridor.
-/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- A finite chain of overlapping pieces has internal distance bounded by the
sum of their bounds in the enclosing domain. -/
theorem IsEuclideanLengthMetric.internalMetric_le_sum_finite_cover_chain
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (U : Set ℂ)
    (A : ℕ → Set ℂ) (z : ℕ → ℂ) (c : ℕ → ℝ≥0∞) (N : ℕ)
    (hz : ∀ i < N, z (i + 1) ∈ A i ∧ z (i + 1) ∈ A (i + 1))
    (hdiam : ∀ i ≤ N, ∀ x ∈ A i, ∀ y ∈ A i, internalMetric D U x y ≤ c i)
    (n k : ℕ) (hnk : n + k ≤ N) {x y : ℂ} (hx : x ∈ A n) (hy : y ∈ A (n + k)) :
    internalMetric D U x y ≤ ∑ i ∈ Finset.range (k + 1), c (n + i) := by
  induction k generalizing y with
  | zero =>
    simpa only [Nat.zero_add, Nat.add_zero, Finset.range_one, Finset.sum_singleton] using
      hdiam n hnk x hx y hy
  | succ k ih =>
    have hprev : n + k < N := by omega
    have hanchor := hz (n + k) hprev
    have hnext : z (n + k + 1) ∈ A (n + (k + 1)) := by
      simpa only [Nat.add_assoc] using hanchor.2
    rw [Finset.sum_range_succ]
    calc
      internalMetric D U x y ≤ internalMetric D U x (z (n + k + 1)) +
          internalMetric D U (z (n + k + 1)) y := hD.internalMetric_triangle U _ _ _
      _ ≤ (∑ i ∈ Finset.range (k + 1), c (n + i)) + c (n + (k + 1)) :=
        add_le_add (ih (by omega) hanchor.1) (hdiam _ hnk _ hnext y hy)

/-- If a set is covered by at most `N+1` overlapping pieces, each of
internal diameter at most `C`, its internal diameter is at most `(N+1) C`. -/
theorem IsEuclideanLengthMetric.internalMetric_le_of_finite_cover_chain
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (U K : Set ℂ)
    (A W : ℕ → Set ℂ) (z : ℕ → ℂ) (N : ℕ) (C : ℝ≥0∞)
    (hz : ∀ i < N, z (i + 1) ∈ A i ∧ z (i + 1) ∈ A (i + 1))
    (hcover : ∀ x ∈ K, ∃ i ≤ N, x ∈ A i)
    (hWU : ∀ i ≤ N, W i ⊆ U)
    (hdiam : ∀ i ≤ N, ∀ x ∈ A i, ∀ y ∈ A i, internalMetric D (W i) x y ≤ C)
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) :
    internalMetric D U x y ≤ (N + 1 : ℕ) * C := by
  have hd : ∀ i ≤ N, ∀ x ∈ A i, ∀ y ∈ A i, internalMetric D U x y ≤ C := by
    intro i hi x hx y hy
    exact (internalMetric_anti D (hWU i hi) x y).trans (hdiam i hi x hx y hy)
  obtain ⟨i, hi, hxi⟩ := hcover x hx
  obtain ⟨j, hj, hyj⟩ := hcover y hy
  have hchain : ∀ i j, i ≤ j → j ≤ N → ∀ {a b}, a ∈ A i → b ∈ A j →
      internalMetric D U a b ≤ (N + 1 : ℕ) * C := by
    intro i j hij hjN a b ha hb
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    have h := hD.internalMetric_le_sum_finite_cover_chain U A z (fun _ => C) N hz hd i k hjN ha hb
    calc
      _ ≤ ∑ _ ∈ Finset.range (k + 1), C := h
      _ = ((k + 1 : ℕ) : ℝ≥0∞) * C := by simp
      _ ≤ ((N + 1 : ℕ) : ℝ≥0∞) * C := by
        gcongr
        omega
  rcases le_total i j with hij | hji
  · exact hchain i j hij hj hxi hyj
  · rw [hD.internalMetric_symm U x y]
    exact hchain j i hji hi hyj hxi

/-- A corridor diameter exceedance forces at least one local diameter
exceedance, provided the ambient distance is a Euclidean length metric. -/
theorem measure_internalMetric_cover_chain_exceedance_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (U K : Set ℂ)
    (A W : ℕ → Set ℂ) (z : ℕ → ℂ) (N : ℕ) (C : Ω → ℝ≥0∞)
    (hz : ∀ i < N, z (i + 1) ∈ A i ∧ z (i + 1) ∈ A (i + 1))
    (hcover : ∀ x ∈ K, ∃ i ≤ N, x ∈ A i)
    (hWU : ∀ i ≤ N, W i ⊆ U) :
    P {ω | IsEuclideanLengthMetric (D ω) ∧
      ∃ x ∈ K, ∃ y ∈ K, (N + 1 : ℕ) * C ω < internalMetric (D ω) U x y} ≤
      ∑ i ∈ Finset.range (N + 1), P {ω | ∃ x ∈ A i, ∃ y ∈ A i,
        C ω < internalMetric (D ω) (W i) x y} := by
  classical
  calc
    _ ≤ P (⋃ i ∈ Finset.range (N + 1), {ω | ∃ x ∈ A i, ∃ y ∈ A i,
        C ω < internalMetric (D ω) (W i) x y}) := by
      apply measure_mono
      intro ω hω
      by_contra hn
      have hd : ∀ i ≤ N, ∀ x ∈ A i, ∀ y ∈ A i,
          internalMetric (D ω) (W i) x y ≤ C ω := by
        intro i hi x hx y hy
        apply le_of_not_gt
        intro hbad
        apply hn
        exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),
          ⟨x, hx, y, hy, hbad⟩⟩⟩
      obtain ⟨hmetric, x, hx, y, hy, hbad⟩ := hω
      exact (not_lt_of_ge (hmetric.internalMetric_le_of_finite_cover_chain U K A W z N
        (C ω) hz hcover hWU hd hx hy)) hbad
    _ ≤ _ := measure_biUnion_finset_le _ _

#print axioms measure_internalMetric_cover_chain_exceedance_le
#print axioms IsEuclideanLengthMetric.internalMetric_le_sum_finite_cover_chain
#print axioms IsEuclideanLengthMetric.internalMetric_le_of_finite_cover_chain

end HarmonicBalls
