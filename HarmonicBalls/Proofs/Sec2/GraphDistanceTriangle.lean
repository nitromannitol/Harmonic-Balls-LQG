import HarmonicBalls.Defs.LQGGraphDistance

/-!
# Concatenation and symmetry of Liouville graph distance

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- Concatenating paths concatenates their admissible ball covers. -/
theorem IsLiouvilleGraphCover.trans {μ : Measure ℂ} {ε : ℝ} {z v w : ℂ}
    {n m : ℕ} (h₁ : IsLiouvilleGraphCover μ ε z v n)
    (h₂ : IsLiouvilleGraphCover μ ε v w m) :
    IsLiouvilleGraphCover μ ε z w (n + m) := by
  obtain ⟨b₁, hb₁, p₁, hp₁⟩ := h₁
  obtain ⟨b₂, hb₂, p₂, hp₂⟩ := h₂
  refine ⟨Fin.append b₁ b₂, ?_, p₁.trans p₂, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hb₁ j
    · simpa only [Fin.append_right] using hb₂ j
  · intro t
    have ht : (p₁.trans p₂) t ∈ Set.range p₁ ∪ Set.range p₂ := by
      rw [← Path.trans_range]
      exact ⟨t, rfl⟩
    rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
    · obtain ⟨i, hi⟩ := hp₁ s
      refine ⟨Fin.castAdd m i, ?_⟩
      simpa only [Fin.append_left, ← hs] using hi
    · obtain ⟨i, hi⟩ := hp₂ s
      refine ⟨Fin.natAdd n i, ?_⟩
      simpa only [Fin.append_right, ← hs] using hi

/-- Reversing a path preserves every admissible cover count. -/
theorem IsLiouvilleGraphCover.symm {μ : Measure ℂ} {ε : ℝ} {z w : ℂ} {n : ℕ}
    (h : IsLiouvilleGraphCover μ ε z w n) : IsLiouvilleGraphCover μ ε w z n := by
  obtain ⟨balls, hb, p, hp⟩ := h
  refine ⟨balls, hb, p.symm, ?_⟩
  intro t
  have ht : p.symm t ∈ Set.range p := by
    rw [← Path.symm_range]
    exact ⟨t, rfl⟩
  obtain ⟨s, hs⟩ := ht
  obtain ⟨i, hi⟩ := hp s
  exact ⟨i, hs ▸ hi⟩

/-- A finite graph distance is attained by an admissible cover. -/
theorem exists_isLiouvilleGraphCover_of_ne_top {μ : Measure ℂ} {ε : ℝ} {z w : ℂ}
    (h : liouvilleGraphDistance μ ε z w ≠ ⊤) :
    ∃ n : ℕ, liouvilleGraphDistance μ ε z w = n ∧ IsLiouvilleGraphCover μ ε z w n := by
  let s : Set ℕ∞ := {k | ∃ n : ℕ, k = n ∧ IsLiouvilleGraphCover μ ε z w n}
  have hs : s.Nonempty := by
    by_contra he
    have : s = ∅ := Set.not_nonempty_iff_eq_empty.mp he
    apply h
    change sInf s = ⊤
    rw [this, sInf_empty]
  have hmem : sInf s ∈ s := csInf_mem hs
  obtain ⟨n, hn, hc⟩ := hmem
  exact ⟨n, hn, hc⟩

/-- Liouville graph distance satisfies the triangle inequality, including infinity. -/
theorem liouvilleGraphDistance_triangle (μ : Measure ℂ) (ε : ℝ) (z v w : ℂ) :
    liouvilleGraphDistance μ ε z w ≤
      liouvilleGraphDistance μ ε z v + liouvilleGraphDistance μ ε v w := by
  by_cases h₁ : liouvilleGraphDistance μ ε z v = ⊤
  · simp [h₁]
  by_cases h₂ : liouvilleGraphDistance μ ε v w = ⊤
  · simp [h₂]
  obtain ⟨n, hn, hc₁⟩ := exists_isLiouvilleGraphCover_of_ne_top h₁
  obtain ⟨m, hm, hc₂⟩ := exists_isLiouvilleGraphCover_of_ne_top h₂
  rw [hn, hm, ← ENat.natCast_add]
  exact liouvilleGraphDistance_le (hc₁.trans hc₂)

/-- Liouville graph distance is symmetric in its endpoints. -/
theorem liouvilleGraphDistance_symm (μ : Measure ℂ) (ε : ℝ) (z w : ℂ) :
    liouvilleGraphDistance μ ε z w = liouvilleGraphDistance μ ε w z := by
  unfold liouvilleGraphDistance
  congr 1
  ext k
  constructor <;> rintro ⟨n, rfl, hc⟩ <;> exact ⟨n, rfl, hc.symm⟩

#print axioms IsLiouvilleGraphCover.trans
#print axioms IsLiouvilleGraphCover.symm
#print axioms exists_isLiouvilleGraphCover_of_ne_top
#print axioms liouvilleGraphDistance_triangle
#print axioms liouvilleGraphDistance_symm

end HarmonicBalls
