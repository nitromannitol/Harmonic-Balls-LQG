import HarmonicBalls.Steps.Sec11.ProperMetricMidpoints

/-!
# Intermediate points in proper length metrics

Compactness upgrades near-minimizing paths to points that exactly split the
distance between their endpoints at any prescribed intermediate radius.
-/

namespace HarmonicBalls

open Metric Set
open scoped ENNReal

/-- A near-minimizing path passes through the prescribed distance from its
initial point, with the remaining distance within `ε` of optimal. -/
theorem IsEuclideanLengthMetric.exists_approximate_intermediate
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (x y : ℂ) {r ε : ℝ}
    (hr : 0 ≤ r) (hr' : r ≤ D x y) (hε : 0 < ε) :
    ∃ m : ℂ, D x m = r ∧ D m y < D x y - r + ε := by
  obtain ⟨p, hp⟩ := hD.exists_pathLength_lt hnonneg x y hε
  have hc : Continuous fun t : ℝ => D x (p.extend t) := by
    have h : Continuous fun m : ℂ => D x m := by
      simpa only [hD.symm x] using hD.continuous_left x
    exact h.comp p.continuous_extend
  have hmem : r ∈ Icc (D x (p.extend 0)) (D x (p.extend 1)) := by
    simpa only [p.extend_zero, p.extend_one, hD.self_eq_zero] using ⟨hr, hr'⟩
  obtain ⟨t, ht, heq⟩ := intermediate_value_Icc (zero_le_one' ℝ) hc.continuousOn hmem
  have hsum := lt_of_le_of_lt (hD.ofReal_two_segment_le_pathLength hnonneg p ht) hp
  have hreal : D x (p.extend t) + D (p.extend t) y < D x y + ε :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (add_nonneg (hnonneg x (p.extend t)) (hnonneg (p.extend t) y))).1 hsum
  exact ⟨p.extend t, heq, by linarith⟩

/-- Every intermediate distance is attained by a point which splits the
endpoint distance exactly, when closed metric balls are compact. -/
theorem IsEuclideanLengthMetric.exists_intermediate_of_compact_closedBalls
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (x y : ℂ) {r : ℝ} (hr : 0 ≤ r) (hr' : r ≤ D x y) :
    ∃ m : ℂ, D x m = r ∧ D m y = D x y - r := by
  let S : Set ℂ := {m | D x m = r}
  have hc : Continuous fun m : ℂ => D x m := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hclosed : IsClosed S := isClosed_eq hc continuous_const
  have hScompact : IsCompact S := (hcompact x r).of_isClosed_subset hclosed (by
    intro m hm
    exact le_of_eq hm)
  obtain ⟨m₀, hm₀, _⟩ :=
    hD.exists_approximate_intermediate hnonneg x y hr hr' zero_lt_one
  have hSnonempty : S.Nonempty := ⟨m₀, hm₀⟩
  obtain ⟨m, hm, hmin⟩ := hScompact.exists_isMinOn hSnonempty
    (hD.continuous_left y).continuousOn
  have hupper : D m y ≤ D x y - r := by
    by_contra hn
    have heps : 0 < (D m y - (D x y - r)) / 2 := by linarith
    obtain ⟨m', hm', hnear⟩ :=
      hD.exists_approximate_intermediate hnonneg x y hr hr' heps
    have hle : D m y ≤ D m' y := hmin hm'
    linarith
  have htri := hD.triangle x m y
  have hlower : D x y - r ≤ D m y := by
    change D x m = r at hm
    linarith
  exact ⟨m, hm, le_antisymm hupper hlower⟩

/-- A prescribed number of equal segments can be placed between two points of
a proper length metric, with total segment length equal to the distance. -/
theorem IsEuclideanLengthMetric.exists_equal_segment_chain
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R}) :
    ∀ (n : ℕ) (x y : ℂ) (δ : ℝ), 0 ≤ δ → D x y = (n : ℝ) * δ →
      ∃ f : ℕ → ℂ, f 0 = x ∧ f n = y ∧ ∀ k < n, D (f k) (f (k + 1)) = δ := by
  intro n
  induction n with
  | zero =>
      intro x y δ hδ hxy
      have hzero : D x y = 0 := by simpa using hxy
      have heq : x = y := hD.eq_of_eq_zero x y hzero
      refine ⟨fun _ => x, rfl, heq, ?_⟩
      intro k hk
      omega
  | succ n ih =>
      intro x y δ hδ hxy
      have hcast : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hle : δ ≤ D x y := by
        rw [Nat.cast_succ] at hxy
        nlinarith
      obtain ⟨m, hxm, hmy⟩ :=
        hD.exists_intermediate_of_compact_closedBalls hnonneg hcompact x y hδ hle
      have hrest : D m y = (n : ℝ) * δ := by
        rw [Nat.cast_succ] at hxy
        linarith
      obtain ⟨g, hg0, hgn, hg⟩ := ih m y δ hδ hrest
      let f : ℕ → ℂ := fun k => Nat.casesOn k x g
      refine ⟨f, rfl, ?_, ?_⟩
      · simpa [f] using hgn
      · intro k hk
        cases k with
        | zero => simpa [f, hg0] using hxm
        | succ k =>
            have hk' : k < n := by omega
            simpa [f] using hg k hk'

/-- Distances along a finite chain are bounded by the sum of its equal
successive segment lengths. -/
theorem IsEuclideanLengthMetric.chain_distance_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {n : ℕ} {δ : ℝ} {f : ℕ → ℂ}
    (hseg : ∀ k < n, D (f k) (f (k + 1)) = δ) :
    ∀ i j : ℕ, i ≤ j → j ≤ n →
      D (f i) (f j) ≤ ((j : ℝ) - (i : ℝ)) * δ := by
  intro i j hij hjn
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      simp only [hD.self_eq_zero, Nat.cast_zero, sub_self, zero_mul, le_refl]
  | succ j ih =>
      by_cases h : i ≤ j
      · have hj : j < n := by omega
        have hi := ih h (by omega)
        have ht := hD.triangle (f i) (f j) (f (j + 1))
        rw [hseg j hj] at ht
        rw [Nat.cast_succ]
        nlinarith
      · have : i = j + 1 := by omega
        subst i
        simp only [hD.self_eq_zero, sub_self, zero_mul, le_refl]

/-- If the length of an equal-segment chain equals the endpoint distance,
every subchain is also distance minimizing. -/
theorem IsEuclideanLengthMetric.chain_distance_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {n : ℕ} {δ : ℝ} {f : ℕ → ℂ}
    (hseg : ∀ k < n, D (f k) (f (k + 1)) = δ)
    (hends : D (f 0) (f n) = (n : ℝ) * δ)
    {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    D (f i) (f j) = ((j : ℝ) - (i : ℝ)) * δ := by
  have hupper := hD.chain_distance_le hseg i j hij hjn
  have hleft := hD.chain_distance_le hseg 0 i (Nat.zero_le i) (le_trans hij hjn)
  have hright := hD.chain_distance_le hseg j n hjn le_rfl
  have ht₁ := hD.triangle (f 0) (f i) (f n)
  have ht₂ := hD.triangle (f i) (f j) (f n)
  rw [hends] at ht₁
  simp only [Nat.cast_zero, sub_zero] at hleft
  nlinarith

/-- Every proper length metric admits an isometric finite subdivision between
any two endpoints, at every prescribed positive subdivision count. -/
theorem IsEuclideanLengthMetric.exists_isometric_subdivision
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y)
    (hcompact : ∀ x : ℂ, ∀ R : ℝ, IsCompact {z : ℂ | D x z ≤ R})
    (n : ℕ) (hn : 0 < n) (x y : ℂ) :
    ∃ f : ℕ → ℂ, f 0 = x ∧ f n = y ∧ ∀ i j : ℕ, i ≤ j → j ≤ n →
      D (f i) (f j) = ((j : ℝ) - (i : ℝ)) * (D x y / n) := by
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hδ : 0 ≤ D x y / n := div_nonneg (hnonneg x y) (le_of_lt hnreal)
  have hdist : D x y = (n : ℝ) * (D x y / n) := by
    field_simp
  obtain ⟨f, hf0, hfn, hseg⟩ :=
    hD.exists_equal_segment_chain hnonneg hcompact n x y (D x y / n) hδ hdist
  refine ⟨f, hf0, hfn, ?_⟩
  have hends : D (f 0) (f n) = (n : ℝ) * (D x y / n) := by
    rw [hf0, hfn, ← hdist]
  intro i j hij hjn
  exact hD.chain_distance_eq hseg hends hij hjn

end HarmonicBalls
