import Mathlib

/-! # Subdivision of a path along an open cover

A path `γ` in `ℂ` whose image is covered by open sets `V i` is cut at the equally spaced times `u i = min (i / N) 1`,
for some `N ≥ 1`, so that each subinterval `[u i, u (i+1)]` is mapped into a single `V (j i)`.
This is the Lebesgue-number step of the lower bound for the punctured internal metric.
-/

namespace HarmonicBalls.S11ac

open Set Metric Filter Topology unitInterval

/-- Equal subdivision of `[0,1]` subordinate to an open cover of the image of a path. -/
theorem exists_subdivision_of_cover {x y : ℂ} (γ : Path x y) {ι : Type*} (V : ι → Set ℂ)
    (hV : ∀ i, IsOpen (V i)) (hcov : ∀ t ∈ Icc (0 : ℝ) 1, ∃ i, γ.extend t ∈ V i) :
    ∃ (N : ℕ) (u : ℕ → ℝ) (j : ℕ → ι), 0 < N ∧ Monotone u ∧ u 0 = 0 ∧ u N = 1 ∧
      ∀ i < N, ∀ t ∈ Icc (u i) (u (i + 1)), γ.extend t ∈ V (j i) := by
  have hc : ∀ i, IsOpen (γ.extend ⁻¹' V i) := fun i => (hV i).preimage γ.continuous_extend
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := Icc (0 : ℝ) 1) isCompact_Icc hc
    (fun t ht => mem_iUnion.2 (hcov t ht))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hNR : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  let u : ℕ → ℝ := fun i => min ((i : ℝ) / ((n + 1 : ℕ) : ℝ)) 1
  have hu : Monotone u := fun i k hik =>
    min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast hik) hNR.le)
  have hu0 : u 0 = 0 := by simp [u]
  have huN : u (n + 1) = 1 := by
    have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := le_of_eq (div_self hNR.ne').symm
    simp only [u]
    rw [min_eq_right h1]
  have hmem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hchoice : ∀ i, ∃ k, ball (u i) δ ⊆ γ.extend ⁻¹' V k := fun i => hleb (u i) (hmem i)
  choose j hj using hchoice
  refine ⟨n + 1, u, j, Nat.succ_pos n, hu, hu0, huN, fun i hi t ht => ?_⟩
  have hiN : ((i + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show i + 1 ≤ n + 1 from hi)
  have hui : u i = (i : ℝ) / ((n + 1 : ℕ) : ℝ) := by
    simp only [u]
    rw [min_eq_left]
    exact div_le_one_of_le₀ (by exact_mod_cast (show i ≤ n + 1 by omega)) hNR.le
  have hui1 : u (i + 1) = ((i : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) := by
    simp only [u]
    rw [min_eq_left]
    · rw [Nat.cast_succ]
    · exact div_le_one_of_le₀ hiN hNR.le
  have key : u (i + 1) - u i = 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [hui1, hui]
    push_cast
    ring
  have hδN : 1 / ((n + 1 : ℕ) : ℝ) < δ := by
    push_cast
    exact hn
  have hdist : dist t (u i) < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  exact hj i (mem_ball.mpr hdist)

end HarmonicBalls.S11ac

