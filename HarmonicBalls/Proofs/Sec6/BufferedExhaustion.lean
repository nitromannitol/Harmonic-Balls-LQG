import HarmonicBalls.Proofs.Sec6.AnnularContinuityExhaustion

/-! # Buffered exhaustions at a vanishing scale -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped Topology

/-- An increasing exhaustion with a positive buffer at each stage can be
slowed down so that the given vanishing scale fits inside the neighborhood.
Each new set is either empty or an original exhaustion set, preserving its
continuity-set properties. -/
theorem exists_buffered_exhaustion
    {X : Type*} [PseudoMetricSpace X] (E : ℕ → Set X) (U : Set X)
    (hmono : Monotone E) (hbuffer : ∀ k, ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E k, closedBall x δ ⊆ U)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ F : ℕ → Set X, Monotone F ∧ (⋃ n, F n) = ⋃ n, E n ∧
      (∀ n, F n = ∅ ∨ ∃ k, F n = E k) ∧
      ∀ n x, x ∈ F n → closedBall x (ε n) ⊆ U := by
  classical
  choose δ hδ hδU using hbuffer
  have hsmall (k : ℕ) : ∀ᶠ n in atTop, ε n < δ k :=
    hε.eventually (Iio_mem_nhds (hδ k))
  choose N hN using fun k => eventually_atTop.mp (hsmall k)
  let index (n : ℕ) : ℕ := n.findGreatest (fun k => N k ≤ n)
  let F (n : ℕ) : Set X := if N 0 ≤ n then E (index n) else ∅
  have hindex (i j : ℕ) (hij : i ≤ j) : index i ≤ index j := by
    exact Nat.findGreatest_mono (fun _ hk => hk.trans hij) hij
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    by_cases hi : N 0 ≤ i
    · have hj : N 0 ≤ j := hi.trans hij
      simpa only [F, hi, hj, ↓reduceIte] using hmono (hindex i j hij)
    · simp only [F, hi, ↓reduceIte, empty_subset]
  · ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hx⟩
      by_cases hn : N 0 ≤ n
      · exact ⟨index n, by simpa [F, hn] using hx⟩
      · simp [F, hn] at hx
    · rintro ⟨k, hx⟩
      let n := max k (max (N 0) (N k))
      have hn0 : N 0 ≤ n := (le_max_left _ _).trans (le_max_right _ _)
      have hkn : k ≤ n := le_max_left _ _
      have hNk : N k ≤ n := (le_max_right _ _).trans (le_max_right _ _)
      have hkindex : k ≤ index n := Nat.le_findGreatest hkn hNk
      refine ⟨n, ?_⟩
      simpa [F, hn0] using (hmono hkindex hx)
  · intro n
    by_cases hn : N 0 ≤ n
    · exact Or.inr ⟨index n, by simp [F, hn]⟩
    · exact Or.inl (by simp [F, hn])
  · intro n x hx
    by_cases hn : N 0 ≤ n
    · have hx' : x ∈ E (index n) := by simpa [F, hn] using hx
      have hNindex : N (index n) ≤ n := by
        exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (Nat.zero_le n) hn
      exact (closedBall_subset_closedBall (hN (index n) n hNindex).le).trans
        (hδU (index n) x hx')
    · simp [F, hn] at hx

/-- An LQG continuity annulus has a continuity-set exhaustion buffered at
any prescribed scale tending to zero. -/
theorem IsWholePlaneGFF.exists_buffered_lqg_annular_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (z : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus z r R)) = 0)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ F : ℕ → Set ℂ, (∀ n, IsOpen (F n)) ∧ Monotone F ∧
      (⋃ n, F n) = annulus z r R ∧ Bornology.IsBounded (⋃ n, F n) ∧
      (∀ n x, x ∈ F n → closedBall x (ε n) ⊆ annulus z r R) ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (F n)) = 0) ∧
        μ ω (frontier (⋃ n, F n)) = 0 := by
  obtain ⟨E, hEopen, hEmono, hEunion, hEbounded, hEbuffer, hEfront⟩ :=
    IsWholePlaneGFF.exists_ae_lqg_annular_continuity_exhaustion P hgff hμ z hr hrR hfront
  obtain ⟨F, hFmono, hFunion, hFchoice, hFbuffer⟩ :=
    exists_buffered_exhaustion E (annulus z r R) hEmono hEbuffer ε hε
  have hFU : (⋃ n, F n) = annulus z r R := hFunion.trans hEunion
  refine ⟨F, ?_, hFmono, hFU, ?_, hFbuffer, ?_⟩
  · intro n
    rcases hFchoice n with hn | ⟨k, hk⟩
    · rw [hn]; exact isOpen_empty
    · rw [hk]; exact hEopen k
  · rw [hFunion]; exact hEbounded
  · filter_upwards [hEfront] with ω hω
    refine ⟨?_, ?_⟩
    · intro n
      rcases hFchoice n with hn | ⟨k, hk⟩
      · rw [hn, frontier_empty, measure_empty]
      · rw [hk]; exact hω.1 k
    · rw [hFunion]; exact hω.2

end HarmonicBalls.Section6
