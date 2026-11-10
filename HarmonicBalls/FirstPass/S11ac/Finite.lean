import HarmonicBalls.FirstPass.S11ac.ChainGlue
import HarmonicBalls.FirstPass.S11ac.Lebesgue

/-! # Finiteness of the internal metric from finite piece metrics (fp-S11ac, owner z6)

If a path-connected open set `X` is covered by open pieces `Dp j ⊆ X` whose internal metrics are finite, then the
internal metric of `X` is finite between any two of its points: subdivide a path in `X` by the Lebesgue lemma and
apply the triangle inequality along the subdivision points.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology unitInterval Metric
open scoped ENNReal

theorem internalMetric_lt_top_of_pieces {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {X : Set ℂ}
    (hXo : IsOpen X) (hXpc : IsPathConnected X) {Dp : ℕ → Set ℂ} (hDpX : ∀ j, Dp j ⊆ X)
    (hDpo : ∀ j, IsOpen (Dp j)) (hcov : X ⊆ ⋃ j, Dp j)
    (hfin : ∀ j z w, z ∈ Dp j → w ∈ Dp j → internalMetric D (Dp j) z w < ⊤)
    {x y : ℂ} (hx : x ∈ X) (hy : y ∈ X) :
    internalMetric D X x y < ⊤ := by
  set γ : Path x y := (hXpc.joinedIn x hx y hy).somePath with hγdef
  have hγX : ∀ t, γ t ∈ X := (hXpc.joinedIn x hx y hy).somePath_mem
  have hext : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ X := by
    intro t ht
    have := hγX ⟨t, ht⟩
    rwa [← Path.extend_extends' γ ⟨t, ht⟩] at this
  obtain ⟨N, u, j, _, hmono, hu0, huN, hpiece⟩ :=
    exists_subdivision_of_cover γ Dp hDpo (fun t ht => by
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov (hext t ht))
      exact ⟨i, hi⟩)
  set q : ℕ → ℂ := fun i => γ.extend (u i) with hq
  have hu_mem : ∀ i ≤ N, u i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← hu0]; exact hmono (Nat.zero_le i)
    · rw [← huN]; exact hmono hi
  have hqX : ∀ i ≤ N, q i ∈ X := fun i hi => hext _ (hu_mem i hi)
  have hq0 : q 0 = x := by
    simp only [hq, hu0, Path.extend_zero]
  have hqN : q N = y := by
    simp only [hq, huN, Path.extend_one]
  have hchain := internalMetric_chain_le hD hXo N q hqX
  rw [hq0, hqN] at hchain
  refine lt_of_le_of_lt hchain (ENNReal.sum_lt_top.2 fun i hi => ?_)
  have hiN : i < N := Finset.mem_range.1 hi
  have hmem1 : q i ∈ Dp (j i) := by
    have hI : u i ∈ Icc (u i) (u (i + 1)) := left_mem_Icc.2 (hmono (Nat.le_succ i))
    exact hpiece i hiN (u i) hI
  have hmem2 : q (i + 1) ∈ Dp (j i) := by
    have hI : u (i + 1) ∈ Icc (u i) (u (i + 1)) := right_mem_Icc.2 (hmono (Nat.le_succ i))
    exact hpiece i hiN (u (i + 1)) hI
  exact lt_of_le_of_lt (internalMetric_anti (hDpX (j i)) (q i) (q (i + 1)))
    (hfin (j i) (q i) (q (i + 1)) hmem1 hmem2)

end HarmonicBalls.S11ac
