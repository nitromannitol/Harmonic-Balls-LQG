import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.InternalMetricPaths

/-!
# Proposition 11.10, deterministic chain bound (fp-S11c, owner n1)

FIRST-PASS NEW. Written source: corrected paper lines 3041-3044 (the triangle bound of the proof of
`lemma:mass-diam`), with the constant repaired to `ε/3` (defect (a), GRAPH G39): a set `K` (the closure of the
exterior set `G`) and pieces `P j` (the enlarged cells `Ŝ ∩ S₂`) each carry a bound `ε/3`, and every piece meets `K`.
Then the internal metric of the big set `W` (`= S₂`) is at most `ε` on `W`.

Only the triangle inequality `IsEuclideanLengthMetric.internalMetric_triangle` and the monotonicity
`internalMetric_anti` are used.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

theorem internalMetric_le_three_pieces {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {ι : Type*} {W K : Set ℂ} {P : ι → Set ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hKW : K ⊆ W) (hPW : ∀ j, P j ⊆ W) (hcover : W ⊆ K ∪ ⋃ j, P j)
    (hmeet : ∀ j, ∃ w, w ∈ K ∧ w ∈ P j)
    (hK : ∀ u ∈ K, ∀ v ∈ K, internalMetric D K u v ≤ ENNReal.ofReal (ε / 3))
    (hP : ∀ j, ∀ u ∈ P j, ∀ v ∈ P j, internalMetric D (P j) u v ≤ ENNReal.ofReal (ε / 3)) :
    ∀ u ∈ W, ∀ v ∈ W, internalMetric D W u v ≤ ENNReal.ofReal ε := by
  have h3 : 0 ≤ ε / 3 := div_nonneg hε (by norm_num)
  have hK' : ∀ u ∈ K, ∀ v ∈ K, internalMetric D W u v ≤ ENNReal.ofReal (ε / 3) :=
    fun u hu v hv => (internalMetric_anti D hKW u v).trans (hK u hu v hv)
  -- every point of `W` has an anchor in `K` at distance at most `ε/3`, in both orders
  have anchorL : ∀ x ∈ W, ∃ a ∈ K, internalMetric D W x a ≤ ENNReal.ofReal (ε / 3) := by
    intro x hx
    rcases hcover hx with hxK | hxP
    · exact ⟨x, hxK, hK' x hxK x hxK⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hxP
      obtain ⟨w, hwK, hwP⟩ := hmeet j
      exact ⟨w, hwK, (internalMetric_anti D (hPW j) x w).trans (hP j x hj w hwP)⟩
  have anchorR : ∀ x ∈ W, ∃ b ∈ K, internalMetric D W b x ≤ ENNReal.ofReal (ε / 3) := by
    intro x hx
    rcases hcover hx with hxK | hxP
    · exact ⟨x, hxK, hK' x hxK x hxK⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hxP
      obtain ⟨w, hwK, hwP⟩ := hmeet j
      exact ⟨w, hwK, (internalMetric_anti D (hPW j) w x).trans (hP j w hwP x hj)⟩
  have hsum : ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add h3 h3, ← ENNReal.ofReal_add h3 (add_nonneg h3 h3)]
    congr 1
    ring
  intro u hu v hv
  obtain ⟨a, haK, hua⟩ := anchorL u hu
  obtain ⟨b, hbK, hbv⟩ := anchorR v hv
  calc internalMetric D W u v
      ≤ internalMetric D W u a + internalMetric D W a v := hD.internalMetric_triangle W u a v
    _ ≤ internalMetric D W u a + (internalMetric D W a b + internalMetric D W b v) :=
        add_le_add le_rfl (hD.internalMetric_triangle W a b v)
    _ ≤ ENNReal.ofReal (ε / 3) + (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) :=
        add_le_add hua (add_le_add (hK' a haK b hbK) hbv)
    _ = ENNReal.ofReal ε := hsum

end HarmonicBalls
