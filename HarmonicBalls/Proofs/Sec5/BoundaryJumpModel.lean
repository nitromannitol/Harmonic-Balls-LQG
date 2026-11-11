import HarmonicBalls.Proofs.Sec5.RightContinuousEnvelope
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # A closed-set model for boundary jumps

This model is not a cluster family. It shows that monotonicity, connectedness,
interior stability and vanishing planar mass of the increment do not by
themselves exclude a boundary jump. The model does not encode the obstacle
problem, and its sets need not be closures of open sets.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

private def modelBefore : Set ℂ := closedBall 0 1 ∩ {z : ℂ | 0 ≤ z.re}
private def modelAfter : Set ℂ := modelBefore ∪ sphere 0 1
private def modelFamily (t : ℝ) : Set ℂ := if 1 < t then modelAfter else modelBefore

private theorem modelBefore_closed : IsClosed modelBefore :=
  isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_re)

private theorem modelBefore_connected : IsConnected modelBefore := by
  apply ((convex_closedBall (0 : ℂ) 1).inter (convex_halfSpace_re_ge 0)).isConnected
  exact ⟨0, by simp⟩

private theorem modelAfter_closed : IsClosed modelAfter := modelBefore_closed.union isClosed_sphere

private theorem modelAfter_connected : IsConnected modelAfter := by
  apply IsConnected.union _ modelBefore_connected (isConnected_sphere (by simp) 0 (by norm_num))
  exact ⟨1, by simp [modelBefore, mem_closedBall, dist_zero_right]⟩

/-- There is an increasing family of compact continua in the closed unit disc
whose right limit adds only circle points of planar measure zero, but adds at
least one such point. This is a topological model, not an LQG cluster. -/
theorem exists_connected_zero_area_boundary_jump :
    ∃ F : ℝ → Set ℂ,
      (∀ t, IsCompact (F t) ∧ IsConnected (F t) ∧ F t ⊆ closedBall (0 : ℂ) 1) ∧
      (∀ s t, s ≤ t → F s ⊆ F t) ∧
      ((rightClosedEnvelope F 1 \ F 1) ⊆ sphere (0 : ℂ) 1) ∧
      volume (rightClosedEnvelope F 1 \ F 1) = 0 ∧
      (rightClosedEnvelope F 1 \ F 1).Nonempty := by
  have hbefore : modelBefore ⊆ closedBall (0 : ℂ) 1 := inter_subset_left
  have hafter : modelAfter ⊆ closedBall (0 : ℂ) 1 :=
    union_subset hbefore sphere_subset_closedBall
  have henv : rightClosedEnvelope modelFamily 1 = modelAfter := by
    apply Set.Subset.antisymm
    · intro x hx
      have hx0 := mem_iInter.mp hx 0
      simpa [modelFamily, modelAfter_closed.closure_eq] using hx0
    · intro x hx
      apply mem_iInter.mpr
      intro n
      apply subset_closure
      simpa [modelFamily] using hx
  have hbase : modelFamily 1 = modelBefore := by simp [modelFamily]
  have hjump : rightClosedEnvelope modelFamily 1 \ modelFamily 1 ⊆ sphere (0 : ℂ) 1 := by
    rw [henv, hbase]
    intro x hx
    rcases hx.1 with h | h
    · exact (hx.2 h).elim
    · exact h
  refine ⟨modelFamily, ?_, ?_, hjump, ?_, ?_⟩
  · intro t
    by_cases ht : 1 < t
    · simp only [modelFamily, ite_eq_left ht]
      exact ⟨(isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset modelAfter_closed hafter,
        modelAfter_connected, hafter⟩
    · simp only [modelFamily, ite_eq_right ht]
      exact ⟨(isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset modelBefore_closed hbefore,
        modelBefore_connected, hbefore⟩
  · intro s t hst
    by_cases hs : 1 < s
    · have ht : 1 < t := lt_of_lt_of_le hs hst
      simp [modelFamily, hs, ht]
    · by_cases ht : 1 < t
      · simp [modelFamily, hs, ht, modelAfter]
      · simp [modelFamily, hs, ht]
  · apply measure_mono_null hjump
    exact Measure.addHaar_sphere volume 0 1
  · rw [henv, hbase]
    refine ⟨-1, ?_, ?_⟩
    · right
      simp
    · simp [modelBefore]


end HarmonicBalls
