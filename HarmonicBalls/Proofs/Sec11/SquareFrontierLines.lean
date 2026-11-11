import HarmonicBalls.Defs.LBM

/-! # Boundary of a square and coordinate level sets -/

namespace HarmonicBalls
open MeasureTheory Set

/-- An s-finite measure charges at most countably many lines parallel to
either coordinate axis. -/
theorem countable_positive_coordinate_lines (μ : Measure ℂ) [SFinite μ] :
    Set.Countable {t : ℝ | 0 < μ {x : ℂ | x.re = t}} ∧
      Set.Countable {t : ℝ | 0 < μ {x : ℂ | x.im = t}} := by
  exact ⟨Measure.countable_meas_level_set_pos Complex.continuous_re.measurable,
    Measure.countable_meas_level_set_pos Complex.continuous_im.measurable⟩

/-- The boundary of a positive-side square lies on its four supporting lines. -/
theorem frontier_closedSquare_subset_lines (z : ℂ) {L : ℝ} (hL : 0 ≤ L) :
    frontier (closedSquare z L) ⊆
      {x : ℂ | x.re = z.re} ∪ {x | x.re = z.re + L} ∪
      {x | x.im = z.im} ∪ {x | x.im = z.im + L} := by
  intro x hx
  rw [closedSquare, Complex.frontier_reProdIm, closure_Icc, closure_Icc,
    frontier_Icc (by linarith : z.re ≤ z.re + L),
    frontier_Icc (by linarith : z.im ≤ z.im + L)] at hx
  simp only [mem_union, Complex.mem_reProdIm, mem_Icc, mem_insert_iff,
    mem_singleton_iff, mem_ofPred_eq] at hx ⊢
  tauto

/-- Four null supporting lines make the boundary of a square null. -/
theorem measure_frontier_closedSquare_eq_zero (μ : Measure ℂ) (z : ℂ)
    {L : ℝ} (hL : 0 ≤ L)
    (h₁ : μ {x : ℂ | x.re = z.re} = 0)
    (h₂ : μ {x : ℂ | x.re = z.re + L} = 0)
    (h₃ : μ {x : ℂ | x.im = z.im} = 0)
    (h₄ : μ {x : ℂ | x.im = z.im + L} = 0) :
    μ (frontier (closedSquare z L)) = 0 := by
  apply measure_mono_null (frontier_closedSquare_subset_lines z hL)
  exact measure_union_null (measure_union_null (measure_union_null h₁ h₂) h₃) h₄

end HarmonicBalls
