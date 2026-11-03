import HarmonicBalls.Steps.Sec9.RegularOpenEqOfAEEq

/-!
# Lemma 9.4: proof of the deterministic step

Proof of the step `RegularOpenEqOfOpenPosMeasure` of `HarmonicBalls/Steps/Sec9/RegularOpenEqOfAEEq.lean`, and of
`RegularOpenEqOfAEEqStmt` (Lemma 9.4, lemma:regular-open-ae, line 2394 of paper/lqg_harmonic_ball-corrected.tex)
from input I1 (`LQGMeasureFullSupportStmt`, an explicit hypothesis: it is not proved in this repository).
-/

universe u

namespace HarmonicBalls

open MeasureTheory Metric Set

/-- If `X` is open, `Y` is regular open and `μ(X \ Y) = 0` for a measure `μ` charging every nonempty open set,
then `X ⊆ Y` (lines 2399-2405). -/
theorem IsRegularOpen.subset_of_measure_diff_eq_zero {μ : Measure ℂ} [μ.IsOpenPosMeasure] {X Y : Set ℂ}
    (hX : IsOpen X) (hY : IsRegularOpen Y) (h : μ (X \ Y) = 0) : X ⊆ Y := by
  have hopen : IsOpen (X \ closure Y) := hX.sdiff isClosed_closure
  have hnull : μ (X \ closure Y) = 0 := measure_mono_null (sdiff_subset_sdiff_right subset_closure) h
  have hcl : X ⊆ closure Y := sdiff_eq_empty.1 ((hopen.measure_eq_zero_iff μ).1 hnull)
  rw [← hY]
  exact hX.subset_interior_iff.2 hcl

theorem regularOpenEqOfOpenPosMeasure : RegularOpenEqOfOpenPosMeasure := by
  intro μ _ X Y hX hY hXY hYX
  exact (hY.subset_of_measure_diff_eq_zero hX.isOpen hXY).antisymm
    (hX.subset_of_measure_diff_eq_zero hY.isOpen hYX)

/-- Lemma 9.4 (lemma:regular-open-ae, line 2394), from the full support of `μ_h` (input I1). -/
theorem regularOpenEqOfAEEq (hI1 : LQGMeasureFullSupportStmt.{u}) : RegularOpenEqOfAEEqStmt.{u} :=
  regularOpenEqOfAEEq_of_steps regularOpenEqOfOpenPosMeasure hI1

end HarmonicBalls
