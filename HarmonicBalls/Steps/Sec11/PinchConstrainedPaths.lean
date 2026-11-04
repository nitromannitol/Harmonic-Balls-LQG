import HarmonicBalls.Steps.Sec11.InternalPinchScales

/-! # Constrained paths for the strengthened pinch event

The auxiliary event in the proof of Lemma 11.12 bounds paths outside the
obstacle. To obtain the internal-metric event one additionally needs those
paths to stay inside the ball of radius six.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- An upper bound for obstacle-avoiding paths constrained to the radius-six
ball supplies the first metric inequality in the strengthened pinch event. -/
theorem pinchFirstInternalBound_of_constrained_paths
    (D : ℂ → ℂ → ℝ) (Q' Q W : Set ℂ) (δ : ℝ)
    (h : (⨆ x ∈ sphere (0 : ℂ) 5,
        internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q))) :
    (⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (ball 0 6) 0 x) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) := by
  apply lt_of_le_of_lt ?_ h
  refine iSup_le fun x => iSup_le fun hx => ?_
  exact le_iSup_of_le x (le_iSup_of_le hx
    (internalMetric_anti D inter_subset_right 0 x))

end HarmonicBalls
