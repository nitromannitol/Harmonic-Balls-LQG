import HarmonicBalls.Steps.Sec11.PinchConstrainedPaths

/-! # Uniform path witnesses for the pinch comparison

The strict internal-distance bound is equivalent to a common strict margin
and paths satisfying that margin. No geodesic existence is required.
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

/-- A strict uniform internal-distance bound is equivalent to the existence of
paths with a common bound strictly below the threshold. -/
theorem iSup_internalMetric_lt_iff_exists_uniform_paths
    (D : ℂ → ℂ → ℝ) (U K : Set ℂ) (x : ℂ) (b : ℝ≥0∞) :
    (⨆ y ∈ K, internalMetric D U x y) < b ↔
      ∃ c : ℝ≥0∞, c < b ∧ ∀ y ∈ K, ∃ p : Path x y,
        (∀ t, p t ∈ U) ∧ pathLength D p ≤ c := by
  constructor
  · intro h
    obtain ⟨c, hc, hcb⟩ := exists_between h
    refine ⟨c, hcb, ?_⟩
    intro y hy
    have hle : internalMetric D U x y ≤ ⨆ z ∈ K, internalMetric D U x z :=
      le_iSup_of_le y (le_iSup (fun _ : y ∈ K => internalMetric D U x y) hy)
    have hyc : internalMetric D U x y < c := hle.trans_lt hc
    change (⨅ p : Path x y, ⨅ (_ : ∀ t, p t ∈ U), pathLength D p) < c at hyc
    obtain ⟨p, hp⟩ := iInf_lt_iff.mp hyc
    obtain ⟨hpU, hpc⟩ := iInf_lt_iff.mp hp
    exact ⟨p, hpU, hpc.le⟩
  · rintro ⟨c, hcb, hpaths⟩
    apply lt_of_le_of_lt _ hcb
    refine iSup_le fun y => iSup_le fun hy => ?_
    obtain ⟨p, hpU, hp⟩ := hpaths y hy
    exact (iInf_le_of_le p (iInf_le _ hpU)).trans hp

/-- Uniform obstacle-avoiding paths inside the radius-six ball supply the
first strict internal-metric inequality in the strengthened pinch event. -/
theorem pinchFirstInternalBound_of_uniform_paths
    (D : ℂ → ℂ → ℝ) (Q' Q W : Set ℂ) (δ : ℝ)
    (h : ∃ c : ℝ≥0∞, c < ENNReal.ofReal (setDist D Q' (frontier Q)) ∧
      ∀ y ∈ sphere (0 : ℂ) 5, ∃ p : Path 0 y,
        (∀ t, p t ∈ (thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) ∧
        pathLength D p ≤ c) :
    (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D (ball 0 6) 0 y) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) := by
  apply pinchFirstInternalBound_of_constrained_paths D Q' Q W δ
  exact (iSup_internalMetric_lt_iff_exists_uniform_paths D _ _ _ _).2 h

end HarmonicBalls
