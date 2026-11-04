import HarmonicBalls.Proofs.Sec10.IntermediateFrontierCrossings
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! # Frontier length forced by multiple annular crossings -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal MeasureTheory

/-- A set meeting every intermediate circle has one-dimensional Hausdorff
measure at least the width of the annulus, already within that annulus. -/
theorem hausdorffMeasure_one_inter_annulus_ge_of_meets_spheres
    {F : Set ℂ} {w : ℂ} {r R : ℝ}
    (h : ∀ s ∈ Ioo r R, (sphere w s ∩ F).Nonempty) :
    ENNReal.ofReal (R - r) ≤
      μH[1] (F ∩ {x | r < dist x w ∧ dist x w < R}) := by
  let S : Set ℂ := F ∩ {x | r < dist x w ∧ dist x w < R}
  have hsub : Ioo r R ⊆ (fun x : ℂ => dist x w) '' S := by
    intro s hs
    obtain ⟨x, hxs, hxF⟩ := h s hs
    have heq : dist x w = s := by simpa [mem_sphere, dist_eq_norm] using hxs
    refine ⟨x, ⟨hxF, ?_⟩, heq⟩
    simpa [heq] using hs
  have hmeasure := (LipschitzWith.dist_left w).hausdorffMeasure_image_le (d := 1)
    (by norm_num) S
  have hmono : (μH[1] : Measure ℝ) (Ioo r R) ≤ μH[1] ((fun x : ℂ => dist x w) '' S) :=
    measure_mono hsub
  rw [hausdorffMeasure_real, Real.volume_Ioo] at hmono
  simpa [S] using hmono.trans (by simpa using hmeasure)

/-- If an open set has multiple crossing components, the part of its frontier
inside the annulus has Hausdorff length at least the annulus width. -/
theorem hausdorffMeasure_one_frontier_inter_annulus_ge_of_multiple_crossings
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hcount : 1 < (crossingComponents (G ∩ ball w R) w r R).encard) :
    ENNReal.ofReal (R - r) ≤
      μH[1]
        (frontier G ∩ {x | r < dist x w ∧ dist x w < R}) := by
  apply hausdorffMeasure_one_inter_annulus_ge_of_meets_spheres
  intro s hs
  by_contra h
  have hdis : Disjoint (sphere w s) (frontier G) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
  exact (not_le_of_gt hcount)
    (encard_crossingComponents_le_one_of_disjoint_intermediate_sphere_frontier
      hG hr hs.1 hs.2 hdis)

/-- A frontier shorter than the annulus width permits at most one crossing
component, without any restriction on the location of the pole. -/
theorem encard_crossingComponents_le_one_of_frontier_hausdorffMeasure_lt
    {G : Set ℂ} (hG : IsOpen G) {w : ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hshort : μH[1] (frontier G ∩ {x | r < dist x w ∧ dist x w < R}) <
      ENNReal.ofReal (R - r)) :
    (crossingComponents (G ∩ ball w R) w r R).encard ≤ 1 := by
  apply le_of_not_gt
  intro hcount
  exact (not_le_of_gt hshort)
    (hausdorffMeasure_one_frontier_inter_annulus_ge_of_multiple_crossings hG hr hcount)

end HarmonicBalls
