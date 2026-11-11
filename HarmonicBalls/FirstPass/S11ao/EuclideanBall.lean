import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthTransport

/-!
# Euclidean reference metric on a convex open set

For a convex open set `B ⊆ ℂ` (in particular a disc `ball c R`) the Euclidean distance `dist` is the
internal metric of `B`: the segment joining two points of `B` lies in `B` and has `dist`-length `dist z w`,
and every path from `z` to `w` has length at least `dist z w`. Hence `IsLengthMetricOn B (fun z w => dist z w)`
(`FirstPassS11ah.IsLengthMetricOn`, LengthTransport.lean). This is the fixed reference metric used off the good
set in `FirstPassS11ao` (`S11ao.lean`).
-/

open Metric Set Filter Topology HarmonicBalls
noncomputable section

open scoped ENNReal

namespace FirstPassS11ao

/-- **Euclidean internal metric on a convex set.** For a convex `B ⊆ ℂ` and `z, w ∈ B`, the internal metric of
the Euclidean distance in `B` is `|z - w|` (Armitage-Gardiner-style: the straight segment is a length-minimising
path; the bound `|z - w| ≤ len(P)` holds for every path). Proof as `internalMetric_dist_univ`
(LQGMetric.lean), with the segment now required to lie in `B`. -/
theorem internalMetric_dist_of_convex {B : Set ℂ} (hB : Convex ℝ B) {z w : ℂ} (hz : z ∈ B) (hw : w ∈ B) :
    internalMetric (fun z w => dist z w) B z w = ENNReal.ofReal (dist z w) := by
  apply le_antisymm
  · have hseg : ∀ t, Path.segment z w t ∈ B := fun t => by
      have ht : Path.segment z w t ∈ Set.range (Path.segment z w) := ⟨t, rfl⟩
      rw [Path.range_segment] at ht
      exact hB.segment_subset hz hw ht
    refine (iInf₂_le (Path.segment z w) hseg).trans ?_
    rw [pathLength, curveLength_dist, eVariationOn.eq_of_eqOn (Path.eqOn_extend_segment z w)]
    have hL : LipschitzWith (nndist z w) (AffineMap.lineMap z w : ℝ → ℂ) :=
      lipschitzWith_lineMap z w
    calc eVariationOn (AffineMap.lineMap z w : ℝ → ℂ) (Icc 0 1)
        = eVariationOn ((AffineMap.lineMap z w : ℝ → ℂ) ∘ id) (Icc 0 1) := rfl
      _ ≤ nndist z w * eVariationOn (id : ℝ → ℝ) (Icc 0 1) :=
          (hL.lipschitzOnWith (s := univ)).comp_eVariationOn_le (mapsTo_univ _ _)
      _ ≤ nndist z w * ENNReal.ofReal (1 - 0) := by
          gcongr
          simp
      _ = ENNReal.ofReal (dist z w) := by
          rw [sub_zero, ENNReal.ofReal_one, mul_one, ← edist_nndist, edist_dist]
  · refine le_iInf₂ fun P _ => ?_
    rw [pathLength, curveLength_dist]
    have := eVariationOn.edist_le P.extend (s := Icc (0 : ℝ) 1)
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    simpa [edist_dist, dist_comm] using this

/-- **Euclidean reference is a local length metric.** On a convex open set `B ⊆ ℂ`, the Euclidean distance
satisfies `FirstPassS11ah.IsLengthMetricOn B` (metric axioms on `B`, continuity, the `D`-open subsets of `B` are the
Euclidean open ones, and the length property `ofReal (D z w) = internalMetric D B z w`). -/
theorem isLengthMetricOn_dist {B : Set ℂ} (hB : Convex ℝ B) (hBo : IsOpen B) :
    FirstPassS11ah.IsLengthMetricOn B (fun z w => dist z w) where
  self_eq_zero := fun z _ => dist_self z
  eq_of_eq_zero := fun z _ w _ h => dist_eq_zero.1 h
  symm := fun z _ w _ => dist_comm z w
  triangle := fun x _ y _ z _ => dist_triangle x y z
  continuousOn := continuous_dist.continuousOn
  isOpen_iff := by
    intro U hUB
    constructor
    · intro hU z hz
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
      exact ⟨ε, hε, fun w _ hw => hball (by rw [mem_ball, dist_comm]; exact hw)⟩
    · intro h
      rw [Metric.isOpen_iff]
      intro z hz
      obtain ⟨ε, hε, hU⟩ := h z hz
      obtain ⟨δ, hδ, hBδ⟩ := Metric.isOpen_iff.1 hBo z (hUB hz)
      refine ⟨min ε δ, lt_min hε hδ, fun w hw => ?_⟩
      rw [mem_ball] at hw
      have hwB : w ∈ B := hBδ (by rw [mem_ball]; exact lt_of_lt_of_le hw (min_le_right _ _))
      have hd : dist z w < ε := by
        rw [dist_comm]
        exact lt_of_lt_of_le hw (min_le_left _ _)
      exact hU w hwB hd
  ofReal_eq_internalMetric := fun z hz w hw => (internalMetric_dist_of_convex hB hz hw).symm

end FirstPassS11ao

end
