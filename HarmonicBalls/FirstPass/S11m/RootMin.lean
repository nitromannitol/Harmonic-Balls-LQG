import HarmonicBalls.Steps.Sec11.PuncturedPathLength
import HarmonicBalls.FirstPass.S11m.RootCut

/-!
# Internal distance through the origin (fp-S11m, owner z4)

Route `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` eq. (16) (lines 355-377): for an open-or-not set `O` and points
`x, y ≠ 0`, a competitor path either avoids `0` (and is then a path of `O \ {0}`) or hits `0` (and is then a concatenation of
a path from `x` to `0` and a path from `0` to `y`). Hence

  `D(x, y; O) = min (D(x, y; O \ {0})) (D(x, 0; O) + D(0, y; O))`.

No point-removal property is assumed (route: "We never assume that removing a point preserves distances").
Deterministic; input: a Euclidean length metric `D`.
-/

namespace HarmonicBalls.S11m

open Set Metric Filter Topology
open scoped ENNReal unitInterval

/-- **Internal distance through the origin** (route eq. (16)). For `x, y ≠ 0`:
`D(x, y; O) = min (D(x, y; O \ {0})) (D(x, 0; O) + D(0, y; O))`. -/
theorem internalMetric_eq_min_punctured {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (O : Set ℂ) {x y : ℂ} :
    internalMetric D O x y = min (internalMetric D (O \ {0}) x y) (internalMetric D O x 0 + internalMetric D O 0 y) := by
  apply le_antisymm
  · exact le_min (internalMetric_anti D sdiff_subset x y) (IsEuclideanLengthMetric.internalMetric_triangle hD O x 0 y)
  · show _ ≤ ⨅ (P : Path x y) (_ : ∀ t, P t ∈ O), pathLength D P
    refine le_iInf₂ fun P hP => ?_
    by_cases h : ∃ t, P t = 0
    · obtain ⟨t0, ht0⟩ := h
      have h1 : x = P 0 := P.source.symm
      have h2 : (0 : ℂ) = P t0 := ht0.symm
      have h4 : y = P 1 := P.target.symm
      have hA : internalMetric D O x 0 ≤ pathLength D ((P.subpath 0 t0).cast h1 h2) :=
        iInf₂_le (f := fun (Q : Path x 0) (_ : ∀ t, Q t ∈ O) => pathLength D Q) _ (fun t => hP _)
      have hB : internalMetric D O 0 y ≤ pathLength D ((P.subpath t0 1).cast h2 h4) :=
        iInf₂_le (f := fun (Q : Path 0 y) (_ : ∀ t, Q t ∈ O) => pathLength D Q) _ (fun t => hP _)
      have hsplit := IsEuclideanLengthMetric.pathLength_initial_add_final_le hD P t0 t0 le_rfl
      exact le_trans (le_trans (min_le_right _ _) (add_le_add hA hB)) hsplit
    · refine le_trans (min_le_left _ _) ?_
      exact iInf₂_le (f := fun (Q : Path x y) (_ : ∀ t, Q t ∈ O \ {0}) => pathLength D Q) P
        (fun t => ⟨hP t, fun h0 => h ⟨t, h0⟩⟩)

end HarmonicBalls.S11m
