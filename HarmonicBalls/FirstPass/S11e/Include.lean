import HarmonicBalls.Steps.Sec11.PinchProofAssembly
import HarmonicBalls.Steps.Sec11.PinchInternalDiam
import HarmonicBalls.Steps.Sec11.PinchRadialCrossing

/-!
# Deterministic inclusion: the three auxiliary pinch events give the pinch-point event (fp-S11e, owner n2)

For a pinch-point proof configuration (`IsPinchPointProofConfiguration`, `Draft/Section11.lean`) the auxiliary events
`Ẽ₁`, `Ẽ₂(M)`, `Ẽ₃` (`pinchFirstEvent`, `pinchSecondEvent`, `pinchThirdEvent`; paper lines 3325-3357) together imply the
pinch-point event `Ĝ₁(0; M)` (`pinchPointEvent ... M 1 0`, paper eq:pinch-point-event, line 3124).

This is the deterministic part of paper Lemma `s11-pinch:lem:include` (lines 3637-3657), in the Draft form with the global
metric `D` in the conclusion. The clauses are: `sup_{∂B₅} D(0,·) < L` from `Ẽ₁` with the internal metric on the complement of
`B_{2δ}(Q ∪ W)` (which dominates `D`); `D(0, ∂B₅) > diam T` from the radial crossing bound (`pinch_radial_crossing`) and the
three internal diameters (`pinchSecondInternalBound_of_auxiliary_events`, Steps/Sec11); the third clause is `Ẽ₂`.
Uses only `IsEuclideanLengthMetric` and the configuration fields; no probability.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- Monotonicity of a set-indexed supremum in `ℝ≥0∞`, pointwise on the index set. -/
theorem biSup_le_biSup_of_le {s : Set ℂ} {f g : ℂ → ℝ≥0∞} (h : ∀ x ∈ s, f x ≤ g x) :
    (⨆ x ∈ s, f x) ≤ ⨆ x ∈ s, g x :=
  iSup₂_le fun x hx => (h x hx).trans (le_iSup₂ (f := fun x (_ : x ∈ s) => g x) x hx)

/-- `Ẽ₁ ∩ Ẽ₂(M) ∩ Ẽ₃` implies `Ĝ₁(0; M)` in the Draft (global metric) form. Paper lines 3637-3657 (`lem:include`). -/
theorem pinchPointEvent_of_auxiliary_events
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (μ : Measure ℂ) (M : ℝ)
    (hfirst : pinchFirstEvent D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent D V W δ) :
    pinchPointEvent μ D U T Q' Q M 1 0 := by
  have hres (A : Set ℂ) : rescaledSet A 1 0 = A := by simp [rescaledSet]
  obtain ⟨hclA, hclB, hclC, hsubA, hsubB, hsubC⟩ := h.auxiliary_piece_containments
  have hδ : 0 ≤ δ := h.δ₀_mem.1.le
  have hδ5 : 3 * δ ≤ 5 := by
    have := h.δ₀_mem.2
    linarith
  have h2 := pinchSecondInternalBound_of_auxiliary_events hD hnonneg μ U V W T Q' Q δ M
    hfirst hsecond hthird hclA hclB hclC hsubA hsubB hsubC
    h.outer_auxiliary_pieces_meet h.inner_auxiliary_pieces_meet
    (hD.pinch_radial_crossing hnonneg hδ hδ5)
  have hle1 : (⨆ x ∈ sphere (0 : ℂ) 5, ENNReal.ofReal (D 0 x)) ≤
      ⨆ x ∈ sphere (0 : ℂ) 5, internalMetric D (thickening (2 * δ) (Q ∪ W))ᶜ 0 x :=
    biSup_le_biSup_of_le fun x _ => by
      rw [hD.ofReal_eq_internalMetric]
      exact internalMetric_anti D (subset_univ _) 0 x
  have hle2 : (⨆ x ∈ T, ⨆ y ∈ T, ENNReal.ofReal (D x y)) ≤
      ⨆ x ∈ T, ⨆ y ∈ T, internalMetric D (ball 0 6) x y :=
    biSup_le_biSup_of_le fun x _ => biSup_le_biSup_of_le fun y _ => by
      rw [hD.ofReal_eq_internalMetric]
      exact internalMetric_anti D (subset_univ _) x y
  have hclause1 : (⨆ x ∈ sphere (0 : ℂ) 5, ENNReal.ofReal (D 0 x)) <
      ENNReal.ofReal (setDist D Q' (frontier Q)) := lt_of_le_of_lt hle1 hfirst.1
  have hclause2 : (⨆ x ∈ T, ⨆ y ∈ T, ENNReal.ofReal (D x y)) <
      ENNReal.ofReal (setDist D {0} (sphere 0 5)) := lt_of_le_of_lt hle2 h2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pinchPointEvent, mul_one, hres] using hclause1
  · simpa only [pinchPointEvent, mul_one, hres] using hclause2
  · simpa only [pinchPointEvent, mul_one, hres] using hsecond.2

#print axioms pinchPointEvent_of_auxiliary_events

end HarmonicBalls
