import HarmonicBalls.Proofs.Sec11.CorrectedPinchSetDistMeasurable
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThresholds
import HarmonicBalls.Steps.Sec11.CountableClearanceChains

/-! Measurability of the open-corridor first pinch certificate. -/

namespace HarmonicBalls

open MeasureTheory Metric Set
open scoped ENNReal

/-- For a pointwise measurable family of Euclidean length metrics, the open
corridor certificate is measurable. -/
theorem IsCorrectedPinchConfiguration.measurableSet_open_first_certificate
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hm : ∀ ω, IsEuclideanLengthMetric (D ω)) :
    MeasurableSet {ω |
      (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
        (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
          closure (thickening (2 * δ) W))) 0 y) <
          ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) ∧
      internalDiam (D ω) δ (T \ thickening (3 * δ) W) <
        ENNReal.ofReal (setDist (D ω) {0} (sphere 0 δ))} := by
  let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
    closure (thickening (2 * δ) W))
  let A : Set ℂ := T \ thickening (3 * δ) W
  have hF : IsOpen F := isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hs : sphere (0 : ℂ) 5 ⊆ F :=
    h.sphere_subset_six_component.trans (connectedComponentIn_subset F 0)
  obtain ⟨y, hy⟩ := NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr (by norm_num : (0 : ℝ) ≤ 5)
  have hz : (0 : ℂ) ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, h.sphere_subset_six_component hy⟩
  have hnonneg : ∀ ω x y, 0 ≤ D ω x y := by
    intro ω x y
    have ht := (hm ω).triangle x y x
    rw [(hm ω).self_eq_zero, (hm ω).symm y x] at ht
    linarith
  have hsup := measurable_iSup_internalMetric hF (singleton_subset_iff.mpr hz) hs hm hnonneg
    (fun x hx y _ => measurable_internalMetric_of_lengthMetric hF
      ((singleton_subset_iff.mpr hz) hx) y hD hm)
  have hsub : A ⊆ thickening δ A := self_subset_thickening h.δ₀_mem.1 A
  have hdiam := measurable_iSup_internalMetric isOpen_thickening hsub hsub hm hnonneg
    (fun x hx y _ => measurable_internalMetric_of_lengthMetric isOpen_thickening
      (hsub hx) y hD hm)
  have hQ : Q'.Nonempty := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.isConnected_Q'.nonempty
  have hfront : (frontier Q).Nonempty := by
    have hpos := h.toIsPinchPointProofConfiguration.toIsPinchPointConfiguration.setDist_frontier_pos isEuclideanLengthMetric_dist
    by_contra hn
    have he : frontier Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he, setDist] at hpos
  have hgap := measurable_ofReal_setDist_of_lengthMetric hQ hfront hD hm
  have hroot := measurable_ofReal_setDist_of_lengthMetric (singleton_nonempty (0 : ℂ))
    (NormedSpace.sphere_nonempty (x := (0 : ℂ)) |>.mpr h.δ₀_mem.1.le) hD hm
  have hc := (measurableSet_lt hsup hgap).inter (measurableSet_lt hdiam hroot)
  convert hc using 1
  ext ω
  simp only [mem_inter_iff, mem_ofPred_eq, iSup_singleton, internalDiam, F, A]

#print axioms IsCorrectedPinchConfiguration.measurableSet_open_first_certificate

end HarmonicBalls
