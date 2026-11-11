import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstLawTransfer
import HarmonicBalls.Steps.Sec11.PinchProofAssembly

/-! # Assembly from the open-corridor pinch certificate -/

namespace HarmonicBalls
open MeasureTheory Metric Set
open scoped ENNReal

/-- The open-corridor certificate supplies both the first auxiliary event
and the constrained-path bound used by the strengthened pinch event. -/
theorem correctedOpenFirstCertificate.constrained_paths
    {D : ℂ → ℂ → ℝ} {W T Q' Q : Set ℂ} {δ : ℝ}
    (h : correctedOpenFirstCertificate D W T Q' Q δ) :
    (⨆ y ∈ sphere (0 : ℂ) 5,
      internalMetric D ((thickening (2 * δ) (Q ∪ W))ᶜ ∩ ball 0 6) 0 y) <
        ENNReal.ofReal (setDist D Q' (frontier Q)) := by
  apply lt_of_le_of_lt ?_ h.1
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  apply le_iSup_of_le y
  apply le_iSup_of_le hy
  apply internalMetric_anti
  intro x hx
  refine ⟨?_, hx.1⟩
  rw [thickening_union]
  intro hmem
  exact hx.2 (hmem.elim (fun hq => Or.inl (subset_closure hq))
    (fun hw => Or.inr (subset_closure hw)))

/-- The three auxiliary certificates imply the strengthened local pinch
event, with no additional constrained-path assumption. -/
theorem IsPinchPointProofConfiguration.pinchPointEventWithInternalBounds_of_open_first
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ)
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (μ : Measure ℂ) (M : ℝ)
    (hfirst : correctedOpenFirstCertificate D W T Q' Q δ)
    (hsecond : pinchSecondEvent μ D U V δ M)
    (hthird : pinchThirdEvent D V W δ) :
    HarmonicBalls.pinchPointEventWithInternalBounds μ D U T Q' Q M 1 0 := by
  have hnonneg (x y : ℂ) : 0 ≤ D x y := by
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  have hpaths := hfirst.constrained_paths
  have hf : pinchFirstEvent D W T Q' Q δ := by
    refine ⟨?_, hfirst.2⟩
    apply lt_of_le_of_lt ?_ hpaths
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le y (le_iSup_of_le hy (internalMetric_anti D inter_subset_left 0 y))
  exact h.pinchPointEventWithInternalBounds hD hnonneg μ M hf hsecond hthird hpaths

end HarmonicBalls
