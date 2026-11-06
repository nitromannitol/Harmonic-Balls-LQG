import HarmonicBalls.Proofs.Sec6.AnnulusMassSandwich
import HarmonicBalls.Proofs.Sec6.NearbyAnnulusWitness

/-! # A displacement criterion for good annuli

The mass condition uses concentric annular envelopes. The Brownian comparison
is stated explicitly and must be estimated separately at the relevant scales.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric MarkovProcess
open scoped ENNReal

/-- A displaced annulus is good if the mass of an explicit concentric collar
fits the threshold slack and the extended witness satisfies the indicated
Brownian avoidance comparison. The displacement bound is the prescribed `δ`;
no continuity or small-scale rate is assumed. -/
theorem isGoodAnnulus_of_concentric_collar_and_avoidance
    (μ : Measure ℂ) (z : ℂ) {r δ a a' b b' : ℝ} (hδ : 0 < δ)
    (hgood : IsGoodAnnulus μ r z a b)
    (hmass : ENNReal.ofReal a' * μ (annulus z (3*r-δ) (5*r+δ)) +
        μ (annulus z (3*r-δ) (5*r+δ) \ annulus z (3*r+δ) (5*r-δ)) ≤
      ENNReal.ofReal a * μ (annulus z (3*r) (5*r)))
    (c : ℝ≥0∞) (hbc : ENNReal.ofReal b + c ≤ ENNReal.ofReal b')
    (hcompare : ∀ w : ℂ, dist w z < δ → ∀ Y : Set ℂ, MeasurableSet Y →
      Y ⊆ annulus w (3*r) (5*r) → ∀ u ∈ sphere w (4*r),
      ∃ v ∈ sphere z (4*r),
        planarBrownianMotion u {p | ContinuousPath.exitTime (annulus w (3*r) (5*r)) p ≤
          ContinuousPath.exitTime Y p} ≤
        planarBrownianMotion v {p | ContinuousPath.exitTime (annulus z (3*r) (5*r)) p ≤
          ContinuousPath.exitTime ((annulus z (3*r) (5*r) ∩ Y) ∪
            (annulus z (3*r) (5*r) \ annulus w (3*r) (5*r))) p} + c) :
    ∀ w : ℂ, dist w z < δ → IsGoodAnnulus μ r w a' b' := by
  intro w hw Y hY hYsub hYmass u hu
  let A := annulus z (3*r) (5*r)
  let B := annulus w (3*r) (5*r)
  let O := annulus z (3*r-δ) (5*r+δ)
  let I := annulus z (3*r+δ) (5*r-δ)
  have hB : B ⊆ O := (annulus_nearby_center_sandwich hw).2
  have hI : I ⊆ B := (annulus_nearby_center_sandwich hw).1
  have hA : A ⊆ O := (annulus_nearby_center_sandwich (show dist z z < δ by simpa using hδ)).2
  have hdiff : A \ B ⊆ O \ I := by
    intro x hx
    exact ⟨hA hx.1, fun hi => hx.2 (hI hi)⟩
  have hXm : μ ((A ∩ Y) ∪ (A \ B)) ≤ ENNReal.ofReal a * μ A := by
    calc
      _ ≤ μ (A ∩ Y) + μ (A \ B) := measure_union_le _ _
      _ ≤ μ Y + μ (O \ I) := add_le_add (measure_mono inter_subset_right) (measure_mono hdiff)
      _ ≤ ENNReal.ofReal a' * μ O + μ (O \ I) :=
        add_le_add (hYmass.trans (by gcongr)) le_rfl
      _ ≤ _ := hmass
  have hAm : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hBm : MeasurableSet B := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hX : MeasurableSet ((A ∩ Y) ∪ (A \ B)) := (hAm.inter hY).union (hAm.diff hBm)
  have hXA : (A ∩ Y) ∪ (A \ B) ⊆ A := union_subset inter_subset_left sdiff_subset
  obtain ⟨v, hv, hvbound⟩ := hcompare w hw Y hY hYsub u hu
  exact hvbound.trans ((add_le_add (hgood _ hX hXA hXm v hv) le_rfl).trans hbc)

end HarmonicBalls.Section6
