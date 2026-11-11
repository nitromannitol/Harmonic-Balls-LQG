import HarmonicBalls.Draft.Section11
import HarmonicBalls.FirstPass.S11c.GreenTranslate11_7

/-!
# Lemma 11.7, translation covariance of the cone-mass event (deterministic)

For the translate `ν.map (· + z)` of a measure, the cone-mass event at the root `z` (`coneMassEvent`,
Draft/Section11.lean:72) is equivalent to the cone-mass event of `ν` at the root `0`. The proof uses only the bijection
`w ↦ w + z` (`MeasurableEquiv.addRight`, for which `Measure.map` is valid on all sets) and the covariance of the annulus
Green potential (GreenTranslate11_7.lean). No measurability of the cone `Q` is needed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls.S11c

lemma coneAt_zero (Q : Set ℂ) : coneAt Q 0 = Q := by
  simp [coneAt]

/-- The translated annulus and cone: the preimage of `annulus z r (2r) ∩ coneAt Q z` under `w ↦ w + z` is
`annulus 0 r (2r) ∩ Q`. -/
lemma preimage_annulus_cone_add_right (Q : Set ℂ) (z : ℂ) (r : ℝ) :
    (fun w => w + z) ⁻¹' (annulus z r (2 * r) ∩ coneAt Q z) = annulus 0 r (2 * r) ∩ Q := by
  simp only [coneAt]
  rw [Set.preimage_inter, Set.preimage_image_eq _ (add_left_injective z)]
  congr 1
  ext w
  simp [annulus, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm]

/-- **Translation covariance of the cone-mass event.** The event at root `z` for the translated measure is the event
at the origin for the original measure (Draft/Section11.lean:72). -/
theorem coneMassEvent_map_add_right (ν : Measure ℂ) (Q : Set ℂ) (M r : ℝ) (z : ℂ) :
    coneMassEvent (ν.map (fun w => w + z)) Q M r z ↔ coneMassEvent ν Q M r 0 := by
  unfold coneMassEvent
  rw [annulusGreenPotentialSup_map_add_right, coneAt_zero]
  have hT : ν.map (fun w => w + z) = ν.map (MeasurableEquiv.addRight z) := rfl
  rw [hT, MeasurableEquiv.map_apply,
    show (MeasurableEquiv.addRight z) ⁻¹' (annulus z r (2 * r) ∩ coneAt Q z) = annulus 0 r (2 * r) ∩ Q from
      preimage_annulus_cone_add_right Q z r]

end HarmonicBalls.S11c
