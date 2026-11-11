import HarmonicBalls.FirstPass.S11aa
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# Universe transfer of the whole-plane GFF existence clause (Phase 2)

`WholePlaneGFFExistsFrozen.{u}` (`FirstPass/S11r/Frozen.lean:37`) asserts that a whole-plane Gaussian
free field `IsWholePlaneGFF P hC hcirc` (Duplantier-Sheffield arXiv:0808.1560 §3.1, Miller-Sheffield
arXiv:1302.4738 §2.2.1, Bou-Rabee-Gwynne arXiv:2208.11795 §2.1) exists on a probability space `Ω : Type u`.
This file proves the universe transfer: an existence witness in `Type 0` yields one in `Type u`, by the
`ULift` pushforward of the probability measure. The transfer is a deduction, and needs no input.

The existence of a witness in `Type 0` itself is not in this file (see the report of the round).
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Set ProbabilityTheory
open FirstPassS11aa

/-- Universe transfer (route `notes/fp-gaps/CHATGPT-hb-frozen-truth-S11r-S11j.md` §1.4): a whole-plane GFF on a
probability space in `Type 0` gives one on `ULift Ω : Type u`, namely `P.map ULift.up`, with the pairings and the
circle averages composed with `ULift.down`. Every clause of `IsWholePlaneGFF` transfers: the pairings and circle
averages are measurable through `ULift.down`; the Gaussian laws of finite families, the centering and the covariance
transfer along the measure-preserving pushforward (`hasGaussianLaw_map_of_comp`, `integral_map_of_measurable`,
`covariance_map_of_ae`); the a.s. continuity transfers along the measurable embedding `ULift.up`. -/
theorem wholePlaneGFFExists_ulift (h : WholePlaneGFFExistsFrozen.{0}) : WholePlaneGFFExistsFrozen.{u} := by
  obtain ⟨Ω, mΩ, P, hP, hC, hcirc, hG⟩ := h
  have hS : Measurable (ULift.up : Ω → ULift.{u} Ω) := measurable_up
  have hE : MeasurableEmbedding (ULift.up : Ω → ULift.{u} Ω) :=
    MeasurableEquiv.ulift.symm.measurableEmbedding
  have hmeas : ∀ o : GFFObservable, o.IsAdmissible →
      Measurable fun ω' : ULift.{u} Ω => o.eval (hC ω'.down) (hcirc ω'.down) := by
    intro o ho
    cases o with
    | pairing φ => exact (hG.measurable_pairing φ ho).comp measurable_down
    | circle r z => exact (hG.measurable_circle r z ho).comp measurable_down
  refine ⟨ULift.{u} Ω, inferInstance, P.map ULift.up, inferInstance,
    fun ω' => hC ω'.down, fun ω' => hcirc ω'.down, ?_⟩
  refine
    { measurable_pairing := fun φ hφ => (hG.measurable_pairing φ hφ).comp measurable_down
      measurable_circle := fun r z hr => (hG.measurable_circle r z hr).comp measurable_down
      isGaussianProcess := ?_
      integral_eq_zero := fun o ho => ?_
      covariance_eq := fun o o' ho ho' => ?_
      ae_continuousOn_circle := ?_ }
  · refine ⟨fun I => hasGaussianLaw_map_of_comp hS ?_ (hG.isGaussianProcess.hasGaussianLaw I)⟩
    exact Measurable.of_eval fun i : I => hmeas i.1.1 i.1.2
  · rw [integral_map_of_measurable hS (hmeas o ho)]
    exact hG.integral_eq_zero o ho
  · exact (covariance_map_of_ae hS (hmeas o ho) (hmeas o' ho')
      (X := fun ω => o.eval (hC ω) (hcirc ω)) (Y := fun ω => o'.eval (hC ω) (hcirc ω))
      (Filter.Eventually.of_forall fun _ => rfl) (Filter.Eventually.of_forall fun _ => rfl)).trans
      (hG.covariance_eq o o' ho ho')
  · exact hE.ae_map_iff.2 hG.ae_continuousOn_circle

end HarmonicBalls
