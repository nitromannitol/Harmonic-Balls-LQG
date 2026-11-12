import HarmonicBalls.FirstPass.LPBridge.BallMassBounds
import LatticeProb.LQG.LQGBallMassBoundsHolds

/-!
# The Ding-Gwynne ball-mass bounds of the whole-plane LQG measure hold

The input `WholePlaneLQGBallMassBounds` (Ding-Gwynne, arXiv:1807.01072, Lemma 3.8; positive and negative moments of
the LQG mass of Euclidean balls, uniformly in the centre and the radius) is the bound
`LatticeProb.LQG.WholePlaneLQGBallMassBoundsLP` of the library, proved there for every `γ` and every model of the
whole-plane GFF (`LatticeProb.LQG.wholePlaneLQGBallMassBoundsLP_holds`), transported through the bridge
`wholePlaneLQGBallMassBounds_of_LP` (`FirstPass/LPBridge/BallMassBounds.lean`).

`wholePlaneLQGBallMassBounds_holds` has exactly the binder shape `hDG` of the counted forms.
-/

open MeasureTheory

universe u

namespace HarmonicBalls

/-- The ball-mass bounds `WholePlaneLQGBallMassBounds` hold for every `Type u` model of the whole-plane GFF and every
`γ` (the binder `hDG` of the counted forms). -/
theorem wholePlaneLQGBallMassBounds_holds :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc :=
  wholePlaneLQGBallMassBounds_forall_of_LP
    (fun _ _ P γ hC hcirc => LatticeProb.LQG.wholePlaneLQGBallMassBoundsLP_holds P γ hC hcirc)

end HarmonicBalls
