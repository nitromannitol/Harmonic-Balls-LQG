import HarmonicBalls.Steps.Sec4.GreenPotentialBallHolderStep
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-!
# Gap G4 discharged: `GreenPotentialBallHolderStep` from `VolumeGrowth.greenPotential_ball_holder`

The step of Steps/Sec4/GreenPotentialBallHolderStep.lean is verbatim the quantitative Hölder bound for Green
potentials on a disc proved in Proofs/Potential/GreenPotentialHolder.lean. This file must not be imported together
with Steps/SecA (name clash on `continuousOn_greenFunction_ball`, see the step file).
-/

namespace HarmonicBalls

/-- **Step G4 holds** (`VolumeGrowth.greenPotential_ball_holder`). -/
theorem greenPotentialBallHolderStep : GreenPotentialBallHolderStep :=
  fun _ hμ _ _ _ hR hV => @VolumeGrowth.greenPotential_ball_holder _ hμ _ _ _ hR hV

end HarmonicBalls
