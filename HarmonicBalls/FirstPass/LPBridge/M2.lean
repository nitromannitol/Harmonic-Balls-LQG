import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.S8c.TorusTail
import HarmonicBalls.FirstPass.S8c.LocalObservation
import HarmonicBalls.Proofs.Sec8.PhaseTorus
import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import HarmonicBalls.Proofs.Sec11.PinchRootedKernel
import HarmonicBalls.LPStage.PhaseTorus
import HarmonicBalls.LPStage.LocalObservation

/-!
# Bridge to the staged phase-torus and local-observation definitions

Each staged definition of `LatticeProb.Prob` (files `HarmonicBalls/LPStage/PhaseTorus.lean` and
`HarmonicBalls/LPStage/LocalObservation.lean`) is the same object as the corresponding `HarmonicBalls` definition:
the bodies agree, so each equality holds by `rfl`. The staged names differ from the `HarmonicBalls` names only for
`PhaseTorusDoublingProductErgodicFrozen`, renamed `PhaseTorusDoublingProductErgodic`.

Not bridged: the definitions `localRadius`, `localDomain`, `localRootObservation`, `localReferenceObservation`,
`localRootKernel`, and `dmsShift`, `dmsConstant`, `dmsShiftedPairing` (not staged, see the report).
-/

universe u

namespace HarmonicBalls.LPBridge

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem phaseCircle_eq : HarmonicBalls.PhaseCircle = LatticeProb.Prob.PhaseCircle := rfl

theorem phaseTorus_eq : HarmonicBalls.PhaseTorus = LatticeProb.Prob.PhaseTorus := rfl

theorem phaseTorusDouble_eq : HarmonicBalls.phaseTorusDouble = LatticeProb.Prob.phaseTorusDouble := rfl

theorem phaseTorusFieldMeasure_eq {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) :
    HarmonicBalls.phaseTorusFieldMeasure P = LatticeProb.Prob.phaseTorusFieldMeasure P := rfl

theorem phaseTorusDoublingProductErgodic_eq :
    HarmonicBalls.PhaseTorusDoublingProductErgodicFrozen.{u} =
      LatticeProb.Prob.PhaseTorusDoublingProductErgodic.{u} := rfl

theorem recenteredRestriction_eq (η : Measure ℂ) (r : ℝ) (z : ℂ) :
    HarmonicBalls.recenteredRestriction η r z = LatticeProb.Prob.recenteredRestriction η r z := rfl

theorem massNormalize_eq (r : ℝ) (η : Measure ℂ) :
    HarmonicBalls.massNormalize r η = LatticeProb.Prob.massNormalize r η := rfl

theorem normalizedRestriction_eq (μ : Measure ℂ) (U : Set ℂ) :
    HarmonicBalls.normalizedRestriction μ U = LatticeProb.Prob.normalizedRestriction μ U := rfl

theorem normalizedRestrictionKernel_eq (A : Set ℂ) (hA : MeasurableSet A) :
    HarmonicBalls.normalizedRestrictionKernel A hA = LatticeProb.Prob.normalizedRestrictionKernel A hA := rfl

theorem weightedRestrictionKernel_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (B : Set ℂ) (hB : MeasurableSet B)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    HarmonicBalls.weightedRestrictionKernel P μ hμ B hB w hw =
      LatticeProb.Prob.weightedRestrictionKernel P μ hμ B hB w hw := rfl

end HarmonicBalls.LPBridge
