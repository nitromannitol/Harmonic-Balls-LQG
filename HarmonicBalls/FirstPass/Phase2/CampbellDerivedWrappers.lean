import HarmonicBalls.FirstPass.Phase2.CampbellMarkedExt
import HarmonicBalls.FirstPass.Phase2.RootedDominationCanonical

/-!
# Consequences of the marked Campbell identity

`dmsLemmaA10WholePlaneMarkedSub_holds` (CampbellMarkedExt.lean) proves the marked whole-plane form of
Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma A.10 (`D = B₁`, `0 < γ < 2`) for every probability space.
This file feeds it into the conditional theorems that take it as their only remaining input:

* `dmsLemmaA10WholePlaneMarkedSub_forall`: the universally quantified form used as the binder `hSub`;
* `dmsFiniteTiltPos_holds`: the finite-family marked tilt identity `DMSFiniteTiltPosStmt`;
* `dmsLemmaA10WholePlaneMarkedJointPos_holds`: the joint identity on circle profile × mark,
  `DMSLemmaA10WholePlaneMarkedJointPosStmt`;
* `localRootedFieldMeasureDomination_holds`: the rooted field-measure domination `LocalRootedFieldMeasureDomination`
  (FirstPass/Frozen/S8c.lean:51).
-/

open MeasureTheory

namespace HarmonicBalls

universe u

/-- **Lemma A.10 of Duplantier-Miller-Sheffield, marked whole-plane clause, for every probability space.** The
universally quantified form of `dmsLemmaA10WholePlaneMarkedSub_holds`, in the shape of the binder `hSub`. -/
theorem dmsLemmaA10WholePlaneMarkedSub_forall :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ :=
  fun _ _ P γ hC hcirc μ => dmsLemmaA10WholePlaneMarkedSub_holds P γ hC hcirc μ

/-- **The finite-family marked tilt identity.** `DMSFiniteTiltPosStmt` holds: it follows from the marked Campbell
identity by `DMSFiniteTiltPosDerived.dMSFiniteTiltPos_of_sub`. -/
theorem dmsFiniteTiltPos_holds : DMSFiniteTiltPosStmt.{u} :=
  DMSFiniteTiltPosDerived.dMSFiniteTiltPos_of_sub dmsLemmaA10WholePlaneMarkedSub_forall

/-- **The joint marked identity of Lemma A.10.** `DMSLemmaA10WholePlaneMarkedJointPosStmt` holds: under `P(dω) μ_ω(dz)`
restricted to `B₁`, the circle profile and the mark have the law of the DMS-shifted profile under `P ⊗ dz`. It follows
from the marked Campbell identity by `DMSJointPosOfFinite.dMSJointPos_of_sub`. -/
theorem dmsLemmaA10WholePlaneMarkedJointPos_holds : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u} :=
  DMSJointPosOfFinite.dMSJointPos_of_sub dmsLemmaA10WholePlaneMarkedSub_forall

/-- **Rooted field-measure domination.** `LocalRootedFieldMeasureDomination` (FirstPass/Frozen/S8c.lean:51) holds: it
follows from the marked Campbell identity by `localRootedFieldMeasureDomination_of_sub`. -/
theorem localRootedFieldMeasureDomination_holds : LocalRootedFieldMeasureDomination.{u} :=
  localRootedFieldMeasureDomination_of_sub dmsLemmaA10WholePlaneMarkedSub_forall

end HarmonicBalls
