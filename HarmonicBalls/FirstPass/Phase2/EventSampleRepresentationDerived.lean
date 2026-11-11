import HarmonicBalls.FirstPass.Phase2.CameronMartinEventTransferDerived
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2

/-!
# Cameron-Martin event transfer, reduced to the event sample representation (phase 2, worker z7)

Row 17 target: `CameronMartinEventTransferFrozen` (`FirstPass/Frozen/S11c.lean:149`).

Route (`notes/fp-gaps/MATH-ANSWERS.md`, MQ-lh-19, lines 282-303): the event sample representation
`CMEventTransfer.EventSampleRepresentation` (`FirstPass/Phase2/CameronMartinEventTransferDerived.lean:60`) is the step that
needs the metric inputs. The Cameron-Martin reweighting `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:33`) is
discharged by its derived theorem `S11aj.cameronMartinGFFReweighting_derived`
(`FirstPass/Phase2/CameronMartinReweightingDerived2.lean:267`).

This file proves the reduction: the frozen event transfer follows from the representation alone. The representation itself is
not derived here (BLOCKED-STEP, see the report).
-/

namespace HarmonicBalls

universe u

/-- **Row 17, reduction.** The frozen Cameron-Martin event transfer, with the Cameron-Martin reweighting discharged by
`S11aj.cameronMartinGFFReweighting_derived`. The only remaining premise is the named representation
`CMEventTransfer.EventSampleRepresentation` (BLOCKED-STEP, MQ-lh-19). -/
theorem cameronMartinEventTransfer_derived_of_representation
    (hRep : CMEventTransfer.EventSampleRepresentation.{u}) :
    CameronMartinEventTransferFrozen.{u} :=
  CMEventTransfer.cameronMartinEventTransfer_of_representation hRep
    HarmonicBalls.S11aj.cameronMartinGFFReweighting_derived

end HarmonicBalls
