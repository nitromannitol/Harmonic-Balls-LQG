import HarmonicBalls.FirstPass.S11ab
import HarmonicBalls.FirstPass.S11ag
import HarmonicBalls.FirstPass.Frozen.S11d

/-! # Shifted clause of the metric and pair event certificates (fp-S11aj)

The shifted clause `hshift` of `metric_event_transfer_of_rule` (`FirstPass/S11ab.lean`) and its pair version for
`MetricMeasureEventCertificateStmt` (`FirstPass/S11ag.lean`), for the shifted field `h^C + f` of a smooth compactly
supported `f` with zero unit-circle average. Route (Lh answer `notes/fp-gaps/CHATGPT-lh-R4-R5.md`, §R4 and its pair
follow-up): a Cameron-Martin reweighting `P'` of the GFF, and a two-copy model on `Ω ⊕ Ω` with the mixture
`½ P.map inl + ½ P'.map inr`, to which the universally quantified certificate is applied once.
-/

namespace HarmonicBalls.S11aj

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- Named input, not an External or Proposed Prop; a form the Cameron-Martin reweighting must supply (pending operator
staging). The Cameron-Martin theorem for the whole-plane GFF (Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2,
Proposition 2.9, printed p. 49, Gaussian tilting): for every whole-plane GFF `(P, hC, hcirc)` and every smooth compactly
supported `f` with zero unit-circle average, there is a measure `P'` equivalent to `P` under which the shifted pairings
`addFunPairing (hC ω) f` and the shifted circle averages `hcirc ω r z + Av_{∂B_r(z)} f` form a whole-plane GFF.

Why this is a named hypothesis and not a consequence of `CameronMartinGFFMutualAbsCont` (`Frozen/S11d.lean:74`): that
frozen input gives only equality of null sets for events of `distributionMeasurableSpace`, i.e. for pairings. A
Radon-Nikodym density `dP'/dP` that makes the circle averages GFF-distributed needs equivalence of the joint laws of
`(hC, hcirc)` and `(hC + f, hcirc + Av f)`, and the circle averages are not `distributionMeasurableSpace`-measurable
functions of `hC` (no input supplies that). -/
def CameronMartinGFFReweighting : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
    HasCompactSupport f → Real.circleAverage f 0 1 = 0 →
    ∃ P' : Measure Ω, P' ≪ P ∧ P ≪ P' ∧
      IsWholePlaneGFF P' (fun ω => addFunPairing (hC ω) f)
        (fun ω r z => hcirc ω r z + Real.circleAverage f z r)

end HarmonicBalls.S11aj
