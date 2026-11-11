import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Phase2.AxiomsUnivDerived

/-!
# Axiom I (Euclidean length metric) of the LQG metric, universe-lifted and derived

The frozen clause `LQGMetricLengthUnivFrozen` (`FirstPass/Frozen/S11j.lean:133`) asks that, for every
γ-LQG metric `𝔇` (`IsLQGMetric`) and every whole-plane GFF `h^ℂ` on a probability space `Ω : Type u`,
the metric `𝔇(h^ℂ)` is almost surely a Euclidean length metric: axiom I of Fact 2.2 of
Bou-Rabee-Gwynne (arXiv:2208.11795), at no insertion.

It follows from the universe-lifted axiom package `lqgMetricSatisfiesAxiomsUniv_derived`
(`Phase2/AxiomsUnivDerived.lean`, no hypotheses) at the zero continuous shift `f = 0`, where
`addFunPairing (hC ω) 0 = hC ω` (`FirstPassS11aa.addFunPairing_zero_fun`). No new input is used.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter Set
open FirstPassS11aa

/-- Axiom I of Fact 2.2 (Gwynne-Miller arXiv:1905.00383, Section 1.2, p. 6; Bou-Rabee-Gwynne arXiv:2208.11795,
Fact 2.2 I), for probability spaces in `Type u` and with no insertion: for every γ-LQG metric `𝔇` with Weyl
exponent `ξ` (`IsLQGMetric γ ξ 𝔇`) and every whole-plane GFF `hC` (`IsWholePlaneGFF P hC hcirc`), almost surely
`𝔇 (hC ω)` is a Euclidean length metric (`IsEuclideanLengthMetric`).
Derived with no binder: specialize `lqgMetricSatisfiesAxiomsUniv_derived` to the zero shift `f = 0`, then pull
the almost sure clause I back along `addFunPairing (hC ω) 0 = hC ω`. The bounds `0 < γ < 2` are not used. -/
theorem lqgMetricLengthUniv_derived : LQGMetricLengthUnivFrozen.{u} := by
  intro γ ξ 𝔇 _ _ hLQG Ω _ P hC hcirc hGFF
  have hS := lqgMetricSatisfiesAxiomsUniv_derived.{u} γ ξ 𝔇 hLQG Ω P hC hcirc (fun _ _ => (0 : ℝ))
    hGFF (fun _ => continuous_const) (fun _ => measurable_const)
  filter_upwards [hS.ae_isEuclideanLengthMetric] with ω hω
  have h0 : addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := addFunPairing_zero_fun (hC ω)
  have hω' : IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) (fun _ => (0 : ℝ)))) := hω
  rwa [h0] at hω'

end HarmonicBalls
