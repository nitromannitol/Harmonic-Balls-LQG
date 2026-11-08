import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositiveNull
import HarmonicBalls.Proofs.Sec11.FixedSquareFrontierNull
import HarmonicBalls.Proofs.GFF.MetricXiSign

/-!
# Raw positivity of the fixed corrected configuration with `hfront` and `0 < ξ` derived (Section 11)

`Closure/FixedRawPositiveNull.lean` (`fixed_raw_positive_null_of_staged_volume_growth`) takes two premises that
committed producers now supply. This module removes them from the exported statement.

* `hfront` (point F1): `μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0` almost surely. It is
  `IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero` (`Proofs/Sec11/FixedSquareFrontierNull.lean:347`),
  applied to the zero-charge measure `hμ`, the deterministic fixed square, and `0 ≤ fixedSquareSide`
  (`fixedSquareSide_pos`). The square is fixed before `ω`; this is not a choice of good squares.
* `0 < ξ` (point R0): `IsLQGMetric.weylExponent_pos` (`Proofs/GFF/MetricXiSign.lean:360`), applied to the metric
  `h𝔇 : IsLQGMetric γ ξ 𝔇` and `hγ : 0 < γ`. Its binders are `(h𝔇) (hγ)`.

Credit: Leonardo Bonanno. The import closure of `FixedSquareFrontierNull.lean` contains his LatticeProb code (the
ergodic theorem `LatticeProb.Prob.Birkhoff`, reached through `Proofs/Sec8/BirkhoffPort.lean`), and the Weyl exponent
positivity uses his GFF construction for its realization (`Proofs/GFF/MetricXiSign.lean:359`). This module consumes
both producers, so both credits apply here.

Kept explicit, not derived here:

* `hDG`, `hCC`, `hE`: the staged literature inputs (`Proposed/LQG.lean`), pending operator source-check. `hE` is
  quantified over all `α`.
* `hdata` (T1): the square dyadic tail input `SquareDyadicTailInput`, and the applicability of the source metric `𝔇`
  (`h𝔇`) to it.
* `A`, `hA`, `hArep`, `ha`, `hb` (F3): the outside certificate premises, measurable with respect to the pinned
  σ-algebra `fixedPinnedSigma hC`. Their first-exit localization is not claimed here.
* `hμ : IsLQGMeasureOfField P γ 0 hcirc μ` (R1): zero log-charge only. The general charge is not covered.
* `Ω : Type` (R7): the carrier is the type zero. Transport to `Type*` is not done here.

The strict measurable clause `hmeasIns` is absent (point F2, closed in `Closure/FixedRawPositiveNull.lean`). This
module claims no closure of Lemma 11.12 (`PinchEventPositiveProbabilityStmt`) and no other numbered result.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Raw strengthened positivity of the fixed corrected configuration at zero log-charge, over the type-zero carrier
`Ω : Type`. The fixed-square frontier premise and the sign `0 < ξ` are supplied by the committed producers
`IsWholePlaneGFF.ae_lqgMeasure_frontier_closedSquare_eq_zero` and `IsLQGMetric.weylExponent_pos`. The premises kept
explicit are the staged inputs `hDG hCC hE`, the square tail input `hdata` (T1), the GFF `hgff`, the metric `h𝔇`,
the zero-charge measure `hμ` (R1), and the outside certificate premises `A hA hArep ha hb` (F3). Credit: Leonardo
Bonanno (see the module docstring). -/
theorem fixed_raw_positive_null_of_staged_volume_growth_derived
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω : Type} [m₀ : MeasurableSpace Ω] (P : Measure Ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (M : ℝ)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide)
    (A : Set Ω) (hA : MeasurableSet[fixedPinnedSigma hC] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) fixedW fixedT fixedQ' fixedQ fixedDelta})
    (ha : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta)))))
    (hb : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} := by
  have hξ : 0 < ξ := IsLQGMetric.weylExponent_pos h𝔇 hγ
  have hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0 :=
    hgff.ae_lqgMeasure_frontier_closedSquare_eq_zero hγ hγ₂ hμ fixedSquareCorner fixedSquareSide_pos.le
  exact fixed_raw_positive_null_of_staged_volume_growth hDG hCC hE hγ hγ₂ hξ P 𝔇 h𝔇 hgff hμ M hfront hdata
    A hA hArep ha hb

#print axioms fixed_raw_positive_null_of_staged_volume_growth_derived

end HarmonicBalls
