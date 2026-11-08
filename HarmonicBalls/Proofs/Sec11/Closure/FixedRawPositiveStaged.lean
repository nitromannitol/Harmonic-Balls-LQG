import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositive
import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs

/-!
# Raw positivity of the fixed corrected configuration with the volume-growth input derived (Section 11)

`Closure/FixedRawPositive.lean` takes the volume-growth input `LQGVolumeGrowthAllScalesStmt.{0}` as a hypothesis.
That input is derived here from the three staged literature inputs `hDG`, `hCC`, `hE` (`WholePlaneLQGBallMassBounds`,
`LQGMeasureCoordChange`, `LQGMeasureExistence`, staged in `Proposed/LQG.lean`), through the proved route
`lqgVolumeGrowthAllScalesStmt_of_staged_inputs` (`Proofs/Sec9/WeakUniquenessDerivedInputs.lean:53`), which
supplies the affine-invariance premise by the proved provider `wholePlaneGFFAffineInvariance_univ`
(`Proofs/Sec3/DerivedInputAssembly.lean:55`) and applies `lqgVolumeGrowthAllScalesStmt_of_stronger_singularity`
(`Proofs/Sec2/SingularAtomAtZero.lean:59`). The staged inputs remain pending operator source-check.

The measurable clause of `hinside` is kept strict (`MeasurableSet`, as in the chain); the producer gives only
`NullMeasurableSet`, so that clause remains the open point F2 of the status note. The remaining leftovers are
the square premises `hfront` (F1) and `hdata` (T1), the measurable clause `hmeasIns` (F2), the pinned-σ-algebra
facts `hm`, `hA`, `hArep`, `ha`, `hb` (F3), and the sign `0 < ξ` (R0).
-/

namespace HarmonicBalls

open MeasureTheory Metric
open scoped ENNReal

/-- Raw strengthened positivity of the fixed corrected configuration at zero log-charge, for `ξ > 0`, with the
volume-growth input derived from the three staged literature inputs `hDG`, `hCC`, `hE`. -/
theorem fixed_raw_positive_of_staged_volume_growth
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (M : ℝ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide)
    (hmeasIns : ∀ n k : ℕ, 0 < n →
      @MeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU})
    (hm : fixedPinnedSigma hC ≤ m₀) (A : Set Ω) (hA : MeasurableSet[fixedPinnedSigma hC] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) fixedW fixedT fixedQ' fixedQ fixedDelta})
    (ha : @Measurable Ω ENNReal (fixedPinnedSigma hC) _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta)))))
    (hb : @Measurable Ω ENNReal (fixedPinnedSigma hC) _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} :=
  fixed_raw_positive_outside (lqgVolumeGrowthAllScalesStmt_of_staged_inputs.{0} hDG hCC hE)
    hγ hγ₂ hξ P 𝔇 h𝔇 hgff hμ M hfront hdata hmeasIns hm A hA hArep ha hb

#print axioms fixed_raw_positive_of_staged_volume_growth

end HarmonicBalls
