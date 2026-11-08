import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositive
import HarmonicBalls.Proofs.Sec11.Closure.NullConditionalGrowth
import HarmonicBalls.Proofs.Sec11.ConditionalCoreMeasurability
import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositiveStaged
import HarmonicBalls.Proofs.Sec11.Closure.PinchedSigmaLe

/-!
# Raw positivity of the fixed corrected configuration with the null-measurable inside clause (Section 11)

`Closure/FixedRawPositive.lean` takes the strict clause `hmeasIns` of `hinside`. Its producer
`IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam` (`Proofs/Sec11/ConditionalCoreMeasurability.lean:26`) gives the
inside events `{ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < n⁻¹ ∧ k < μ ω fixedU}` in `NullMeasurableSet`, and the
null-measurable growth chain `Closure/NullConditionalGrowth.lean` consumes exactly that. This module therefore removes
the leftover `hmeasIns` (point F2 of the status note) and keeps the other premises of `fixed_raw_positive_outside`.
The remaining leftovers are `hgrowth`, `hfront` (F1), `hdata` (T1), `hm`, `hA`, `hArep`, `ha`, `hb` (F3), and `0 < ξ` (R0).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Raw strengthened positivity of the fixed corrected configuration at zero log-charge, for `ξ > 0`, with the
null-measurable inside clause. Same as `fixed_raw_positive_outside` (`Closure/FixedRawPositive.lean`) without the
strict measurability premise `hmeasIns`. -/
theorem fixed_raw_positive_outside_null (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (M : ℝ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide)
    (hm : fixedPinnedSigma hC ≤ m₀) (A : Set Ω) (hA : MeasurableSet[fixedPinnedSigma hC] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) fixedW fixedT fixedQ' fixedQ fixedDelta})
    (ha : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta)))))
    (hb : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} := by
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ₂ hα Ω P hC hcirc μ hgff hμ
  have hδ : (0 : ℝ) < fixedDelta := by
    rw [fixedDelta_eq]
    norm_num
  have hU : MeasurableSet fixedU := isOpen_ball.measurableSet
  have hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU}).indicator (fun _ => (1 : ℝ)) | fixedPinnedSigma hC]) ω := by
    intro n k hn
    refine ⟨?_, ?_⟩
    · have hnull := IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam hgff hμ hδ 𝔇 h𝔇 fixedU fixedV
        hU (k : ℝ≥0∞) ((n : ℝ≥0∞)⁻¹)
      have hset : {ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
          (k : ℝ≥0∞) < μ ω fixedU} = {ω | (k : ℝ≥0∞) < μ ω fixedU ∧
          internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹} := by
        ext ω
        exact and_comm
      rw [hset]
      exact hnull
    · exact @fixed_outside_hinside_of_square_dyadic_tail Ω m₀ P 0 γ ξ hC hcirc μ hgff hμ hγ hξ 𝔇 h𝔇
        hfull hfront hdata n hn k
  exact IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth_null hgrowth
    isCorrectedPinchConfiguration_fixed hξ hγ hγ₂ hα P hC hcirc 𝔇 μ h𝔇 hgff hμ M
    (fixedPinnedSigma hC) hm A hA hArep ha hb hinside

#print axioms fixed_raw_positive_outside_null

/-- Raw strengthened positivity of the fixed corrected configuration for `ξ > 0`, with the volume-growth input derived
from the staged inputs `hDG`, `hCC`, `hE`, the pinned-σ-algebra premise `hm` proved (`fixedPinnedSigma_le`), and the
null-measurable inside clause. The leftover premises are `hfront` (F1), `hdata` (T1), `A`, `hA`, `hArep`, `ha`, `hb`
(F3), and `0 < ξ` (R0). The staged inputs remain pending operator source-check. -/
theorem fixed_raw_positive_null_of_staged_volume_growth
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] (P : Measure Ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (M : ℝ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide)
    (A : Set Ω) (hA : MeasurableSet[fixedPinnedSigma hC] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) fixedW fixedT fixedQ' fixedQ fixedDelta})
    (ha : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta)))))
    (hb : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} :=
  fixed_raw_positive_outside_null (lqgVolumeGrowthAllScalesStmt_of_staged_inputs.{0} hDG hCC hE)
    hγ hγ₂ hξ P 𝔇 h𝔇 hgff hμ M hfront hdata (fixedPinnedSigma_le hgff) A hA hArep ha hb

#print axioms fixed_raw_positive_null_of_staged_volume_growth

end HarmonicBalls
