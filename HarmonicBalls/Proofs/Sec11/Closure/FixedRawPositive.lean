import HarmonicBalls.Proofs.Sec11.CorrectedPinchConditionalPositive
import HarmonicBalls.Proofs.Sec11.Closure.CorrectedFixedGeometry
import HarmonicBalls.Proofs.Sec11.Closure.FixedMassDiameterOutside

/-!
# Raw strengthened positivity of the fixed corrected configuration (Section 11, r7 lines 937–1037)

The conditional chain `IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth`
(`Proofs/Sec11/CorrectedPinchConditionalPositive.lean:13`) gives the positivity of the strengthened pinch event
for a corrected configuration, given the volume-growth input, `0 < ξ`, the conditional positivity `hinside`, and
the pinned-σ-algebra facts of the first event. This module instantiates it for the fixed corrected configuration
(`Closure/CorrectedFixedGeometry.lean`), with the pinned σ-algebra `fixedPinnedSigma hC` of the outside of a
neighbourhood of `W` (`Closure/FixedMassDiameterOutside.lean`), and the positivity part of `hinside` from
`fixed_outside_hinside_of_square_dyadic_tail`.

The leftover premises are explicit: the volume-growth input (through the full-support hypothesis, derived from
`LQGVolumeGrowthAllScalesStmt`), the square premises `hfront` (F1) and `hdata` (T1), the measurable clause `hmeasIns`
of `hinside` (F2), and the pinned-σ-algebra facts `hm`, `hA`, `hArep`, `ha`, `hb` (the first event measurable
outside `W`, the claim under review F3). `0 < ξ` is the premise R0 of the status note.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- The σ-algebra of the field outside a neighbourhood of `W`, modulo constants: the pinned σ-algebra of the
fixed configuration. -/
@[instance_reducible]
noncomputable def fixedPinnedSigma {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (localModConstPairings 0 hC fixedOutside) inferInstance

/-- Raw strengthened positivity of the fixed corrected configuration at zero log-charge, for `ξ > 0`, from the
conditional chain. The premises are explicit (see the module docstring). -/
theorem fixed_raw_positive_outside (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
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
    (ha : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta)))))
    (hb : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ (fun ω =>
      ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} := by
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ₂ hα Ω P hC hcirc μ hgff hμ
  have hinside : ∀ n k : ℕ, 0 < n →
      @MeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU} ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU}).indicator (fun _ => (1 : ℝ)) | fixedPinnedSigma hC]) ω := by
    intro n k hn
    refine ⟨hmeasIns n k hn, ?_⟩
    exact @fixed_outside_hinside_of_square_dyadic_tail Ω m₀ P 0 γ ξ hC hcirc μ hgff hμ hγ hξ 𝔇 h𝔇
      hfull hfront hdata n hn k
  exact IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth hgrowth
    isCorrectedPinchConfiguration_fixed hξ hγ hγ₂ hα P hC hcirc 𝔇 μ h𝔇 hgff hμ M
    (fixedPinnedSigma hC) hm A hA hArep ha hb hinside

#print axioms fixed_raw_positive_outside

end HarmonicBalls
