import HarmonicBalls.Proofs.Sec11.PinchSecondBaseVolumeGrowth
import HarmonicBalls.Proofs.Sec11.CorrectedPinchDyadicThresholds

/-! # Second pinch from a dyadic diameter tail

The conditional dyadic-core argument uses Leonardo Bonanno's smooth-shift
formalization `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A uniform dyadic diameter tail supplies the conditional interior
thresholds in the second-pinch assembly. -/
theorem IsCorrectedPinchConfiguration.positive_second_base_of_dyadic_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [m₀ : MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (A : Set Ω) (M : ℝ)
    (hA : MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance] A) (hAp : 0 < P A)
    (z : ℂ) (L : ℝ) (hL : 0 < L) (hSU : closedSquare z L ⊆ U)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0)
    (hfull : ∀ᵐ ω ∂P, ∀ B : Set ℂ, IsOpen B → B.Nonempty → 0 < μ ω B)
    (b : ℕ → ℝ≥0∞) (p : ℝ) (hp : 2 < p) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hsmall : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, b n < ENNReal.ofReal a)
    (hbound : ∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
      (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
        (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) :
    0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  have hm : MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance ≤ m₀ := by
    apply measurable_iff_comap_le.mp
    exact measurable_pi_iff.mpr fun φ =>
      (hgff.measurable_pairing φ.1 (φ.2.1.mono_set (subset_univ _))).sub_const _
  exact h.positive_second_base_of_volumeGrowth hgrowth hγ hγ2 hgff hμ hAff 𝔇 h𝔇
    hm A M hA hAp (h.conditional_dyadic_thresholds hgff hμ hγ hξ 𝔇 h𝔇 z L hL
      hSU hfront hfull b p hp e he hsmall hbound)

end HarmonicBalls
