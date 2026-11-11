import HarmonicBalls.Proofs.Sec11.PinchSecondBaseSelectedSquare

/-! # A single continuity square for every outside event

The conditional dyadic-core argument uses Leonardo Bonanno's smooth-shift
formalization `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A continuity square can be chosen independently of the outside event;
a dyadic tail for that square works simultaneously for every positive
outside event. -/
theorem IsCorrectedPinchConfiguration.exists_square_second_base_all_outside
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
    (M : ℝ) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      (∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0) ∧
      ∀ (b : ℕ → ℝ≥0∞) (p : ℝ), 2 < p → ∀ (e : ℕ → ℝ),
      Tendsto e atTop (𝓝 0) →
      (∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, b n < ENNReal.ofReal a) →
      (∀ᶠ n in atTop, ∀ i, P {ω | b n * ENNReal.ofReal
        (Real.exp (ξ * hcirc ω 1 0)) < dyadicIntermediateInternalDiameter
          (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + e n) * n))) →
      ∀ A : Set Ω, MeasurableSet[MeasurableSpace.comap
        (localModConstPairings 0 hC (closure W)ᶜ) inferInstance] A → 0 < P A →
      0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ2 hQ
    Ω P hC hcirc μ hgff hμ
  obtain ⟨z, L, hL, hSU, _, _, hfront⟩ := h.exists_continuity_mass_core_square hgff hμ
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro b p hp e he hsmall hbound A hA hAp
  exact h.positive_second_base_of_dyadic_tail hgrowth hγ hγ2 hξ hgff hμ hAff 𝔇 h𝔇
    A M hA hAp z L hL hSU hfront hfull b p hp e he hsmall hbound

end HarmonicBalls
