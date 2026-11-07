import HarmonicBalls.Proofs.Sec11.DyadicTailPrefactor
import HarmonicBalls.Proofs.Sec11.PinchBaseInternalAffine

/-! # Base pinch positivity from diameter tails with a prefactor

The smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The uniform tail
estimate is an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A uniform open-domain diameter tail with a fixed prefactor implies
positivity of the strengthened base-metric pinch event. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_prefactor_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hξ : 0 < ξ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (M : ℝ) :
    ∃ z : ℂ, ∃ L : ℝ, 0 < L ∧ closedSquare z L ⊆ U ∧
      (∀ᵐ ω ∂P, μ ω (frontier (closedSquare z L)) = 0) ∧
      ∀ (c s A p : ℝ), 0 < s → 0 ≤ A → 2 < p →
      ∀ (e : ℝ → ℝ), Tendsto e (𝓝[>] 0) (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
        P {ω | ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
          ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
          dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
          ENNReal.ofReal (A * (3 * L / (2 * (2 : ℝ) ^ n)) ^
            (p + e (3 * L / (2 * (2 : ℝ) ^ n))))) →
      0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ2 hQ
    Ω P hC hcirc μ hgff hμ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  obtain ⟨z, L, hL, hSU, hfront, hpos⟩ :=
    h.exists_square_positive_base_first_second hgrowth hγ hγ2 hξ hgff hμ
      (wholePlaneGFFAffineInvariance_proved P hC hcirc) 𝔇 h𝔇 M
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro c s A p hs hA hp e he hbound
  let p' := (2 + p) / 2
  have hp' : 2 < p' := by dsimp [p']; linarith
  have hpp : p' < p := by dsimp [p']; linarith
  have htail := dyadicIntermediateInternalDiameter_tail_of_prefactor P
    (fun ω => 𝔇 (hC ω)) z L hL
    (fun n ω => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
      ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0))) A p p' hA (by linarith) hpp e he hbound
  have hsmall : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop,
      ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) < ENNReal.ofReal a :=
    fun a ha => intermediate_square_threshold_eventually_lt c L s hL hs a ha
  apply h.positive_internal_pinch_of_open_first_second hξ P M hC hcirc 𝔇 μ
    h𝔇 hgff hμ hfull ψ hψ hψint
  exact hpos (fun n => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s))
    p' hp' (fun _ => 0) tendsto_const_nhds hsmall (by simpa using htail)

#print axioms IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_prefactor_tail
end HarmonicBalls
