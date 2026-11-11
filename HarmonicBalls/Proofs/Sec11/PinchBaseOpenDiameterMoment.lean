import HarmonicBalls.Proofs.Sec11.PinchBaseInternalMoment

/-! # Base pinch positivity from open-square diameter moments

The conditional smooth-shift argument uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. The moment estimate
remains an explicit hypothesis. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- A uniform optimized moment estimate for the measurable intermediate
diameters implies positivity of the strengthened base-metric pinch event. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_open_moment
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
      ∀ (c s : ℝ), 0 < c → 0 < s → s < ξ * (lqgQ γ - 2) →
      ∀ (e : ℝ → ℝ), Tendsto e (𝓝[>] 0) (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
        let r := 3 * L / (2 * (2 : ℝ) ^ n)
        let t := (ξ * lqgQ γ - s) / ξ ^ 2
        (∫⁻ ω, ((ENNReal.ofReal c)⁻¹ *
          dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω) ^ t ∂P) ≤
          ENNReal.ofReal (r ^ (ξ * lqgQ γ * t - ξ ^ 2 * t ^ 2 / 2 + e r))) →
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
  intro c s hc hs hsh e he hm
  have hsQ : s < ξ * lqgQ γ := by nlinarith
  let q := (ξ * lqgQ γ - s) ^ 2 / (2 * ξ ^ 2)
  have hq : 2 < q := metricDiameterTailExponent_gt_two hξ hsh
  let p := (2 + q) / 2
  have hp : 2 < p := by dsimp [p]; linarith
  have hpq : p < q := by dsimp [p]; linarith
  have hscale := dyadic_scaled_power_error_eventually_le (3 * L / 2) q p
    (by positivity) (by linarith) hpq
    (fun n => e (3 * L / (2 * (2 : ℝ) ^ n)))
    (tendsto_intermediate_square_error L hL e he)
  have htail : ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
        ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
        dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p + (0 : ℝ)) * n)) := by
    filter_upwards [hm, hscale] with n hn hscale'
    intro i
    have hr : 0 < 3 * L / (2 * (2 : ℝ) ^ n) := by positivity
    have hmeas : AEMeasurable (fun ω => (ENNReal.ofReal c)⁻¹ *
        dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i ω) P :=
      aemeasurable_const.mul
        (hgff.aemeasurable_dyadicIntermediateInternalDiameter 𝔇 h𝔇 z L hL n i)
    have ht := hgff.measure_scaled_power_tail_of_optimized_moment
      (dyadicIntermediateInternalDiameter (fun ω => 𝔇 (hC ω)) z L n i)
      c _ ξ (lqgQ γ) s _ hc hr hξ hsQ hmeas (hn i)
    have hside : 3 * L / (2 * (2 : ℝ) ^ n) = (3 * L / 2) * (1 / 2 : ℝ) ^ n := by
      rw [div_pow]
      field_simp
      ring
    exact ht.trans (ENNReal.ofReal_le_ofReal (by simpa only [hside, add_zero, q] using hscale'))
  have hsmall : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop,
      ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) < ENNReal.ofReal a :=
    fun a ha => intermediate_square_threshold_eventually_lt c L s hL hs a ha
  apply h.positive_internal_pinch_of_open_first_second hξ P M hC hcirc 𝔇 μ
    h𝔇 hgff hμ hfull ψ hψ hψint
  exact hpos (fun n => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s))
    p hp (fun _ => 0) tendsto_const_nhds hsmall htail

/-- A closed-square moment bound suffices for the measurable open-domain
diameters. No measurability of the closed-square diameter is needed. -/
theorem IsCorrectedPinchConfiguration.exists_square_positive_base_internal_pinch_of_closed_moment
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
      ∀ (c s : ℝ), 0 < c → 0 < s → s < ξ * (lqgQ γ - 2) →
      ∀ (e : ℝ → ℝ), Tendsto e (𝓝[>] 0) (𝓝 0) →
      (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
        let r := 3 * L / (2 * (2 : ℝ) ^ n)
        let t := (ξ * lqgQ γ - s) / ξ ^ 2
        (∫⁻ ω, ((ENNReal.ofReal c)⁻¹ *
          (⨆ x ∈ complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i,
            ⨆ y ∈ complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i,
              internalMetric (𝔇 (hC ω))
                (complexIntermediateGridSquare z (L / (2 : ℝ) ^ n) i) x y)) ^ t ∂P) ≤
          ENNReal.ofReal (r ^ (ξ * lqgQ γ * t - ξ ^ 2 * t ^ 2 / 2 + e r))) →
      0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  obtain ⟨z, L, hL, hSU, hfront, hpos⟩ :=
    h.exists_square_positive_base_internal_pinch_of_open_moment
      hgrowth hγ hγ2 hξ hgff hμ 𝔇 h𝔇 M
  refine ⟨z, L, hL, hSU, hfront, ?_⟩
  intro c s hc hs hsh e he hm
  apply hpos c s hc hs hsh e he
  have hsQ : s < ξ * lqgQ γ := by nlinarith
  have ht : 0 ≤ (ξ * lqgQ γ - s) / ξ ^ 2 :=
    (div_pos (by linarith) (sq_pos_of_pos hξ)).le
  filter_upwards [hm] with n hn
  intro i
  refine (lintegral_mono fun ω => ENNReal.rpow_le_rpow ?_ ht).trans (hn i)
  gcongr
  exact dyadicIntermediateInternalDiameter_le_closedSquareDiameter
    (fun ω => 𝔇 (hC ω)) z L hL n i ω

end HarmonicBalls
