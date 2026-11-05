import HarmonicBalls.Proofs.Sec11.InternalDiameterPositiveMoment
import HarmonicBalls.Proofs.Sec11.DyadicLocalityFiniteMoments
import HarmonicBalls.Proofs.Sec11.PinchUnitScalesFiniteMoments

/-! # Dyadic locality from positive diameter moments

The Section 8 inputs use Leonardo Bonanno's LatticeProb formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped ENNReal

/-- Puncture removal follows from finitely many fixed-scale diameter moments,
for a singular metric with its length and Weyl identities made explicit. -/
theorem IsWholePlaneGFF.exists_puncture_criterion_of_lqgMetric_positive_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (E : Ω → ℂ → ℂ → ℝ) (s α p : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) (hp : 0 < p)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ Metric.closedBall (c i) ε,
        ⨆ y ∈ Metric.closedBall (c i) ε,
          internalMetric (𝔇 (hC ω)) (Metric.ball (c i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y) := by
  have hD := h.ae_isEuclideanLengthMetric_baseMetric 𝔇 h𝔇
  have hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ 𝔇 (hC ω) x y := by
    filter_upwards [hD] with ω hω
    intro x y
    have ht := hω.triangle x y x
    rw [hω.self_eq_zero, hω.symm y x] at ht
    linarith
  have hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y := by
    filter_upwards [hE] with ω hω
    intro x y
    have ht := hω.triangle x y x
    rw [hω.self_eq_zero, hω.symm y x] at ht
    linarith
  have hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y) := by
    filter_upwards [hD] with ω hω
    exact hω.weylScaling_zero ξ
  exact h.exists_puncture_criterion_of_fixed_diameter_positive_moments hAff 𝔇 h𝔇 E s α p
    hs hξ hα hαQ hp V hball (h.measurable_baseMetric_apply 𝔇 h𝔇) hD hE
    hDnonneg hEnonneg hzero hscale

/-- Finitely many fixed-domain moments yield the dyadic modulo-constant
locality needed for the fixed-point pinch-frequency argument. -/
theorem IsWholePlaneGFF.exists_dyadic_locality_criterion_of_positive_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) (p : ℝ) (hp : 0 < p) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ closedBall (z i) ε,
        ⨆ y ∈ closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) →
        ∀ δ, 0 < δ → ∃ K, ∀ n, K ≤ n →
          ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
            (∀ᵐ ω ∂P, 0 < c ω) ∧
            (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC (ball 0 δ)]
              (fun ω => G ω x y)) ∧
            ∀ᵐ ω ∂P, ∀ x ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
              ∀ y ∈ ball 0 (6 * ((2 : ℝ)⁻¹ ^ n)),
              internalMetric (fun x y => c ω * D ω x y)
                (ball 0 (6 * ((2 : ℝ)⁻¹ ^ n))) x y = G ω x y) := by
  let R : ℕ → ℝ := fun n => 6 * ((2 : ℝ)⁻¹ ^ n)
  have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
  have hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
    filter_upwards [hD] with ω hω
    exact fun x y => (hω x y).2
  have hball : ball (0 : ℂ) (Real.exp (1 - (1 : ℝ))) ⊆ ball 0 1 := by simp
  obtain ⟨ε, N, z, hε, hremove⟩ :=
    h.exists_puncture_criterion_of_lqgMetric_positive_moments hAff 𝔇 h𝔇 D 1 α p
      (by norm_num) hξ hα hαQ hp (ball 0 1) hball hmetric hscale
  refine ⟨ε, N, z, hε, ?_⟩
  intro hmom δ hδ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_ball : IsOpen (ball (0 : ℂ) δ)) ⟨0, mem_ball_self hδ⟩
  have hlim : Tendsto R atTop (𝓝 0) := by
    simpa only [R, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).const_mul 6
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds (lt_min (show (0 : ℝ) < 1 by norm_num) hδ)))
  refine ⟨K, ?_⟩
  intro n hn
  have hsmall : R n < min 1 δ := hK n hn
  have hne : (ball (0 : ℂ) (R n) \ {0}).Nonempty := by
    refine ⟨((R n / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos (hR n))]
      linarith [hR n]
    · simp only [mem_singleton_iff]
      exact_mod_cast (ne_of_gt (half_pos (hR n)))
  apply h.exists_modConst_internal_singularMetric_of_point_removal 𝔇 h𝔇 hD hmetric
    isOpen_ball hne (ball_subset_ball (le_of_lt (hsmall.trans_le (min_le_right _ _)))) ψ hψ hψint
  filter_upwards [hremove hmom, hmetric] with ω hω hmetricω x hx y hy
  have hres := hmetricω.internalMetric_sdiff_zero_eq_of_subset
    (V := ball (0 : ℂ) 1) (W := ball 0 (R n)) isOpen_ball isOpen_ball
    (mem_ball_self (hR n)) (ball_subset_ball (le_of_lt (hsmall.trans_le (min_le_left _ _))))
    (by intro a ha b hb; exact hω a b (by simpa using ha.2) (by simpa using hb.2))
  exact hres x y (by simpa using hx.2) (by simpa using hy.2)


open Classical in
/-- At Liouville charge, finitely many base-metric diameter moments and
positive unit-scale internal-pinch probability imply arbitrarily small
internal and original pinch scales. -/
theorem IsWholePlaneGFF.exists_small_pinch_scales_of_unit_probability_and_positive_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hDG : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (γ' : ℝ)
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P' γ' hC' hcirc')
    (hCC0 : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (γ' : ℝ)
      (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P' γ' 0 hC' hcirc')
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hCC : LQGMeasureCoordChange P γ γ hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) (p : ℝ) (hp : 0 < p)
    (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ γ
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (hpos : 0 < P {ω | pinchPointEventWithInternalBounds (μ ω)
      (fun x y => D ω (x, y)) U T Q V M 1 0}) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, (⨆ x ∈ closedBall (z i) ε,
        ⨆ y ∈ closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y) ^ p ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∃ n : ℕ, ((2 : ℝ)⁻¹) ^ n < r ∧
          pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
            U T Q V M ((2 : ℝ)⁻¹ ^ n) 0 ∧
          pinchPointEvent (μ ω) (fun x y => D ω (x, y))
            U T Q V M ((2 : ℝ)⁻¹ ^ n) 0) := by
  have hα := gamma_lt_lqgQ hγ hγ₂
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hm := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  obtain ⟨ε, N, z, hε, hlocal⟩ :=
    h.exists_dyadic_locality_criterion_of_positive_diameter_moments hAff 𝔇 h𝔇 hD hm hξ hγ.le hα p hp
  refine ⟨ε, N, z, hε, ?_⟩
  intro hmom
  obtain ⟨δ, hδ, hfreq⟩ := h.ae_positive_internal_pinch_frequency_of_lqg_inputs
    hDG hCC0 hE0 hCC hγ hγ₂ hα hμ 𝔇 h𝔇 hD haxioms hconfig M (hlocal hmom) hpos
  filter_upwards [hfreq, hm] with ω hω hmetric r hr
  obtain ⟨n, hn, hevent⟩ := exists_small_dyadic_scale_of_positive_block_density hδ.1 hω r hr
  exact ⟨n, hn, hevent, pinchPointEvent_of_internalBounds hmetric hevent⟩

#print axioms IsWholePlaneGFF.exists_small_pinch_scales_of_unit_probability_and_positive_moments
#print axioms IsWholePlaneGFF.exists_puncture_criterion_of_lqgMetric_positive_moments
#print axioms IsWholePlaneGFF.exists_dyadic_locality_criterion_of_positive_diameter_moments

end HarmonicBalls
