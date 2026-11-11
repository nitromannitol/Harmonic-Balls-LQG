import HarmonicBalls.Proofs.Sec11.DyadicMetricLocalityMoments
import HarmonicBalls.Steps.Sec11.LocalPunctureRemoval

/-! # Dyadic locality from finitely many diameter moments

One fixed puncture-removal criterion suffices for all sufficiently small
dyadic balls. The Section 8 inputs use Leonardo Bonanno's LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology
open scoped ENNReal

/-- Finitely many fixed-domain moments yield the dyadic modulo-constant
locality needed for the fixed-point pinch-frequency argument. -/
theorem IsWholePlaneGFF.exists_dyadic_locality_criterion_of_finite_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hξ : 0 < ξ) (hα : 0 ≤ α) (hαQ : α < lqgQ γ) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ closedBall (z i) ε,
        ⨆ y ∈ closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y ∂P) ≠ ∞) →
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
    h.exists_puncture_criterion_of_lqgMetric hAff 𝔇 h𝔇 D 1 α
      (by norm_num) hξ hα hαQ (ball 0 1) hball hmetric hscale
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


/-- Finitely many base-metric diameter moments suffice for the normalized
LQG pinch-frequency criterion. The one-scale probability bound and staged
field, affine and measure-coordinate hypotheses remain explicit. -/
theorem IsWholePlaneGFF.exists_pinch_frequency_criterion_of_finite_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) (hα0 : 0 ≤ α) (hα : α < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ α
      (fun x => if x.1 = 0 then hC x.2.1 else
        affinePairing hC hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else
        affineCircle hcirc (((2 : ℝ)⁻¹ : ℝ) : ℂ) 0 x.2.2))
    {U T Q V : Set ℂ} (hconfig : IsPinchPointConfiguration U T Q V) (M : ℝ)
    (δ : ℝ) (hδ : δ < (P {ω | pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
      U T Q V M ((2 : ℝ)⁻¹ ^ 1) 0}).toReal) :
    ∃ (ε : ℝ) (N : ℕ) (z : ℕ → ℂ), 0 < ε ∧
      ((∀ i, i ≤ N → (∫⁻ ω, ⨆ x ∈ closedBall (z i) ε,
        ⨆ y ∈ closedBall (z i) ε,
          internalMetric (𝔇 (hC ω)) (ball (z i) (2 * ε)) x y ∂P) ≠ ∞) →
        ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop, δ * k ≤
          ({n : ℕ | k + 1 ≤ n ∧ n ≤ 2 * k ∧
            pinchPointEventWithInternalBounds (μ ω) (fun x y => D ω (x, y))
              U T Q V M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℝ)) := by
  have hm := h.ae_lengthMetric_of_affine_mixture hAff hγ hγ₂ hα
    (k := (2 : ℝ)⁻¹) (by norm_num) 𝔇 h𝔇 hD haxioms
  obtain ⟨ε, N, z, hε, hcriterion⟩ :=
    h.exists_dyadic_locality_criterion_of_finite_diameter_moments hAff 𝔇 h𝔇 hD hm hξ hα0 hα
  exact ⟨ε, N, z, hε, fun hmom =>
    h.ae_internal_pinch_frequency_of_normalizedLQG hAff hCC hγ hγ₂ hα hμ hfull
      𝔇 h𝔇 hD haxioms hconfig M (hcriterion hmom) δ hδ⟩



end HarmonicBalls
