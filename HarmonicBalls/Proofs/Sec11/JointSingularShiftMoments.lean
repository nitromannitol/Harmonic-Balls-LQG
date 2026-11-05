import HarmonicBalls.Proofs.Sec11.JointSingularShiftShells
import HarmonicBalls.Proofs.Sec11.PunctureMetricHypotheses
import HarmonicBalls.Proofs.Sec11.InternalDiameterPositiveMoment

/-! # Joint singular observables from diameter moments

The Cameron–Martin argument uses Leonardo Bonanno's LatticeProb formalization.
The metric-field and affine-invariance propositions are staged hypotheses.
The displayed fixed-scale diameter moments remain to be established.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

set_option maxHeartbeats 400000 in
/-- Fixed-scale positive base-metric diameter moments yield a joint decoder on
countably many full open domains containing the origin. -/
theorem IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder_of_positive_diameter_moments
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hε : 0 < ε) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hDfield : IsLQGMetricOfField P γ ξ α hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ) (hξ : 0 < ξ) (hαnonneg : 0 ≤ α) (hβ : 0 < β)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    (f : ℂ → ℝ) (hf : Continuous f) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n ∧ (p n).1 ≠ 0)
    (hp₂ : ∀ n, (p n).2 ≠ 0)
    (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hball : ∀ i, ball (0 : ℂ) (Real.exp (1 - s i)) ⊆ U i) :
    ∃ (ε' : ℕ → ℝ) (N : ℕ → ℕ) (z : ℕ → ℕ → ℂ),
      (∀ i, 0 < ε' i) ∧
      ((∀ i j, j ≤ N i → (∫⁻ ω, (⨆ x ∈ closedBall (z i j) (ε' i),
        ⨆ y ∈ closedBall (z i j) (ε' i),
          internalMetric (𝔇 (hC ω)) (ball (z i j) (2 * ε' i)) x y) ^ β ∂P) ≠ ∞) →
    ∃ R ∈ Ioo (0 : ℝ) ε,
      ∃ F : (LocalZeroMeanTest univ → ℝ) → Measure ℂ × (ℕ → ℝ≥0∞), Measurable F ∧
        (∀ᵐ ω ∂P, F (localModConstPairings 0 hC univ ω) =
          (normalizedRestriction (μ ω) (ball 0 R), fun n =>
            ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, f z * ψ z)))) *
              internalMetric (D ω) (U n) (p n).1 (p n).2)) ∧
        ∀ g : ℂ → ℝ, IsTestFunction univ g → (∀ z, g z ≤ 0) →
          (∀ᵐ ω ∂P, F (localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ ω) =
            (normalizedRestriction ((μ ω).withDensity
              (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R), fun n =>
                ENNReal.ofReal (Real.exp (ξ * (-(hC ω ψ + ∫ z, (g z + f z) * ψ z)))) *
                  internalMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal)
                    (U n) (p n).1 (p n).2)) ∧
          P.map (F ∘ localModConstPairings 0
            (fun ω => addFunPairing (hC ω) g) univ) ≪
            P.map (F ∘ localModConstPairings 0 hC univ) ∧
          P.map (F ∘ localModConstPairings 0 hC univ) ≪
            P.map (F ∘ localModConstPairings 0
              (fun ω => addFunPairing (hC ω) g) univ)) := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield
  have hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y := by
    filter_upwards [hD] with ω hω
    exact fun x y => (hω x y).2
  have hbase := h.ae_isEuclideanLengthMetric_baseMetric 𝔇 h𝔇
  have hbaseNonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ 𝔇 (hC ω) x y := by
    filter_upwards [hbase] with ω hm x y
    have ht := hm.triangle x y x
    rw [hm.self_eq_zero, hm.symm y x] at ht
    linarith
  have hsingularNonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := by
    filter_upwards [hmetric] with ω hm x y
    have ht := hm.triangle x y x
    rw [hm.self_eq_zero, hm.symm y x] at ht
    linarith
  have hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (𝔇 (hC ω)) ξ 0 x y = ENNReal.ofReal (𝔇 (hC ω) x y) := by
    filter_upwards [hbase] with ω hm
    exact hm.weylScaling_zero ξ
  choose ε' N z hε' hcriterion using fun i =>
    h.exists_puncture_criterion_of_fixed_diameter_positive_moments hAff 𝔇 h𝔇
      D (s i) α β (hs i) hξ hαnonneg hα hβ (U i) (hball i)
      (h.measurable_baseMetric_apply 𝔇 h𝔇) hbase hmetric hbaseNonneg
      hsingularNonneg hzero hscale
  refine ⟨ε', N, z, hε', ?_⟩
  intro hmom
  have hremove : ∀ᵐ ω ∂P, ∀ i, ∀ a ∈ U i \ {0}, ∀ b ∈ U i \ {0},
      internalMetric (D ω) (U i \ {0}) a b = internalMetric (D ω) (U i) a b := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [hcriterion i (hmom i)] with ω hω a ha b hb
    exact hω a b (by simpa using ha.2) (by simpa using hb.2)
  exact h.exists_joint_singular_weyl_shift_decoder_of_point_removal hμ hfull hε 𝔇 h𝔇
    hD hDfield haxioms hγ hγ₂ hα hξ.le ψ hψ hψint f hf U hU p hp hp₂ hremove

#print axioms IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder_of_positive_diameter_moments

end HarmonicBalls
