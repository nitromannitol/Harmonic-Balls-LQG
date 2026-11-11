import HarmonicBalls.Proofs.Sec11.JointSingularCutoffShift
import HarmonicBalls.Proofs.Sec11.SingularCutoffWeylComparison

/-! # Joint singular-measure and singular-metric Weyl shifts

The Cameron–Martin argument uses Leonardo Bonanno's LatticeProb formalization.
The metric-field axioms used for the singular length properties are staged
and await source check.
-/

noncomputable section

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

set_option maxHeartbeats 400000 in
/-- A joint observable decodes the singular measure and internal metric and
identifies its law under nonpositive smooth shifts. The observation domains
are separated from zero. The singular length properties use the explicit
staged metric-field axioms. -/
theorem IsWholePlaneGFF.exists_joint_singular_weyl_shift_decoder
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α ε : ℝ}
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
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ) (hξ : 0 ≤ ξ)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction univ ψ) (hψint : ∫ x, ψ x = 1)
    {r : ℝ} (hr : 0 < r) (U : ℕ → Set ℂ) (hU : ∀ n, IsOpen (U n))
    (haway : ∀ n z, z ∈ U n → r ≤ ‖z‖)
    (p : ℕ → ℂ × ℂ) (hp : ∀ n, (p n).1 ∈ U n) :
    let f : ℂ → ℝ := fun z => -α * Real.log (max ‖z‖ r)
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
              (fun ω => addFunPairing (hC ω) g) univ) := by
  have hmetric := ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield
  have hshifts := ae_singularField_weylBump_lengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
    haxioms h hγ hγ₂ hα hDfield hξ
  obtain ⟨R, hR, F, hF, hbase, hshift⟩ :=
    h.exists_joint_singular_cutoff_shift_decoder hμ hfull hε 𝔇 h𝔇 hD hmetric
      ψ hψ hψint hr U hU haway p hp
  refine ⟨R, hR, F, hF, hbase, ?_⟩
  intro g hg hu
  obtain ⟨hgshift, hac1, hac2⟩ := hshift g hg
  have hgmetric : ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ g x y).toReal) := by
    filter_upwards [hshifts] with ω hω
    exact hω g hg.1.continuous hg.2.1 hu
  have hrepr : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (D ω u v) =
      weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v := by
    filter_upwards [hD] with ω hω u v
    exact (hω u v).2
  have hcompare := h.ae_internal_singularMetric_weylShift_eq_cutoff 𝔇 h𝔇 hrepr hmetric
    g hg.1.continuous hg.2.1 hu hξ hgmetric hr U hU haway
  refine ⟨?_, hac1, hac2⟩
  filter_upwards [hgshift, hcompare] with ω hω heq
  rw [hω]
  congr 1
  funext n
  rw [heq n (p n).1 (p n).2]


end HarmonicBalls
