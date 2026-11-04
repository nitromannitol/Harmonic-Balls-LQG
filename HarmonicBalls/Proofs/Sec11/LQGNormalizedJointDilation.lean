import HarmonicBalls.Proofs.Sec11.LQGNormalizedJointLaw
import HarmonicBalls.Proofs.Sec11.NormalizedSingularMetric
import HarmonicBalls.Steps.Sec11.CurveConstantFiber

/-! # Joint law under normalized dilation of the singular metric -/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set

/-- The normalized geometric dilation of a continuous singular metric. -/
noncomputable def normalizedDilationMetric {Ω : Type*} (γ ξ α k : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → C(ℂ × ℂ, ℝ)) (ω : Ω) : C(ℂ × ℂ, ℝ) :=
  ⟨fun z => (Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k)) *
    Real.exp (ξ * (α * Real.log k))) * D ω (k • z.1, k • z.2), by fun_prop⟩

/-- Joint scaling of the LQG measure and singular metric. The affine invariance,
measure coordinate change and mixture metric axioms are staged inputs. -/
theorem IsWholePlaneGFF.identDistrib_normalizedDilation_singularMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → C(ℂ × ℂ, ℝ)}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {k : ℝ} (hk : 0 < k)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω (u, v) ∧
      ENNReal.ofReal (D ω (u, v)) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (haxioms : LQGMetricFieldAxioms (mixMeasure.prod (P.prod P)) γ ξ α
      (fun x => if x.1 = 0 then hC x.2.1 else affinePairing hC hcirc (k : ℂ) 0 x.2.2)
      (fun x => if x.1 = 0 then hcirc x.2.1 else affineCircle hcirc (k : ℂ) 0 x.2.2)) :
    IdentDistrib (fun ω => (μ ω, D ω))
      (fun ω => (normalizedPullbackMeasure γ α k (hcirc ω) (μ ω),
        normalizedDilationMetric γ ξ α k hcirc D ω)) P P := by
  have hD' : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ normalizedDilationMetric γ ξ α k hcirc D ω (u, v) ∧
      ENNReal.ofReal (normalizedDilationMetric γ ξ α k hcirc D ω (u, v)) =
        weylScaling (𝔇 (affinePairing hC hcirc (k : ℂ) 0 ω)) ξ
          (fun x => -α * Real.log ‖x‖) u v := by
    apply h.ae_normalized_affine_singularMetric_representation hAff 𝔇 h𝔇 hk hD
    · exact Filter.Eventually.of_forall (fun ω u v => rfl)
    · have hb := (h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
        (by intro ω; fun_prop) (by intro x; fun_prop)).ae_isEuclideanLengthMetric
      filter_upwards [hb] with ω hω
      have hpair : addFunPairing (hC ω) (fun _ => 0) = hC ω := by
        funext φ
        simp [addFunPairing]
      rw [hpair] at hω
      intro T p hp
      exact hω.ae_ne_of_lengthParametrized hp 0
  exact h.identDistrib_normalizedPullback_singularMetric hAff hCC hγ hγ₂ hα hμ hk
    𝔇 h𝔇 hD hD' haxioms

#print axioms IsWholePlaneGFF.identDistrib_normalizedDilation_singularMetric

end HarmonicBalls
