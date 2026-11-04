import HarmonicBalls.Proofs.Sec8.LocalCirclePairingApproximation
import HarmonicBalls.Proofs.Sec8.RootedCircleSamplingComparison

/-! # Rooted circle approximation under normalized sampling

The imported Section 8 development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Convergence of local pairings under normalized rooted sampling is enough
for the unnormalized joint field and circle comparison. The two rooted
sampling measures have the same null sets on a set of finite LQG mass. -/
theorem IsWholePlaneGFF.exists_normalized_rooted_tests_for_joint_circle_law
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} {Q : Measure Ω} {γ α α₀ ε : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {gC : Ω → (ℂ → ℝ) → ℝ} {gcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hμ : IsLQGMeasureOfField Q γ α gcirc μ) (hm : AEMeasurable μ Q)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfin : ∀ᵐ ω ∂Q, ((μ ω).withDensity w) B ≠ ∞)
    (n : ℕ) (z : ℂ) (hz : closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ φ : ℕ → Section6.LocalTest (ball 0 ε),
      ∀ (Y : Ω × ℂ → (Section6.LocalTest (ball 0 ε) → ℝ)), Measurable Y →
        (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw).map Y ≪
          P.map (Section6.localPairingProc (ball 0 ε) hC) →
        TendstoInMeasure (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw)
          (fun j x => Y x (φ j)) atTop
          (fun x => fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
            fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2 +
              α₀ * (Real.circleAverage (fun v => Real.log ‖v‖) z (dyadicScale n) -
                Real.circleAverage (fun v => Real.log ‖v‖) 0 (dyadicScale n))) →
        (Q ⊗ₘ unnormalizedWeightedRestrictionKernel Q μ hm B hB w hw).map
          (fun x => (Y x, fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
            fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2)) ≪
        P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
            fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0)) := by
  obtain ⟨φ, hφ⟩ := hGFF.exists_localPairing_tests_for_joint_circle_law
    (α₀ := α₀) (dyadicScale_pos n) z hz
  refine ⟨φ, ?_⟩
  intro Y hY hdom hlim
  have hnormalized := hφ (Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw)
    Y hY hdom
    (fun x => fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
      fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2) hlim
  exact ((gGFF.rooted_centeredCircle_laws_mutually_absolutelyContinuous hμ hm B hB w hw
    hfin Y hY n z).2).trans hnormalized

#print axioms IsWholePlaneGFF.exists_normalized_rooted_tests_for_joint_circle_law

end HarmonicBalls
