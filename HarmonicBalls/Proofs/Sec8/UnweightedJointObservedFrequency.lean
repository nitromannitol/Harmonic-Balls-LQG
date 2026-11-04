import HarmonicBalls.Proofs.Sec8.UnnormalizedJointObservedFrequency
import HarmonicBalls.Proofs.Sec8.RootedCircleWeightDomination

/-! # Rooted frequency from an unweighted joint comparison

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. The unweighted comparison is an
explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A joint circle comparison for unweighted roots on a superset gives a
measurable frequency representative for weighted roots on a subset. -/
theorem IsWholePlaneGFF.exists_rooted_observed_frequency_of_unweighted_joint_domination
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ξ} {Q : Measure Ω} {γ α α₀ R : ℝ}
    {hC : Ξ → (ℂ → ℝ) → ℝ} {hcirc : Ξ → ℝ → ℂ → ℝ}
    {gC : Ω → (ℂ → ℝ) → ℝ} {gcirc : Ω → ℝ → ℂ → ℝ}
    {ν : Ξ → Measure ℂ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (gGFF : IsWholePlaneGFF Q gC gcirc)
    (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (hμ : IsLQGMeasureOfField Q γ α gcirc μ) (hm : AEMeasurable μ Q)
    (B U : Set ℂ) (hB : MeasurableSet B) (hU : MeasurableSet U) (hBU : B ⊆ U)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂Q, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (hfinU : ∀ᵐ ω ∂Q, (μ ω) U ≠ ∞)
    (hR : 0 < R)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ν ω (ball (0 : ℂ) r) ≠ 0)
    (Y : ∀ ε : ℝ, Ω × ℂ → (Section6.LocalTest (ball 0 ε) → ℝ))
    (hY : ∀ ε, Measurable (Y ε))
    (hdom : ∀ ε ∈ Ioo (0 : ℝ) R, ∀ n z,
      closedBall z (dyadicScale n) ⊆ ball 0 ε →
      (Q ⊗ₘ unnormalizedWeightedRestrictionKernel Q μ hm U hU (fun _ => 1)
        measurable_const).map (fun x => (Y ε x,
        fieldCircleAverage α (gcirc x.1) (dyadicScale n) (z + x.2) -
          fieldCircleAverage α (gcirc x.1) (dyadicScale n) x.2)) ≪
      P.map (fun ω => (Section6.localPairingProc (ball 0 ε) hC ω,
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0)))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ ε ∈ Ioo (0 : ℝ) R,
      ∃ E : Set ((Section6.LocalTest (ball 0 ε) → ℝ) × ℂ), MeasurableSet E ∧
        ∀ᵐ x ∂(Q ⊗ₘ weightedRestrictionKernel Q μ hm B hB w hw),
          ((Y ε x, x.2) ∈ E ↔ ∀ᶠ N : ℕ in atTop,
            (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x.1) β x.2 N₀
              a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  have hfinB : ∀ᵐ ω ∂Q, ((μ ω).withDensity w) B ≠ ∞ := hmass.mono fun _ h => h.2
  apply hGFF.exists_rooted_observed_frequency_of_unnormalized_joint_domination
    gGFF hν hμ hm B hB w hw hmass hR hpos Y hY ?_
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  intro ε hε n z hz
  exact (gGFF.rooted_centeredCircle_law_ac_of_subset hμ hm B U hB hU hBU w hw
    hfinB hfinU (Y ε) (hY ε) n z).trans (hdom ε hε n z hz)

#print axioms IsWholePlaneGFF.exists_rooted_observed_frequency_of_unweighted_joint_domination

end HarmonicBalls
