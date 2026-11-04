import HarmonicBalls.Proofs.Sec8.RootedSamplingBallMass
import HarmonicBalls.Proofs.Sec8.ObservedFrequencyApproximation

/-! # Observable frequency under a normalized rooted law

The phase-frequency argument uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. Convergence of the local mass
approximations under the rooted law remains an explicit hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Convergent observed mass approximants produce an observed frequency
event under the normalized weighted rooted sampling law. -/
theorem exists_observed_frequency_event_weightedRestriction_compProd
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    (observe : Ω → F) (hobserve : Measurable observe) (ε : ℝ) (hε : 0 < ε)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (f : S → ℕ → F × ℂ → ℝ) (hf : ∀ V n, Measurable (f V n))
    (hlim : ∀ V, TendstoInMeasure (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw)
      (fun n x => f V n (observe x.1, x.2)) atTop
      (fun x => (normalizedRestriction
        ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) V.val).toReal))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (F × ℂ), MeasurableSet E ∧
      ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw),
        ((observe x.1, x.2) ∈ E ↔ ∀ᶠ N : ℕ in atTop,
          (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ x.1) β x.2 N₀
            a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) := by
  let κ := weightedRestrictionKernel P μ hμ B hB w hw
  let Q := P ⊗ₘ κ
  let : IsProbabilityMeasure Q := isProbabilityMeasure_weightedRestriction_compProd
    P μ hμ B hB w hw hmass
  have hμQ : AEMeasurable (fun x : Ω × ℂ => μ x.1) Q := by
    apply (hμ.measurable_mk.comp measurable_fst).aemeasurable.congr
    filter_upwards [ae_fst_of_ae_compProd P κ hμ.ae_eq_mk] with x hx
    exact hx.symm
  have hlocQ : ∀ᵐ x ∂Q, IsLocallyFiniteMeasure (μ x.1) :=
    ae_fst_of_ae_compProd P κ hloc
  have hmQ := ae_recentered_ball_mass_weightedRestriction_compProd P μ hμ hloc B hB w hw hε
  exact exists_observed_frequency_event_of_mass_approximations Q
    (fun x => (observe x.1, x.2)) ((hobserve.comp measurable_fst).prodMk measurable_snd)
    (fun x => μ x.1) ε hε hμQ hlocQ hmQ S hcount hgen hpi hsets f hf hlim
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit

#print axioms exists_observed_frequency_event_weightedRestriction_compProd

end HarmonicBalls
