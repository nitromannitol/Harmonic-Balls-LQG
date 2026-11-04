import HarmonicBalls.Proofs.Sec8.JointPhaseFrequencyTransfer
import HarmonicBalls.Proofs.Sec8.RootedSamplingBallMass

/-! # Rooted frequency from common local approximations

The phase-frequency development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Common mass approximations and an observed-law comparison transfer a
reference phase-frequency estimate to the centered count under a weighted
rooted law. Positivity of mass at the sampled root follows from local finiteness. -/
theorem ae_rooted_veryGoodComparableScaleFrequency_of_common_approximations
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (observe : Ω → F) (hobserve : Measurable observe)
    (R : Measure Ξ) (X : Ξ → F × ℂ) (hX : Measurable X)
    (ν : Ξ → Measure ℂ) (hν : Measurable ν)
    (ε : ℝ) (hε : 0 < ε)
    (hνpos : ∀ᵐ ω ∂ R, ν ω (ball 0 ε) ≠ 0 ∧ ν ω (ball 0 ε) ≠ ∞)
    (hdom : (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw).map
        (fun x => (observe x.1, x.2)) ≪ R.map X)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ A ∈ S, MeasurableSet A) (huniv : univ ∈ S)
    (f : S → ℕ → F × ℂ → ℝ) (hf : ∀ A n, Measurable (f A n))
    (href : ∀ A, TendstoInMeasure R (fun n ω => f A n (X ω)) atTop
      (fun ω => (normalizedRestriction (ν ω) (ball 0 ε) A.val).toReal))
    (hroot : ∀ A, TendstoInMeasure (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw)
      (fun n x => f A n (observe x.1, x.2)) atTop
      (fun x => (normalizedRestriction
        ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hfreq : ∀ᵐ ω ∂ R, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-(X ω).2))) ∧
        AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ)) :
    ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ x.1) β x.2 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  let Q := P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw
  let center : Ω × ℂ → Measure ℂ := fun x => (μ x.1).map (fun v : ℂ => v - x.2)
  have hc : AEMeasurable center Q :=
    (aemeasurable_recentered_of_weightedRestriction_compProd P μ hμ hloc B hB w hw).1
  let ν' := hc.mk center
  have hν' : Measurable ν' := hc.measurable_mk
  have heq : center =ᵐ[Q] ν' := hc.ae_eq_mk
  have hpos : ∀ᵐ x ∂Q, ν' x (ball 0 ε) ≠ 0 ∧ ν' x (ball 0 ε) ≠ ∞ := by
    filter_upwards [ae_recentered_ball_mass_weightedRestriction_compProd P μ hμ hloc B hB w hw hε,
      heq] with x hx he
    simpa only [center, he] using hx
  have hroot' : ∀ A, TendstoInMeasure Q (fun n x => f A n (observe x.1, x.2)) atTop
      (fun x => (normalizedRestriction (ν' x) (ball 0 ε) A.val).toReal) := by
    intro A
    apply (hroot A).congr_right
    filter_upwards [heq] with x hx
    simp only [← hx, center]
  have hY : Measurable (fun x : Ω × ℂ => (observe x.1, x.2)) :=
    (hobserve.comp measurable_fst).prodMk measurable_snd
  have hphase : Measurable (fun x : F × ℂ => phaseTorusOfComplex (-x.2)) :=
    measurable_phaseTorusOfComplex.comp measurable_snd.neg
  have htransfer := ae_phaseFrequency_of_common_mass_approximations
    R Q X (fun x : Ω × ℂ => (observe x.1, x.2)) hX hY ν ν' hν hν' ε hε
    hνpos hpos hdom S hcount hgen hpi hsets huniv f hf href hroot'
    (fun x : F × ℂ => phaseTorusOfComplex (-x.2)) hphase
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hfreq
  filter_upwards [htransfer, heq] with x hx he
  filter_upwards [hx] with N hN
  rw [veryGoodComparableScaleCount_eq_centered_torus]
  simpa only [center, he] using hN

#print axioms ae_rooted_veryGoodComparableScaleFrequency_of_common_approximations

end HarmonicBalls
