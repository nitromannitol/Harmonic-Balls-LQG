import HarmonicBalls.Proofs.Sec8.TypicalCommonPhaseFrequency
import HarmonicBalls.Proofs.Sec8.RootedSamplingEquivalence

/-! # Typical-point frequency from unnormalized rooted observations

The imported phase-frequency development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- The rooted observation comparison may be stated for the unnormalized
law on each ball, as in rooted-field change of measure. Local finiteness
transfers it to the normalized sampling law. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_unnormalized_observation
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (observe : Ω → F) (hobserve : Measurable observe)
    (R : ℕ → Measure Ξ) (X : ℕ → Ξ → F × ℂ) (hX : ∀ n, Measurable (X n))
    (ν : ℕ → Ξ → Measure ℂ) (hν : ∀ n, Measurable (ν n))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hνpos : ∀ n, ∀ᵐ ω ∂(R n), ν n ω (ball 0 (ε n)) ≠ 0 ∧
      ν n ω (ball 0 (ε n)) ≠ ∞)
    (hdom : ∀ (n : ℕ), (P ⊗ₘ unnormalizedWeightedRestrictionKernel P μ hμ
      (ball 0 ((n : ℝ) + 1)) measurableSet_ball (fun _ => 1) measurable_const).map
        (fun x => (observe x.1, x.2)) ≪ (R n).map (X n))
    (S : ℕ → Set (Set ℂ)) (hcount : ∀ n, (S n).Countable)
    (hgen : ∀ n, (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom (S n))
    (hpi : ∀ n, IsPiSystem (S n)) (hsets : ∀ n A, A ∈ S n → MeasurableSet A)
    (huniv : ∀ n, univ ∈ S n)
    (f : (n : ℕ) → S n → ℕ → F × ℂ → ℝ) (hf : ∀ n A k, Measurable (f n A k))
    (href : ∀ n A, TendstoInMeasure (R n) (fun k ω => f n A k (X n ω)) atTop
      (fun ω => (normalizedRestriction (ν n ω) (ball 0 (ε n)) A.val).toReal))
    (hroot : ∀ (n : ℕ) A, TendstoInMeasure
      (P ⊗ₘ weightedRestrictionKernel P μ hμ (ball 0 ((n : ℝ) + 1))
        measurableSet_ball (fun _ => 1) measurable_const)
      (fun k x => f n A k (observe x.1, x.2)) atTop
      (fun x => (normalizedRestriction
        ((μ x.1).map (fun v : ℂ => v - x.2)) (ball 0 (ε n)) A.val).toReal))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b})
    (hfreq : ∀ n, ∀ᵐ ω ∂(R n), ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ ({k : ℕ | k ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (ν n ω) β (dyadicScale k) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-(X n ω).2))) ∧
        AnnulusBallComparison (ν n ω) k 0 m}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  have hY : Measurable (fun x : Ω × ℂ => (observe x.1, x.2)) :=
    (hobserve.comp measurable_fst).prodMk measurable_snd
  have hnormdom : ∀ (n : ℕ), (P ⊗ₘ weightedRestrictionKernel P μ hμ
      (ball 0 ((n : ℝ) + 1)) measurableSet_ball (fun _ => 1) measurable_const).map
        (fun x => (observe x.1, x.2)) ≪ (R n).map (X n) := by
    intro n
    have hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1))
        (ball 0 ((n : ℝ) + 1)) ≠ ∞ := by
      filter_upwards [hloc] with ω hω
      let : IsLocallyFiniteMeasure (μ ω) := hω
      simpa only [withDensity_const, one_smul] using
        (measure_ball_lt_top.ne : (μ ω) (ball 0 ((n : ℝ) + 1)) ≠ ∞)
    exact ((weightedRestrictionKernel_compProd_ac_canonical P μ hμ _
      measurableSet_ball (fun _ => 1) measurable_const hfin).map hY).trans (hdom n)
  exact ae_ae_veryGoodComparableScaleFrequency_of_common_approximations
    P μ hμ hloc observe hobserve R X hX ν hν ε hε hνpos hnormdom
    S hcount hgen hpi hsets huniv f hf href hroot
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit hfreq

end HarmonicBalls
