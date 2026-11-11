import HarmonicBalls.Proofs.Sec8.RootedCommonPhaseFrequency

/-! # Typical-point frequency from common local approximations

The phase-frequency development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization. -/

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Reference phase-frequency estimates and common local mass approximations,
one for each ball of an exhausting cover, imply the centered block-frequency
estimate at almost every point of the random measure. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_common_approximations
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (observe : Ω → F) (hobserve : Measurable observe)
    (R : ℕ → Measure Ξ) (X : ℕ → Ξ → F × ℂ) (hX : ∀ n, Measurable (X n))
    (ν : ℕ → Ξ → Measure ℂ) (hν : ∀ n, Measurable (ν n))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n)
    (hνpos : ∀ n, ∀ᵐ ω ∂(R n), ν n ω (ball 0 (ε n)) ≠ 0 ∧
      ν n ω (ball 0 (ε n)) ≠ ∞)
    (hdom : ∀ (n : ℕ), (P ⊗ₘ weightedRestrictionKernel P μ hμ
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
  let B : ℕ → Set ℂ := fun n => ball 0 ((n : ℝ) + 1)
  have hB : ∀ n, MeasurableSet (B n) := fun _ => measurableSet_ball
  have hcover : ∀ z, ∃ n, z ∈ B n := by
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    refine ⟨n, ?_⟩
    change z ∈ ball 0 ((n : ℝ) + 1)
    rw [mem_ball_zero_iff]
    linarith
  let w : ℕ → ℂ → ℝ≥0∞ := fun _ _ => 1
  have hw : ∀ n, Measurable (w n) := fun _ => measurable_const
  have hpos : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (B n), w n z ≠ 0 := by
    intro n
    exact Filter.Eventually.of_forall fun _ => Filter.Eventually.of_forall fun _ => one_ne_zero
  have hfin : ∀ n, ∀ᵐ ω ∂P, ((μ ω).withDensity (w n)) (B n) ≠ ∞ := by
    intro n
    filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    simpa only [w, withDensity_const, one_smul, B] using
      (measure_ball_lt_top.ne : (μ ω) (ball 0 ((n : ℝ) + 1)) ≠ ∞)
  apply ae_ae_of_rooted_weighted_cover_of_aemeasurable P μ hμ B hB hcover w hw hpos hfin
    (fun n => P ⊗ₘ weightedRestrictionKernel P μ hμ (B n) (hB n) (w n) (hw n))
    (fun _ => Measure.AbsolutelyContinuous.rfl)
  intro n
  exact ae_rooted_veryGoodComparableScaleFrequency_of_common_approximations
    P μ hμ hloc (B n) (hB n) (w n) (hw n) observe hobserve
    (R n) (X n) (hX n) (ν n) (hν n) (ε n) (hε n) (hνpos n) (hdom n)
    (S n) (hcount n) (hgen n) (hpi n) (hsets n) (huniv n) (f n) (hf n)
    (href n) (hroot n) β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit (hfreq n)

end HarmonicBalls
