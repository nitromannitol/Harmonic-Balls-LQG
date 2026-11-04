import HarmonicBalls.Proofs.Sec6.MeasurePushforwardJoint
import HarmonicBalls.Proofs.Sec6.SizeRatioTranslationLaw
import HarmonicBalls.Proofs.Sec8.GoodEventMeasurablePositive

/-! # Joint measurability of very-good annuli

The countable lattice in the definition stays fixed as the centre varies.
These results prepare the measurable block-frequency event for rooted measures.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The good-scale condition is measurable jointly in the measure and centre;
the lattice is fixed in the plane. -/
theorem measurableSet_veryGoodAnnulus_goodScales_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hc : Measurable c) (ρ : ℝ) (hρ : 0 < ρ)
    (N₀ : ℕ) (a b C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {x : A |
      ∀ n : ℕ, N₀ ≤ n → ∀ z ∈ annulus (c x) (ρ / 2) ρ,
        (∃ j k : ℤ, z = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
          ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ x) r z a b}.ncard : ℝ)} := by
  let z : ℕ → ℤ → ℤ → ℂ := fun n j k =>
    ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)
  let T : ℕ → ℤ → ℤ → Set A := fun n j k => {x |
    (N₀ ≤ n ∧ z n j k ∈ annulus (c x) (ρ / 2) ρ) →
      C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
          (∃ l : ℕ, 1 ≤ l ∧ r = ρ * (7 : ℝ)⁻¹ ^ l) ∧
            IsGoodAnnulus (μ x) r (z n j k) a b}.ncard : ℝ)}
  have hT : ∀ n j k, MeasurableSet (T n j k) := by
    intro n j k
    have hg : ∀ l : ℕ, MeasurableSet {ν : Measure ℂ |
        IsGoodAnnulus ν (ρ * (7 : ℝ)⁻¹ ^ l) (z n j k) a b} := by
      intro l
      apply measurableSet_isGoodAnnulus_of_unit a b hunit
      positivity
    have hcount := (measurable_goodAnnulus_radius_count ρ hρ n (z n j k) a b hg).comp hμ
    by_cases hn : N₀ ≤ n
    · have hz : MeasurableSet {x : A | z n j k ∈ annulus (c x) (ρ / 2) ρ} := by
        have hdist : Measurable (fun x : A => dist (z n j k) (c x)) := measurable_const.dist hc
        convert (measurableSet_lt hdist (measurable_const : Measurable (fun _ : A => ρ))).inter
          (measurableSet_lt (measurable_const : Measurable (fun _ : A => ρ / 2)) hdist) using 1
        ext x
        simp [annulus, mem_ball, mem_closedBall, not_le]
      have hbound := measurableSet_le
        (measurable_const : Measurable (fun _ : A => C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))))) hcount
      convert hz.compl.union hbound using 1
      ext x
      simp only [T, mem_ofPred_eq, hn, true_and, mem_union, mem_compl_iff, imp_iff_not_or, Function.comp_apply]
    · simp only [T, hn, false_and, false_implies, ofPred_true, MeasurableSet.univ]
  have heq : {x : A |
      ∀ n : ℕ, N₀ ≤ n → ∀ w ∈ annulus (c x) (ρ / 2) ρ,
        (∃ j k : ℤ, w = ((dyadicScale n * ρ / 100 : ℝ) : ℂ) *
          ((j : ℂ) + (k : ℂ) * Complex.I)) →
        C₃ * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
          ({r : ℝ | r ∈ Icc (dyadicScale n * ρ) (Real.sqrt (dyadicScale n) * ρ) ∧
            (∃ k : ℕ, 1 ≤ k ∧ r = ρ * (7 : ℝ)⁻¹ ^ k) ∧
              IsGoodAnnulus (μ x) r w a b}.ncard : ℝ)} = ⋂ n, ⋂ j, ⋂ k, T n j k := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter, T]
    constructor
    · intro h n j k ⟨hn, hz⟩
      exact h n hn (z n j k) hz ⟨j, k, rfl⟩
    · intro h n hn w hw hlat
      obtain ⟨j, k, heq⟩ := hlat
      subst w
      exact h n j k ⟨hn, hw⟩
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun k => hT n j k

/-- Both size ratios are measurable jointly in a locally finite measure
and its centre. -/
theorem measurable_veryGoodAnnulus_sizeRatios_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (β ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (fun x => annulusBallMassSize (μ x) β ρ (c x) /
      (μ x) (annulus (c x) (ρ / 4) (2 * ρ))) ∧
    Measurable (fun x => annulusGreenPotentialSup (μ x) (c x) (ρ / 4) (2 * ρ) /
      (μ x) (annulus (c x) (ρ / 4) (2 * ρ))) := by
  let ν : A → Measure ℂ := fun x => (μ x).map (fun z => z - c x)
  have hν : Measurable ν := Section6.measurable_map_of_locallyFinite hμ hfinite
    (measurable_snd.sub (hc.comp measurable_fst))
  constructor
  · have hm := (measurable_annulusBallMassSize_ratio β ρ 0 hρ).comp hν
    convert hm using 1
    funext x
    simp only [Function.comp_apply, ν, Section6.annulusBallMassSize_map_sub,
      Section6.map_sub_annulus]
  · have hm := (measurable_annulusGreenPotentialRatio_zero ρ).comp hν
    convert hm using 1
    funext x
    simp only [Function.comp_apply, ν, Section6.annulusGreenPotentialSup_map_sub,
      Section6.map_sub_annulus]

/-- The very-good-annulus event is jointly measurable in a locally finite
measure and the centre, whenever the unit good-annulus event is measurable. -/
theorem measurableSet_isVeryGoodAnnulus_joint_of_unit_good
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (β ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {x : A | IsVeryGoodAnnulus (μ x) β ρ (c x) N₀
      a b C₁m C₁p C₂m C₂p C₃} := by
  obtain ⟨hball, hgreen⟩ := measurable_veryGoodAnnulus_sizeRatios_joint hμ hfinite hc β ρ hρ
  unfold IsVeryGoodAnnulus
  exact (isClosed_Icc.measurableSet.preimage hball).inter
    ((isClosed_Icc.measurableSet.preimage hgreen).inter
      (measurableSet_veryGoodAnnulus_goodScales_joint hμ hc ρ hρ N₀ a b C₃ hunit))

open MarkovProcess in
/-- Point avoidance gives joint measurability at every positive mass threshold. -/
theorem measurableSet_isVeryGoodAnnulus_joint_of_ae_point_avoidance
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (β ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    MeasurableSet {x : A | IsVeryGoodAnnulus (μ x) β ρ (c x) N₀
      a b C₁m C₁p C₂m C₂p C₃} := by
  apply measurableSet_isVeryGoodAnnulus_joint_of_unit_good hμ hfinite hc β ρ hρ N₀
    a b C₁m C₁p C₂m C₂p C₃
  apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha
  simpa using hpolar

/-- The annulus-ball comparison event is measurable jointly in a locally
finite measure and its centre. -/
theorem measurableSet_annulusBallComparison_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (n : ℕ) (m : ℝ) :
    MeasurableSet {x : A | AnnulusBallComparison (μ x) n (c x) m} := by
  let ν : A → Measure ℂ := fun x => (μ x).map (fun z => z - c x)
  have hν : Measurable ν := Section6.measurable_map_of_locallyFinite hμ hfinite
    (measurable_snd.sub (hc.comp measurable_fst))
  have hball : Measurable (fun x => (μ x) (ball (c x) (dyadicScale n))) := by
    have hm := (Measure.measurable_coe (isOpen_ball.measurableSet :
      MeasurableSet (ball (0 : ℂ) (dyadicScale n)))).comp hν
    convert hm using 1
    funext x
    change (μ x) (ball (c x) (dyadicScale n)) =
      ((μ x).map (fun z => z - c x)) (ball 0 (dyadicScale n))
    rw [Measure.map_apply (by fun_prop) isOpen_ball.measurableSet]
    congr 1
    ext z
    simp [mem_ball, dist_eq_norm]
  have hann : Measurable (fun x => (μ x)
      (annulus (c x) (dyadicScale (n + 1)) (dyadicScale n))) := by
    have hm := (Measure.measurable_coe ((isOpen_ball.sdiff isClosed_closedBall).measurableSet :
      MeasurableSet (annulus (0 : ℂ) (dyadicScale (n + 1)) (dyadicScale n)))).comp hν
    convert hm using 1
    funext x
    change (μ x) (annulus (c x) (dyadicScale (n + 1)) (dyadicScale n)) =
      ((μ x).map (fun z => z - c x)) (annulus 0 (dyadicScale (n + 1)) (dyadicScale n))
    rw [Section6.map_sub_annulus]
  exact measurableSet_le (measurable_const.mul hball) hann

/-- The block count of very-good comparable scales is jointly measurable. -/
theorem measurable_veryGoodComparableScaleCount_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) (N : ℕ) :
    Measurable (fun x => veryGoodComparableScaleCount (μ x) β (c x) N₀
      a b C₁m C₁p C₂m C₂p C₃ m N) := by
  let S : A → Set ℕ := fun x => {n | n ∈ Icc (N + 1) (2 * N) ∧
    IsVeryGoodAnnulus (μ x) β (dyadicScale n) (c x) N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
    AnnulusBallComparison (μ x) n (c x) m}
  have hS : Measurable S := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro n
    apply measurableSet_setOfPred.mp
    by_cases hn : n ∈ Icc (N + 1) (2 * N)
    · simp only [hn, true_and]
      exact (measurableSet_isVeryGoodAnnulus_joint_of_unit_good hμ hfinite hc β
        (dyadicScale n) (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ hunit).inter
        (measurableSet_annulusBallComparison_joint hμ hfinite hc n m)
    · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
  exact measurable_ncard.comp hS

/-- The eventual block-frequency event is jointly measurable. -/
theorem measurableSet_eventually_veryGoodComparableScaleCount_joint
    {A : Type*} [MeasurableSpace A] {μ : A → Measure ℂ} {c : A → ℂ}
    (hμ : Measurable μ) (hfinite : ∀ x, IsLocallyFiniteMeasure (μ x))
    (hc : Measurable c) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b}) :
    MeasurableSet {x : A | ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (μ x) β (c x) N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)} := by
  have hN (N : ℕ) : MeasurableSet {x : A | (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (μ x) β (c x) N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)} :=
    measurableSet_le measurable_const
      (Measurable.of_discrete.comp (measurable_veryGoodComparableScaleCount_joint hμ hfinite hc β N₀
        a b C₁m C₁p C₂m C₂p C₃ m hunit N))
  have heq : {x : A | ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (μ x) β (c x) N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)} =
      ⋃ K : ℕ, ⋂ N : ℕ, ⋂ (_ : K ≤ N), {x : A | (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ x) β (c x) N₀
          a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, eventually_atTop]
  rw [heq]
  exact MeasurableSet.iUnion fun K => MeasurableSet.iInter fun N =>
    MeasurableSet.iInter fun _ => hN N

end HarmonicBalls
