import HarmonicBalls.Proofs.Sec8.MeasurableCompactTests
import HarmonicBalls.Proofs.Sec8.PointPolarityApproximation

/-! # Measurability of good annuli with positive mass threshold -/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- On a positive finite-mass set, the normalized restriction has the same
null measurable subsets as the original measure. -/
theorem normalizedRestriction_eq_zero_iff (μ : Measure ℂ) {A V : Set ℂ}
    (hV : MeasurableSet V) (hVA : V ⊆ A) (ht : μ A ≠ ∞) :
    normalizedRestriction μ A V = 0 ↔ μ V = 0 := by
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hV, inter_eq_left.mpr hVA, mul_eq_zero,
    ENNReal.inv_ne_zero.mpr ht, false_or]

open MarkovProcess in
/-- For positive finite annulus mass, a bad annulus either fails a strict
compact test or has a concentrated bad witness at a threshold-sized atom. -/
theorem isGoodAnnulus_iff_compact_and_no_concentrated_witness
    (μ : Measure ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hz : μ (annulus z (3*r) (5*r)) ≠ 0)
    (ht : μ (annulus z (3*r) (5*r)) ≠ ∞)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    IsGoodAnnulus μ r z a b ↔
      (∀ K : Set ℂ, IsCompact K → K ⊆ annulus z (3 * r) (5 * r) →
        μ (annulus z (3 * r) (5 * r) \ K) <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (annulus z (3 * r) (5 * r) \ K) p} ≤ ENNReal.ofReal b) ∧
      ¬ (∃ u ∈ sphere z (4 * r),
        normalizedRestriction μ (annulus z (3*r) (5*r)) {u} = ENNReal.ofReal a ∧
        ∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ annulus z (3*r) (5*r) ∧
          normalizedRestriction μ (annulus z (3*r) (5*r)) (Y \ {u}) = 0 ∧
          ENNReal.ofReal b < planarBrownianMotion u
            {p | ContinuousPath.exitTime (annulus z (3*r) (5*r)) p ≤
              ContinuousPath.exitTime Y p}) := by
  let A := annulus z (3*r) (5*r)
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hSA : sphere z (4*r) ⊆ A := by
    intro u hu
    have hd := mem_sphere.mp hu
    change dist u z < 5*r ∧ ¬ dist u z ≤ 3*r
    rw [hd]
    constructor <;> linarith
  constructor
  · intro hg
    refine ⟨(isGoodAnnulus_iff_compact_and_concentrated_tests μ r hr z a b ht hsmall).1 hg |>.1, ?_⟩
    rintro ⟨u, hu, hatom, Y, hY, hYA, hnull, hp⟩
    have hatom' : μ {u} = ENNReal.ofReal a * μ A :=
      (normalizedRestriction_singleton_eq_iff μ (hSA hu) hz ht _).1 hatom
    have hnull' : μ (Y \ {u}) = 0 :=
      (normalizedRestriction_eq_zero_iff μ (hY.diff (measurableSet_singleton u))
        (sdiff_subset.trans hYA) ht).1 hnull
    have hmass : μ Y ≤ ENNReal.ofReal a * μ A := by
      calc
        μ Y ≤ μ (Y \ {u}) + μ {u} :=
          (measure_mono (show Y ⊆ (Y \ {u}) ∪ {u} from by intro x hx; by_cases h : x = u <;> simp [hx, h])).trans
            (measure_union_le _ _)
        _ = ENNReal.ofReal a * μ A := by rw [hnull', zero_add, hatom']
    exact (not_le_of_gt hp) (hg Y hY hYA hmass u hu)
  · rintro ⟨hcomp, hnot⟩
    by_contra hbad
    obtain ⟨Y, hY, hYA, u, hu, huY, hatom, hnull, hp⟩ :=
      exists_threshold_atom_badWitness_of_compact_tests μ r hr z a b ht hsmall hcomp hbad
    have hatom' : normalizedRestriction μ A {u} = ENNReal.ofReal a :=
      (normalizedRestriction_singleton_eq_iff μ (hSA hu) hz ht _).2 hatom
    have hnull' : normalizedRestriction μ A (Y \ {u}) = 0 :=
      (normalizedRestriction_eq_zero_iff μ (hY.diff (measurableSet_singleton u))
        (sdiff_subset.trans hYA) ht).2 hnull
    exact hnot ⟨u, hu, hatom', Y, hY, hYA, hnull', hp⟩

open MarkovProcess in
/-- At positive mass threshold, the good-annulus event is Borel for arbitrary
measures, assuming the interior small-ball hitting estimate. -/
theorem measurableSet_isGoodAnnulus_of_smallBall
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} := by
  by_cases hb : 1 ≤ b
  · have heq : {μ : Measure ℂ | IsGoodAnnulus μ r z a b} = univ := by
      ext μ
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact isGoodAnnulus_of_one_le μ r z a hb
    rw [heq]
    exact MeasurableSet.univ
  have hblt : b < 1 := lt_of_not_ge hb
  let A := annulus z (3*r) (5*r)
  let S := sphere z (4*r)
  have hA : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hSA : S ⊆ A := by
    intro u hu
    have hd := mem_sphere.mp hu
    change dist u z < 5*r ∧ ¬ dist u z ≤ 3*r
    rw [hd]
    constructor <;> linarith
  let C : Set (Measure ℂ) := {μ | μ A ≠ 0 ∧ μ A ≠ ∞}
  let T : Set (Measure ℂ) := {μ | ∀ K : Set ℂ, IsCompact K → K ⊆ A →
    μ (A \ K) < ENNReal.ofReal a * μ A →
    ∀ u ∈ S, planarBrownianMotion u {p | ContinuousPath.exitTime A p ≤
      ContinuousPath.exitTime (A \ K) p} ≤ ENNReal.ofReal b}
  let W : Set (Measure ℂ) := {μ | ∃ u ∈ S,
    normalizedRestriction μ A {u} = ENNReal.ofReal a ∧
    ∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ A ∧
      normalizedRestriction μ A (Y \ {u}) = 0 ∧
      ENNReal.ofReal b < planarBrownianMotion u {p |
        ContinuousPath.exitTime A p ≤ ContinuousPath.exitTime Y p}}
  have hm : Measurable (fun μ : Measure ℂ => μ A) := Measure.measurable_coe hA.measurableSet
  have hC : MeasurableSet C := (hm (measurableSet_singleton 0)).compl.inter
    (hm (measurableSet_singleton ∞)).compl
  have hT : MeasurableSet T := measurableSet_compact_obstacle_tests r hr z a b
  have hW : MeasurableSet W := measurableSet_exists_concentrated_survival_at_threshold_atom
    A S A hA (isBounded_ball.subset sdiff_subset) isClosed_sphere.measurableSet hSA
    hA.measurableSet (ENNReal.ofReal a) (ENNReal.ofReal b) (ENNReal.ofReal_pos.mpr ha)
  have heq : {μ : Measure ℂ | IsGoodAnnulus μ r z a b} = C ∩ T ∩ Wᶜ := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, C, T, W]
    constructor
    · intro hg
      have hc := isGoodAnnulus_annulus_mass_ne_zero_ne_top μ hr.le z ha hblt hg
      have ht := (isGoodAnnulus_iff_compact_and_no_concentrated_witness
        μ r hr z a b hc.1 hc.2 hsmall).1 hg
      exact ⟨⟨hc, ht.1⟩, ht.2⟩
    · rintro ⟨⟨hc, ht⟩, hw⟩
      exact (isGoodAnnulus_iff_compact_and_no_concentrated_witness
        μ r hr z a b hc.1 hc.2 hsmall).2 ⟨ht, hw⟩
  rw [heq]
  exact (hC.inter hT).inter hW.compl

open MarkovProcess in
/-- Point avoidance implies good-annulus measurability at every positive mass
threshold, for all measures and every probability threshold. -/
theorem measurableSet_isGoodAnnulus_of_ae_point_avoidance
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere z (4*r), ∀ x ∈ annulus z (3*r) (5*r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} :=
  measurableSet_isGoodAnnulus_of_smallBall r hr z a b ha
    (annulus_smallBallHitting_of_ae_point_avoidance r hr z hpolar)

open MarkovProcess in
/-- Point avoidance also yields measurability of the origin-centered very-good
annulus event at every positive mass threshold. -/
theorem measurableSet_isVeryGoodAnnulus_zero_of_ae_point_avoidance
    (β ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    MeasurableSet {μ : Measure ℂ |
      IsVeryGoodAnnulus μ β ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} := by
  apply measurableSet_isVeryGoodAnnulus_zero_of_unit_good β ρ hρ N₀
    a b C₁m C₁p C₂m C₂p C₃
  apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha
  simpa using hpolar

end HarmonicBalls
