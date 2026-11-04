import HarmonicBalls.Proofs.Sec8.SurvivalLimsup

/-! # Measurable tests for concentrated survival -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The mass of a fixed Borel set away from a variable point is jointly
measurable in that point and the normalized measure. -/
theorem measurable_normalizedRestriction_sdiff_singleton
    (A V : Set ℂ) (hA : MeasurableSet A) (hV : MeasurableSet V) :
    Measurable (fun p : Measure ℂ × ℂ => normalizedRestriction p.1 A (V \ {p.2})) := by
  let κ : Kernel (Measure ℂ × ℂ) ℂ :=
    (normalizedRestrictionKernel A hA).comap Prod.fst measurable_fst
  have hE : MeasurableSet {q : (Measure ℂ × ℂ) × ℂ | q.2 ∈ V ∧ q.2 ≠ q.1.2} :=
    (hV.preimage measurable_snd).inter
      (measurableSet_eq_fun measurable_snd (measurable_snd.comp measurable_fst)).compl
  have h := Kernel.measurable_kernel_prodMk_left (κ := κ) hE
  convert h using 1
  ext p
  simp only [κ, normalizedRestrictionKernel, Kernel.comap_apply]
  congr 1

open MarkovProcess in
/-- For a countable center set and fixed probability threshold, all rational
obstacle tests form a jointly measurable condition on the measure and starting point. -/
theorem measurableSet_concentrated_rational_obstacle_tests
    (D U : Set ℂ) [Countable D] (hU : IsOpen U)
    (A : Set ℂ) (hA : MeasurableSet A) (c : ℝ≥0∞) (ε : ℕ → ℝ≥0∞) :
    MeasurableSet {p : Measure ℂ × ℂ | ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction p.1 A ((U \ rationalBallObstacle D s) \ {p.2}) < ε n ∧
      c ≤ planarBrownianMotion p.2 {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} := by
  simp only [ofPred_forall, ofPred_exists]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro s
  have hmass : Measurable (fun p : Measure ℂ × ℂ => normalizedRestriction p.1 A
      ((U \ rationalBallObstacle D s) \ {p.2})) :=
    measurable_normalizedRestriction_sdiff_singleton A _ hA
      (hU.measurableSet.diff (isCompact_rationalBallObstacle D s).measurableSet)
  have hprob : Measurable (fun u : ℂ => planarBrownianMotion u {path |
      ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}) :=
    (Measure.measurable_coe (Section6.measurableSet_avoid_before_exit hU
      (isCompact_rationalBallObstacle D s))).comp planarBrownianMotion.measurable
  by_cases h : rationalBallObstacle D s ⊆ U
  · simpa only [h, true_and, ofPred_and, Function.comp_apply] using
      (measurableSet_lt hmass measurable_const).inter
        (measurableSet_le measurable_const (hprob.comp measurable_snd))
  · simp [h]

open MarkovProcess in
/-- A fixed-threshold concentrated obstacle test at some threshold-sized atom
is measurable, by integrating its Borel graph against the normalized measure. -/
theorem measurableSet_exists_threshold_atom_obstacle_tests
    (D U S A : Set ℂ) [Countable D] (hU : IsOpen U) (hS : MeasurableSet S)
    (hA : MeasurableSet A) (a c : ℝ≥0∞) (ha : 0 < a) (ε : ℕ → ℝ≥0∞) :
    MeasurableSet {μ : Measure ℂ | ∃ u ∈ S,
      normalizedRestriction μ A {u} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction μ A ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c ≤ planarBrownianMotion u {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} := by
  let E : Set (Measure ℂ × ℂ) := {p | p.2 ∈ S ∧
    normalizedRestriction p.1 A {p.2} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction p.1 A ((U \ rationalBallObstacle D s) \ {p.2}) < ε n ∧
      c ≤ planarBrownianMotion p.2 {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}}
  have hE : MeasurableSet E := (hS.preimage measurable_snd).inter
    ((measurableSet_eq_fun (measurable_normalizedRestriction_singleton A hA) measurable_const).inter
      (measurableSet_concentrated_rational_obstacle_tests D U hU A hA c ε))
  let κ := normalizedRestrictionKernel A hA
  have heval : Measurable fun μ => κ μ (Prod.mk μ ⁻¹' E) :=
    Kernel.measurable_kernel_prodMk_left hE
  have heq : {μ : Measure ℂ | ∃ u ∈ S,
      normalizedRestriction μ A {u} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction μ A ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c ≤ planarBrownianMotion u {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} =
      {μ | 0 < κ μ (Prod.mk μ ⁻¹' E)} := by
    ext μ
    constructor
    · rintro ⟨u, hu, hmass, htest⟩
      have huE : u ∈ Prod.mk μ ⁻¹' E := ⟨hu, hmass, htest⟩
      have hle : normalizedRestriction μ A {u} ≤ κ μ (Prod.mk μ ⁻¹' E) :=
        measure_mono (singleton_subset_iff.mpr huE)
      have hpos : 0 < normalizedRestriction μ A {u} := by simpa [hmass] using ha
      exact hpos.trans_le hle
    · intro hp
      have hne : (Prod.mk μ ⁻¹' E).Nonempty := by
        by_contra hn
        have hz : Prod.mk μ ⁻¹' E = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
        simp [hz] at hp
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, hu.1, hu.2⟩
  rw [heq]
  exact measurableSet_lt measurable_const heval

open MarkovProcess in
/-- The threshold-atom tests remain measurable after a countable choice of
strict survival thresholds. -/
theorem measurableSet_exists_countable_threshold_atom_tests
    (D U S A : Set ℂ) [Countable D] (hU : IsOpen U) (hS : MeasurableSet S)
    (hA : MeasurableSet A) (a b : ℝ≥0∞) (ha : 0 < a) (ε : ℕ → ℝ≥0∞)
    (C : Set ℝ≥0∞) (hC : C.Countable) :
    MeasurableSet {μ : Measure ℂ | ∃ c ∈ C, b < c ∧ ∃ u ∈ S,
      normalizedRestriction μ A {u} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction μ A ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c ≤ planarBrownianMotion u {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} := by
  let : Countable C := hC.to_subtype
  have heq : {μ : Measure ℂ | ∃ c ∈ C, b < c ∧ ∃ u ∈ S,
      normalizedRestriction μ A {u} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction μ A ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c ≤ planarBrownianMotion u {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} =
      ⋃ c : C, {μ | b < c.1 ∧ ∃ u ∈ S,
      normalizedRestriction μ A {u} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction μ A ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c.1 ≤ planarBrownianMotion u {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iUnion]
    exact ⟨fun ⟨c, hc, h⟩ => ⟨⟨c, hc⟩, h⟩, fun ⟨c, h⟩ => ⟨c.1, c.2, h⟩⟩
  rw [heq]
  apply MeasurableSet.iUnion
  intro c
  by_cases hbc : b < c.1
  · simpa only [hbc, true_and] using
      measurableSet_exists_threshold_atom_obstacle_tests D U S A hU hS hA a c.1 ha ε
  · simp [hbc]

open MarkovProcess in
/-- Existence of a concentrated survival witness at a threshold-sized atom is
Borel as a property of the normalized measure. -/
theorem measurableSet_exists_concentrated_survival_at_threshold_atom
    (U S A : Set ℂ) (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hS : MeasurableSet S) (hSU : S ⊆ U) (hA : MeasurableSet A)
    (a b : ℝ≥0∞) (ha : 0 < a) :
    MeasurableSet {μ : Measure ℂ | ∃ u ∈ S, normalizedRestriction μ A {u} = a ∧
      ∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ U ∧
        normalizedRestriction μ A (Y \ {u}) = 0 ∧
        b < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime Y p}} := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable D := hDc.to_subtype
  obtain ⟨C, hCc, hC⟩ := TopologicalSpace.exists_countable_dense ℝ≥0∞
  let ε : ℕ → ℝ≥0∞ := fun n => (2⁻¹ : ℝ≥0∞) ^ n
  have hε : ∀ n, 0 < ε n := fun n => by
    have hhalf : (0 : ℝ≥0∞) < 2⁻¹ := by norm_num
    exact pos_iff_ne_zero.mpr (pow_ne_zero n (ne_of_gt hhalf))
  have hεsum : (∑' n, ε n) ≠ ∞ := by simp [ε]
  have hmeas := measurableSet_exists_countable_threshold_atom_tests
    D U S A hU hS hA a b ha ε C hCc
  have heq : {μ : Measure ℂ | ∃ u ∈ S, normalizedRestriction μ A {u} = a ∧
      ∃ Y : Set ℂ, MeasurableSet Y ∧ Y ⊆ U ∧
        normalizedRestriction μ A (Y \ {u}) = 0 ∧
        b < planarBrownianMotion u {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime Y p}} =
      {μ | ∃ c ∈ C, b < c ∧ ∃ u ∈ S,
      normalizedRestriction μ A {u} = a ∧ ∀ n, ∃ s : Finset (D × ℚ),
      rationalBallObstacle D s ⊆ U ∧
      normalizedRestriction μ A ((U \ rationalBallObstacle D s) \ {u}) < ε n ∧
      c ≤ planarBrownianMotion u {path | ContinuousPath.exitTime U path ≤
        ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ path}} := by
    ext μ
    have hfin : IsFiniteMeasure (normalizedRestriction μ A) := by
      change IsFiniteMeasure (normalizedRestrictionKernel A hA μ)
      infer_instance
    constructor
    · rintro ⟨u, hu, hatom, hwitness⟩
      obtain ⟨c, hbc, htests⟩ :=
        (exists_concentrated_survival_iff_rational_obstacles hD hU hbounded
          (normalizedRestriction μ A) (measure_ne_top _ _) u (hSU hu) b ε hε hεsum).1 hwitness
      obtain ⟨d, hdC, hbd, hdc⟩ := hC.exists_between hbc
      refine ⟨d, hdC, hbd, u, hu, hatom, fun n => ?_⟩
      obtain ⟨s, hsU, hmass, hprob⟩ := htests n
      exact ⟨s, hsU, hmass, hdc.le.trans hprob⟩
    · rintro ⟨c, hcC, hbc, u, hu, hatom, htests⟩
      refine ⟨u, hu, hatom, ?_⟩
      exact (exists_concentrated_survival_iff_rational_obstacles hD hU hbounded
        (normalizedRestriction μ A) (measure_ne_top _ _) u (hSU hu) b ε hε hεsum).2
          ⟨c, hbc, htests⟩
  rw [heq]
  exact hmeas

end HarmonicBalls
