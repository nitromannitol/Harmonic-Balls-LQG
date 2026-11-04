import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios
import HarmonicBalls.Proofs.Sec8.AtomicCountableObstacles
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.Probability.Kernel.Composition.MapComap

/-! # Measurable masses of starting atoms -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The normalized restriction is a measurable function of the measure. -/
theorem measurable_normalizedRestriction_measure (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun μ : Measure ℂ => normalizedRestriction μ A) := by
  apply measurable_normalizedRestriction _ A
  intro V hV
  exact (Measure.measurable_coe (hV.measurableSet.inter hA)).div (Measure.measurable_coe hA)

/-- A normalized restriction is a uniformly finite kernel of the original measure. -/
noncomputable def normalizedRestrictionKernel (A : Set ℂ) (hA : MeasurableSet A) :
    Kernel (Measure ℂ) ℂ := ⟨fun μ => normalizedRestriction μ A,
      measurable_normalizedRestriction_measure A hA⟩

instance normalizedRestrictionKernel_finite (A : Set ℂ) (hA : MeasurableSet A) :
    IsFiniteKernel (normalizedRestrictionKernel A hA) where
  exists_univ_le := by
    refine ⟨1, by simp, ?_⟩
    intro μ
    change (normalizedRestriction μ A) univ ≤ 1
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    by_cases hz : μ A = 0
    · simp [hz]
    by_cases ht : μ A = ∞
    · simp [ht]
    simp [ENNReal.inv_mul_cancel hz ht]

/-- The mass of a singleton is jointly measurable in a normalized restriction
and the point at which it is evaluated. -/
theorem measurable_normalizedRestriction_singleton (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun p : Measure ℂ × ℂ => normalizedRestriction p.1 A {p.2}) := by
  let κ : Kernel (Measure ℂ × ℂ) ℂ :=
    (normalizedRestrictionKernel A hA).comap Prod.fst measurable_fst
  have hdiag : MeasurableSet {q : (Measure ℂ × ℂ) × ℂ | q.1.2 = q.2} :=
    measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_snd
  have h := Kernel.measurable_kernel_prodMk_left (κ := κ) hdiag
  convert h using 1
  ext p
  simp [κ, normalizedRestrictionKernel, eq_comm]

/-- For a fixed positive threshold, the absence of sufficiently large atoms
in a Borel set is measurable as a property of a normalized restriction. -/
theorem measurableSet_no_large_normalized_atoms
    (A S : Set ℂ) (hA : MeasurableSet A) (hS : MeasurableSet S)
    (c : ℝ≥0∞) (hc : 0 < c) :
    MeasurableSet {μ : Measure ℂ | ∀ x ∈ S, normalizedRestriction μ A {x} < c} := by
  let κ := normalizedRestrictionKernel A hA
  let E : Set (Measure ℂ × ℂ) := {p | p.2 ∈ S ∧ c ≤ normalizedRestriction p.1 A {p.2}}
  have hE : MeasurableSet E := (hS.preimage measurable_snd).inter
    (measurableSet_le measurable_const (measurable_normalizedRestriction_singleton A hA))
  have heval : Measurable fun μ => κ μ (Prod.mk μ ⁻¹' E) :=
    Kernel.measurable_kernel_prodMk_left hE
  have heq : {μ : Measure ℂ | ∀ x ∈ S, normalizedRestriction μ A {x} < c} =
      {μ : Measure ℂ | κ μ (Prod.mk μ ⁻¹' E) = 0} := by
    ext μ
    constructor
    · intro h
      have hempty : Prod.mk μ ⁻¹' E = ∅ := by
        ext x
        simp only [mem_preimage, E, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hx, hxlarge⟩
        exact (not_le_of_gt (h x hx)) hxlarge
      simp [hempty]
    · intro hz x hx
      by_contra hn
      have hxE : x ∈ Prod.mk μ ⁻¹' E := ⟨hx, le_of_not_gt hn⟩
      have hbound : normalizedRestriction μ A {x} ≤ κ μ (Prod.mk μ ⁻¹' E) :=
        measure_mono (singleton_subset_iff.mpr hxE)
      have hlarge : c ≤ normalizedRestriction μ A {x} := le_of_not_gt hn
      rw [hz] at hbound
      exact (not_le_of_gt hc) (hlarge.trans hbound)
  rw [heq]
  exact heval (measurableSet_singleton 0)

/-- Inside the restricted set, normalization preserves comparisons of an
atom with a fixed proportion of the total mass. -/
theorem normalizedRestriction_singleton_lt_iff (μ : Measure ℂ) {A : Set ℂ}
    {x : ℂ} (hx : x ∈ A) (hz : μ A ≠ 0) (ht : μ A ≠ ∞) (c : ℝ≥0∞) :
    normalizedRestriction μ A {x} < c ↔ μ {x} < c * μ A := by
  have heq : normalizedRestriction μ A {x} = (μ A)⁻¹ * μ {x} := by
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurableSet_singleton x)]
    simp [singleton_inter_of_mem hx]
  rw [heq]
  have h := ENNReal.mul_lt_mul_iff_left (a := (μ A)⁻¹ * μ {x}) (b := c) hz ht
  rw [← h]
  simp [mul_assoc, mul_left_comm, ENNReal.inv_mul_cancel hz ht]

open MarkovProcess in
/-- The good-annulus event restricted to finite positive-mass measures with
small starting atoms is Borel, conditional on the small-ball hitting estimate. -/
theorem measurableSet_isGoodAnnulus_of_small_starting_atoms
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    MeasurableSet {μ : Measure ℂ |
      μ (annulus z (3 * r) (5 * r)) ≠ 0 ∧
      μ (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
      (∀ u ∈ sphere z (4 * r), μ {u} <
        ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))) ∧
      IsGoodAnnulus μ r z a b} := by
  let A := annulus z (3 * r) (5 * r)
  let S := sphere z (4 * r)
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hSA : S ⊆ A := by
    intro u hu
    have hd := mem_sphere.mp hu
    change dist u z < 5 * r ∧ ¬ dist u z ≤ 3 * r
    rw [hd]
    constructor <;> linarith
  have hnorm := measurableSet_no_large_normalized_atoms A S hA isClosed_sphere.measurableSet
    (ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha)
  have hmass : Measurable (fun μ : Measure ℂ => μ A) := Measure.measurable_coe hA
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_of_small_starting_atoms r hr z a b hsmall
  have heq : {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
      (∀ u ∈ S, μ {u} < ENNReal.ofReal a * μ A) ∧ IsGoodAnnulus μ r z a b} =
      {μ | μ A ≠ 0} ∩ {μ | μ A ≠ ∞} ∩
      {μ | ∀ u ∈ S, normalizedRestriction μ A {u} < ENNReal.ofReal a} ∩ G := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hz, ht, hatom, hgood⟩
      have hn : ∀ u ∈ S, normalizedRestriction μ A {u} < ENNReal.ofReal a := by
        intro u hu
        exact (normalizedRestriction_singleton_lt_iff μ (hSA hu) hz ht _).2 (hatom u hu)
      exact ⟨⟨⟨hz, ht⟩, hn⟩, (hrep μ ht hatom).2 hgood⟩
    · rintro ⟨⟨⟨hz, ht⟩, hn⟩, hg⟩
      have hatom : ∀ u ∈ S, μ {u} < ENNReal.ofReal a * μ A := by
        intro u hu
        exact (normalizedRestriction_singleton_lt_iff μ (hSA hu) hz ht _).1 (hn u hu)
      exact ⟨hz, ht, hatom, (hrep μ ht hatom).1 hg⟩
  change MeasurableSet {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
    (∀ u ∈ S, μ {u} < ENNReal.ofReal a * μ A) ∧ IsGoodAnnulus μ r z a b}
  rw [heq]
  exact (((hmass (measurableSet_singleton 0)).compl.inter
    (hmass (measurableSet_singleton ∞)).compl).inter hnorm).inter hG

end HarmonicBalls
