import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import HarmonicBalls.Proofs.Sec8.GoodEventParameterExtremes

/-! # Measurability reduction to large starting atoms -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- On positive finite-mass measures, the absence of atoms that carry a fixed
fraction of the mass is a measurable condition. -/
theorem measurableSet_small_atoms_relative_to_mass
    (A S : Set ℂ) (hA : MeasurableSet A) (hS : MeasurableSet S) (hSA : S ⊆ A)
    (c : ℝ≥0∞) (hc : 0 < c) :
    MeasurableSet {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
      ∀ x ∈ S, μ {x} < c * μ A} := by
  have hnorm := measurableSet_no_large_normalized_atoms A S hA hS c hc
  have hmass : Measurable (fun μ : Measure ℂ => μ A) := Measure.measurable_coe hA
  have heq : {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
      ∀ x ∈ S, μ {x} < c * μ A} =
      {μ | μ A ≠ 0} ∩ {μ | μ A ≠ ∞} ∩
        {μ | ∀ x ∈ S, normalizedRestriction μ A {x} < c} := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hz, ht, hatom⟩
      exact ⟨⟨hz, ht⟩, fun x hx =>
        (normalizedRestriction_singleton_lt_iff μ (hSA hx) hz ht c).2 (hatom x hx)⟩
    · rintro ⟨⟨hz, ht⟩, hnorm⟩
      exact ⟨hz, ht, fun x hx =>
        (normalizedRestriction_singleton_lt_iff μ (hSA hx) hz ht c).1 (hnorm x hx)⟩
  rw [heq]
  exact ((hmass (measurableSet_singleton 0)).compl.inter
    (hmass (measurableSet_singleton ∞)).compl).inter hnorm

open MarkovProcess in
/-- In the nontrivial parameter range, unrestricted good-annulus measurability
is equivalent to measurability on measures with a large starting atom. -/
theorem measurableSet_isGoodAnnulus_iff_large_starting_atom
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} ↔
      MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b ∧
        ∃ u ∈ sphere z (4 * r),
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) ≤ μ {u}} := by
  classical
  let A := annulus z (3 * r) (5 * r)
  let S := sphere z (4 * r)
  let C : Set (Measure ℂ) := {μ | μ A ≠ 0 ∧ μ A ≠ ∞}
  let H : Set (Measure ℂ) := {μ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
    ∀ x ∈ S, μ {x} < ENNReal.ofReal a * μ A}
  let Good : Set (Measure ℂ) := {μ | IsGoodAnnulus μ r z a b}
  let Large : Set (Measure ℂ) := {μ | IsGoodAnnulus μ r z a b ∧
    ∃ u ∈ S, ENNReal.ofReal a * μ A ≤ μ {u}}
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hSA : S ⊆ A := by
    intro u hu
    have hd := mem_sphere.mp hu
    change dist u z < 5 * r ∧ ¬ dist u z ≤ 3 * r
    rw [hd]
    constructor <;> linarith
  have hC : MeasurableSet C := by
    have hm := Measure.measurable_coe hA
    exact (hm (measurableSet_singleton 0)).compl.inter
      (hm (measurableSet_singleton ∞)).compl
  have hH : MeasurableSet H := measurableSet_small_atoms_relative_to_mass A S hA
    isClosed_sphere.measurableSet hSA (ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha)
  have hsmallGood : MeasurableSet (H ∩ Good) := by
    have heq : H ∩ Good = {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
        (∀ u ∈ S, μ {u} < ENNReal.ofReal a * μ A) ∧ IsGoodAnnulus μ r z a b} := by
      ext μ
      simp only [H, Good, mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [heq]
    exact measurableSet_isGoodAnnulus_of_small_starting_atoms r hr z a b ha hsmall
  have hgoodC : Good ⊆ C := by
    intro μ hμ
    exact isGoodAnnulus_annulus_mass_ne_zero_ne_top μ hr.le z ha hb hμ
  have hLarge : Large = Good ∩ (C \ H) := by
    ext μ
    simp only [Large, Good, C, H, mem_ofPred_eq, mem_inter_iff, mem_sdiff]
    constructor
    · rintro ⟨hg, u, hu, hatom⟩
      have hc := hgoodC hg
      refine ⟨hg, hc, ?_⟩
      rintro ⟨_, _, hless⟩
      exact (not_le_of_gt (hless u hu)) hatom
    · rintro ⟨hg, hc, hn⟩
      refine ⟨hg, ?_⟩
      have hn' : ¬ ∀ u ∈ S, μ {u} < ENNReal.ofReal a * μ A := by
        intro hall
        exact hn ⟨hc.1, hc.2, hall⟩
      push Not at hn'
      exact hn'
  change MeasurableSet Good ↔ MeasurableSet Large
  constructor
  · intro hg
    rw [hLarge]
    exact hg.inter (hC.diff hH)
  · intro hl
    have heq : Good = (H ∩ Good) ∪ Large := by
      rw [hLarge]
      ext μ
      simp only [mem_union, mem_inter_iff, mem_sdiff]
      constructor
      · intro hg
        by_cases hh : μ ∈ H
        · exact Or.inl ⟨hh, hg⟩
        · exact Or.inr ⟨hg, hgoodC hg, hh⟩
      · rintro (⟨_, hg⟩ | ⟨hg, _, _⟩) <;> exact hg
    rw [heq]
    exact hsmallGood.union hl

end HarmonicBalls
