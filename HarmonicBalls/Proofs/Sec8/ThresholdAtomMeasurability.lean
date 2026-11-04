import HarmonicBalls.Proofs.Sec8.ThresholdAtomObstacles
import HarmonicBalls.Proofs.Sec8.LargeAtomMeasurabilityReduction

/-! # Measurability away from threshold-sized atoms -/

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The absence of an atom of a fixed positive mass in a Borel set is measurable. -/
theorem measurableSet_no_threshold_normalized_atoms
    (A S : Set ℂ) (hA : MeasurableSet A) (hS : MeasurableSet S)
    (c : ℝ≥0∞) (hc : 0 < c) :
    MeasurableSet {μ : Measure ℂ | ∀ x ∈ S, normalizedRestriction μ A {x} ≠ c} := by
  let κ := normalizedRestrictionKernel A hA
  let E : Set (Measure ℂ × ℂ) := {p | p.2 ∈ S ∧ normalizedRestriction p.1 A {p.2} = c}
  have hE : MeasurableSet E := (hS.preimage measurable_snd).inter
    (measurableSet_eq_fun (measurable_normalizedRestriction_singleton A hA) measurable_const)
  have heval : Measurable fun μ => κ μ (Prod.mk μ ⁻¹' E) :=
    Kernel.measurable_kernel_prodMk_left hE
  have heq : {μ : Measure ℂ | ∀ x ∈ S, normalizedRestriction μ A {x} ≠ c} =
      {μ : Measure ℂ | κ μ (Prod.mk μ ⁻¹' E) = 0} := by
    ext μ
    constructor
    · intro h
      have hempty : Prod.mk μ ⁻¹' E = ∅ := by
        ext x
        simp only [mem_preimage, E, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hx, heq⟩
        exact h x hx heq
      simp [hempty]
    · intro hz x hx heq
      have hxE : x ∈ Prod.mk μ ⁻¹' E := ⟨hx, heq⟩
      have hbound : normalizedRestriction μ A {x} ≤ κ μ (Prod.mk μ ⁻¹' E) :=
        measure_mono (singleton_subset_iff.mpr hxE)
      rw [hz, heq] at hbound
      exact (not_le_of_gt hc) hbound
  rw [heq]
  exact heval (measurableSet_singleton 0)

/-- At positive finite total mass, normalization preserves equality to a fixed proportion. -/
theorem normalizedRestriction_singleton_eq_iff (μ : Measure ℂ) {A : Set ℂ}
    {x : ℂ} (hx : x ∈ A) (hz : μ A ≠ 0) (ht : μ A ≠ ∞) (c : ℝ≥0∞) :
    normalizedRestriction μ A {x} = c ↔ μ {x} = c * μ A := by
  have heq : normalizedRestriction μ A {x} = (μ A)⁻¹ * μ {x} := by
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurableSet_singleton x)]
    simp [singleton_inter_of_mem hx]
  rw [heq]
  constructor
  · intro h
    have h' := congrArg (fun v : ℝ≥0∞ => v * μ A) h
    simpa [mul_assoc, mul_left_comm, ENNReal.inv_mul_cancel hz ht] using h'
  · intro h
    rw [h]
    simp [mul_left_comm, ENNReal.inv_mul_cancel hz ht]


open MarkovProcess in
/-- The good-annulus event restricted to finite positive-mass measures with
no threshold-sized starting atoms is Borel, conditional on the small-ball hitting estimate. -/
theorem measurableSet_isGoodAnnulus_of_no_threshold_starting_atoms
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    MeasurableSet {μ : Measure ℂ |
      μ (annulus z (3 * r) (5 * r)) ≠ 0 ∧
      μ (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
      (∀ u ∈ sphere z (4 * r), μ {u} ≠
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
  have hnorm := measurableSet_no_threshold_normalized_atoms A S hA isClosed_sphere.measurableSet
    (ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha)
  have hmass : Measurable (fun μ : Measure ℂ => μ A) := Measure.measurable_coe hA
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_of_no_threshold_starting_atoms r hr z a b hsmall
  have heq : {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
      (∀ u ∈ S, μ {u} ≠ ENNReal.ofReal a * μ A) ∧ IsGoodAnnulus μ r z a b} =
      {μ | μ A ≠ 0} ∩ {μ | μ A ≠ ∞} ∩
      {μ | ∀ u ∈ S, normalizedRestriction μ A {u} ≠ ENNReal.ofReal a} ∩ G := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hz, ht, hatom, hgood⟩
      have hn : ∀ u ∈ S, normalizedRestriction μ A {u} ≠ ENNReal.ofReal a := by
        intro u hu
        exact fun h => hatom u hu ((normalizedRestriction_singleton_eq_iff μ (hSA hu) hz ht _).1 h)
      exact ⟨⟨⟨hz, ht⟩, hn⟩, (hrep μ ht hatom).2 hgood⟩
    · rintro ⟨⟨⟨hz, ht⟩, hn⟩, hg⟩
      have hatom : ∀ u ∈ S, μ {u} ≠ ENNReal.ofReal a * μ A := by
        intro u hu
        exact fun h => hn u hu ((normalizedRestriction_singleton_eq_iff μ (hSA hu) hz ht _).2 h)
      exact ⟨hz, ht, hatom, (hrep μ ht hatom).1 hg⟩
  change MeasurableSet {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
    (∀ u ∈ S, μ {u} ≠ ENNReal.ofReal a * μ A) ∧ IsGoodAnnulus μ r z a b}
  rw [heq]
  exact (((hmass (measurableSet_singleton 0)).compl.inter
    (hmass (measurableSet_singleton ∞)).compl).inter hnorm).inter hG


/-- On positive finite-mass measures, the absence of atoms that carry exactly a fixed
fraction of the mass is a measurable condition. -/
theorem measurableSet_no_threshold_atoms_relative_to_mass
    (A S : Set ℂ) (hA : MeasurableSet A) (hS : MeasurableSet S) (hSA : S ⊆ A)
    (c : ℝ≥0∞) (hc : 0 < c) :
    MeasurableSet {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
      ∀ x ∈ S, μ {x} ≠ c * μ A} := by
  have hnorm := measurableSet_no_threshold_normalized_atoms A S hA hS c hc
  have hmass : Measurable (fun μ : Measure ℂ => μ A) := Measure.measurable_coe hA
  have heq : {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
      ∀ x ∈ S, μ {x} ≠ c * μ A} =
      {μ | μ A ≠ 0} ∩ {μ | μ A ≠ ∞} ∩
        {μ | ∀ x ∈ S, normalizedRestriction μ A {x} ≠ c} := by
    ext μ
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hz, ht, hatom⟩
      exact ⟨⟨hz, ht⟩, fun x hx =>
        fun h => hatom x hx ((normalizedRestriction_singleton_eq_iff μ (hSA hx) hz ht c).1 h)⟩
    · rintro ⟨⟨hz, ht⟩, hnorm⟩
      exact ⟨hz, ht, fun x hx =>
        fun h => hnorm x hx ((normalizedRestriction_singleton_eq_iff μ (hSA hx) hz ht c).2 h)⟩
  rw [heq]
  exact ((hmass (measurableSet_singleton 0)).compl.inter
    (hmass (measurableSet_singleton ∞)).compl).inter hnorm

open MarkovProcess in
/-- In the nontrivial parameter range, unrestricted good-annulus measurability
is equivalent to measurability on measures with a threshold-sized starting atom. -/
theorem measurableSet_isGoodAnnulus_iff_threshold_starting_atom
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ) (ha : 0 < a) (hb : b < 1)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b} ↔
      MeasurableSet {μ : Measure ℂ | IsGoodAnnulus μ r z a b ∧
        ∃ u ∈ sphere z (4 * r),
          μ {u} = ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r))} := by
  classical
  let A := annulus z (3 * r) (5 * r)
  let S := sphere z (4 * r)
  let C : Set (Measure ℂ) := {μ | μ A ≠ 0 ∧ μ A ≠ ∞}
  let H : Set (Measure ℂ) := {μ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
    ∀ x ∈ S, μ {x} ≠ ENNReal.ofReal a * μ A}
  let Good : Set (Measure ℂ) := {μ | IsGoodAnnulus μ r z a b}
  let Large : Set (Measure ℂ) := {μ | IsGoodAnnulus μ r z a b ∧
    ∃ u ∈ S, μ {u} = ENNReal.ofReal a * μ A}
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
  have hH : MeasurableSet H := measurableSet_no_threshold_atoms_relative_to_mass A S hA
    isClosed_sphere.measurableSet hSA (ENNReal.ofReal a) (ENNReal.ofReal_pos.mpr ha)
  have hsmallGood : MeasurableSet (H ∩ Good) := by
    have heq : H ∩ Good = {μ : Measure ℂ | μ A ≠ 0 ∧ μ A ≠ ∞ ∧
        (∀ u ∈ S, μ {u} ≠ ENNReal.ofReal a * μ A) ∧ IsGoodAnnulus μ r z a b} := by
      ext μ
      simp only [H, Good, mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [heq]
    exact measurableSet_isGoodAnnulus_of_no_threshold_starting_atoms r hr z a b ha hsmall
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
      exact hless u hu hatom
    · rintro ⟨hg, hc, hn⟩
      refine ⟨hg, ?_⟩
      have hn' : ¬ ∀ u ∈ S, μ {u} ≠ ENNReal.ofReal a * μ A := by
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
