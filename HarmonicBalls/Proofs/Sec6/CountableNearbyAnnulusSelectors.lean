import HarmonicBalls.Proofs.Sec6.CountableNearbyAnnulusIteration

/-! # Radius-dependent selectors of nearby annuli

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A count of radii good at every prescribed centre is bounded by the count
for any radius-dependent selector from those centres. -/
theorem nearby_goodAnnulus_count_le_selected
    (μ : Measure ℂ) (x : ℂ) (z : ℝ → ℕ → ℂ) (f : ℝ → ℕ)
    {s ε a b : ℝ} (hε : 0 < ε) :
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      ∀ i, IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b}.ncard : ℝ) ≤
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) (f r)) a b}.ncard : ℝ) := by
  have hfin : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) (f r)) a b}.Finite := by
    apply finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε
    intro r hr
    obtain ⟨n, hn⟩ := hr.2.1
    exact ⟨hr.1.1, n, by simpa only [one_mul] using hn⟩
  have hsub : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      ∀ i, IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b} ⊆
      {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) (f r)) a b} := by
    intro r hr
    exact ⟨hr.1, hr.2.1, hr.2.2 (f r)⟩
  exact_mod_cast Set.ncard_le_ncard hsub hfin

/-- A selector can choose a bad centre whenever one exists, so its good-radius
set agrees exactly with the set of radii good at every prescribed centre. -/
theorem exists_nearby_goodAnnulus_count_selector
    (μ : Measure ℂ) (x : ℂ) (z : ℝ → ℕ → ℂ) (s ε a b : ℝ) :
    ∃ f : ℝ → ℕ,
    {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      ∀ i, IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b} =
    {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) (f r)) a b} := by
  classical
  let f : ℝ → ℕ := fun r =>
    if h : ∃ i, ¬ IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b
    then Classical.choose h else 0
  refine ⟨f, ?_⟩
  ext r
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hr, hn, hg⟩
    exact ⟨hr, hn, hg (f r)⟩
  · rintro ⟨hr, hn, hg⟩
    refine ⟨hr, hn, ?_⟩
    intro i
    by_contra hbad
    have hex : ∃ i, ¬ IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b :=
      ⟨i, hbad⟩
    have hsel := Classical.choose_spec hex
    have heq : f r = Classical.choose hex := by simp only [f, dite_eq_left hex]
    exact hsel (heq ▸ hg)

/-- The simultaneous good-radius count is measurable in the measure. -/
theorem measurable_nearby_goodAnnulus_count
    (x : ℂ) (z : ℝ → ℕ → ℂ) {s : ℝ} (hs : 0 < s)
    (ε : ℝ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Measurable (fun μ : Measure ℂ =>
      ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b}.ncard : ℝ)) := by
  let q : ℕ → ℝ := fun n => (7 : ℝ)⁻¹ ^ n
  have hq : Function.Injective q := by
    intro j k hjk
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1) hjk
  let S : Measure ℂ → Set ℕ := fun μ => {n |
    q n ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
    ∀ i, IsGoodAnnulus μ (s * q n) (x + (s * q n) • z (s * q n) i) a b}
  have hS : Measurable S := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro n
    apply measurableSet_setOfPred.mp
    by_cases hn : q n ∈ Icc ε (ε ^ (3 / 4 : ℝ))
    · simp only [hn, true_and]
      convert MeasurableSet.iInter (fun i : ℕ => measurableSet_isGoodAnnulus_of_pos
        (s * q n) (mul_pos hs (by dsimp [q]; positivity))
        (x + (s * q n) • z (s * q n) i) a b ha) using 1
      ext μ
      simp only [mem_ofPred_eq, mem_iInter]
    · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
  have hcount : Measurable (fun μ : Measure ℂ => ((S μ).ncard : ℝ)) :=
    Measurable.of_discrete.comp (measurable_ncard.comp hS)
  convert hcount using 1
  funext μ
  have heq : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      ∀ i, IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b} = q '' S μ := by
    ext r
    constructor
    · rintro ⟨hr, ⟨n, rfl⟩, hg⟩
      exact ⟨n, ⟨hr, hg⟩, rfl⟩
    · rintro ⟨n, ⟨hr, hg⟩, rfl⟩
      exact ⟨hr, ⟨n, rfl⟩, hg⟩
  rw [heq, Set.ncard_image_of_injective _ hq]

/-- The event that some selector has too few good radii is measurable, even
though selectors themselves need not be measurable. -/
theorem measurableSet_exists_nearby_selected_count_lt
    (x : ℂ) (z : ℝ → ℕ → ℂ) {s ε a b c : ℝ} (hs : 0 < s) (hε : 0 < ε)
    (ha : 0 < a) :
    MeasurableSet {μ : Measure ℂ | ∃ f : ℝ → ℕ,
      ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) (f r)) a b}.ncard : ℝ) < c} := by
  have heq : {μ : Measure ℂ | ∃ f : ℝ → ℕ,
      ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) (f r)) a b}.ncard : ℝ) < c} =
      {μ : Measure ℂ | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus μ (s * r) (x + (s * r) • z (s * r) i) a b}.ncard : ℝ) < c} := by
    ext μ
    constructor
    · rintro ⟨f, hf⟩
      exact lt_of_le_of_lt (nearby_goodAnnulus_count_le_selected μ x z f hε) hf
    · intro h
      obtain ⟨f, hf⟩ := exists_nearby_goodAnnulus_count_selector μ x z s ε a b
      refine ⟨f, ?_⟩
      rwa [← hf]
  rw [heq]
  exact measurableSet_lt (measurable_nearby_goodAnnulus_count x z hs ε ha b) measurable_const

/-- The count-tail bound holds simultaneously for every radius-dependent
selector from each prescribed countable centre family. The selector may depend
on the field, with no measurability assumption. -/
theorem exists_countable_nearby_goodAnnuli_selected_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℂ) (z : ℝ → ℕ → ℂ), (∀ r i, z r i ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ s : ℝ, 0 < s → ∀ ε : ℝ, 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ∃ f : ℝ → ℕ,
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ ω) (s * r) (x + (s * r) • z (s * r) (f r)) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_radius_dependent_countable_nearby_goodAnnuli_count_tail
      hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro x z hz s hs ε hε ht
  apply (measure_mono ?_).trans (htail x z hz s hs ε hε ht)
  intro ω hbad
  obtain ⟨f, hf⟩ := hbad
  exact lt_of_le_of_lt (nearby_goodAnnulus_count_le_selected (μ ω) x z f hε) hf

end HarmonicBalls.Section6
