import HarmonicBalls.Proofs.Sec6.DominatedRootAnnulusCounts

/-! # Annulus counts at dominated sampled centres

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The polynomial count tail holds at a sampled centre when its conditional
law is dominated by a fixed finite measure. The count is simultaneous over a
countable family of relative offsets, which may vary with the sampled centre
and the radius. -/
theorem exists_dominated_sampledCentre_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (ν : Measure ℂ) [IsFiniteMeasure ν] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
      (D : ℝ≥0∞), (∀ᵐ ω ∂P, κ ω ≤ D • ν) →
    ∀ (F : ℝ → ℕ → ℂ → ℂ),
      (∀ r i, Measurable (F r i)) →
      (∀ r i z, F r i z ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ (s ε : ℝ), 0 < s → 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (μ p.1) (s * r) (p.2 + (s * r) • F (s * r) i p.2) a b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      D * (ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) * ν univ) := by
  let := h.isProbabilityMeasure
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_radius_dependent_countable_nearby_goodAnnuli_count_tail hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro ν _ κ _ D hκ F hF hFbound s ε hs hε ht
  obtain ⟨m, hm, hmfin, heq⟩ := exists_measurable_locallyFinite_rep
    (h.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ hω => hω.isLocallyFiniteMeasure)
  let q : ℕ → ℝ := fun n => (7 : ℝ)⁻¹ ^ n
  have hqi : Function.Injective q := by
    intro j k hjk
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1) hjk
  let S : Set ℕ := {n | q n ∈ Icc ε (ε ^ (3 / 4 : ℝ))}
  let T : (Ω × ℂ) → Set ℕ := fun p => {n | n ∈ S ∧
    ∀ i, IsGoodAnnulus (m p.1) (s * q n)
      (p.2 + (s * q n) • F (s * q n) i p.2) a b}
  have hT : Measurable T := by
    apply measurable_setOfPred.comp
    apply measurable_pi_iff.mpr
    intro n
    apply measurableSet_setOfPred.mp
    by_cases hn : n ∈ S
    · simp only [hn, true_and]
      have hg (i : ℕ) : MeasurableSet {p : Ω × ℂ |
          IsGoodAnnulus (m p.1) (s * q n)
            (p.2 + (s * q n) • F (s * q n) i p.2) a b} := by
        apply measurableSet_isGoodAnnulus_joint (hm.comp measurable_fst) (fun p => hmfin p.1)
        · exact measurable_snd.add ((show Measurable (fun _ : Ω × ℂ => s * q n) from
            measurable_const).smul ((hF (s * q n) i).comp measurable_snd))
        · exact measurable_const
        · intro p
          exact mul_pos hs (by dsimp [q]; positivity)
        · exact ha.1
      convert MeasurableSet.iInter hg using 1
      ext p
      simp only [mem_ofPred_eq, mem_iInter]
    · simp only [hn, false_and, ofPred_false, MeasurableSet.empty]
  let count : (Ω × ℂ) → ℝ := fun p => ((T p).ncard : ℝ)
  have hcount : Measurable count := Measurable.of_discrete.comp (measurable_ncard.comp hT)
  let E : Set (Ω × ℂ) := {p | count p < (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))}
  have hE : MeasurableSet E := measurableSet_lt hcount measurable_const
  have hcounteq (ω : Ω) (z : ℂ) :
      count (ω,z) = ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (m ω) (s * r) (z + (s * r) • F (s * r) i z) a b}.ncard : ℝ) := by
    have he : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (m ω) (s * r) (z + (s * r) • F (s * r) i z) a b} =
        q '' T (ω,z) := by
      ext r
      constructor
      · rintro ⟨hr, ⟨n, rfl⟩, hg⟩
        exact ⟨n, ⟨hr, hg⟩, rfl⟩
      · rintro ⟨n, ⟨hr, hg⟩, rfl⟩
        exact ⟨hr, ⟨n, rfl⟩, hg⟩
    dsimp only [count]
    rw [he, Set.ncard_image_of_injective _ hqi]
  have hsection : ∀ᵐ z ∂ν, P ((fun ω => (ω,z)) ⁻¹' E) ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
    filter_upwards with z
    have hbnd := htail z (fun r i => F r i z) (fun r i => hFbound r i z) s hs ε hε ht
    have hcongr : ((fun ω => (ω,z)) ⁻¹' E) =ᵐ[P]
        {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i : ℕ, IsGoodAnnulus (μ ω) (s * r) (z + (s * r) • F (s * r) i z) a b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      filter_upwards [heq] with ω hω
      simp only [mem_preimage, E, mem_ofPred_eq, hcounteq, ← hω]
    rw [measure_congr hcongr]
    exact hbnd
  have hbound := compProd_le_of_dominated_sections P ν κ D _ hκ hE hsection
  have hp := quasiMeasurePreserving_fst_compProd P κ
  have heq' := hp.ae_eq_comp heq
  have hcongr : {p : Ω × ℂ | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      ∀ i, IsGoodAnnulus (μ p.1) (s * r) (p.2 + (s * r) • F (s * r) i p.2) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} =ᵐ[P ⊗ₘ κ] E := by
    filter_upwards [heq'] with p hp
    simp only [Function.comp_apply] at hp
    simp only [E, mem_ofPred_eq, hcounteq, hp]
  rw [measure_congr hcongr]
  exact hbound

/-- The sampled-centre count bound holds for every selector of the prescribed
nearby family, including selectors depending on the field and the root. -/
theorem exists_dominated_sampledCentre_selected_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (ν : Measure ℂ) [IsFiniteMeasure ν] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
      (D : ℝ≥0∞), (∀ᵐ ω ∂P, κ ω ≤ D • ν) →
    ∀ (F : ℝ → ℕ → ℂ → ℂ),
      (∀ r i, Measurable (F r i)) →
      (∀ r i z, F r i z ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ (s ε : ℝ), 0 < s → 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | ∃ f : ℝ → ℕ,
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) (p.2 + (s * r) • F (s * r) (f r) p.2) a b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      D * (ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) * ν univ) := by
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_dominated_sampledCentre_goodAnnuli_count_tail hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro ν _ κ _ D hκ F hF hFbound s ε hs hε ht
  calc
    _ ≤ (P ⊗ₘ κ) {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (μ p.1) (s * r) (p.2 + (s * r) • F (s * r) i p.2) a b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply measure_mono
      rintro p ⟨f, hf⟩
      exact lt_of_le_of_lt
        (nearby_goodAnnulus_count_le_selected (μ p.1) p.2 (fun r i => F r i p.2) f hε) hf
    _ ≤ _ := htail ν κ D hκ F hF hFbound s ε hs hε ht

end HarmonicBalls.Section6
