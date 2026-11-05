import HarmonicBalls.Proofs.Sec6.RootedNearbyAnnulusCounts
import HarmonicBalls.Proofs.Sec6.GoodAnnulusJointMeasurability

/-! # Annulus counts for dominated root sampling

The annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A sampling kernel dominated by a fixed finite measure inherits bounds for
measurable events from their deterministic-root sections. -/
theorem compProd_le_of_dominated_sections
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [SFinite P] (ν : Measure Z) [IsFiniteMeasure ν]
    (κ : Kernel Ω Z) [IsSFiniteKernel κ] (C t : ℝ≥0∞)
    (hκ : ∀ᵐ ω ∂P, κ ω ≤ C • ν)
    {E : Set (Ω × Z)} (hE : MeasurableSet E)
    (hsection : ∀ᵐ z ∂ν, P ((fun ω => (ω, z)) ⁻¹' E) ≤ t) :
    (P ⊗ₘ κ) E ≤ C * (t * ν univ) := by
  rw [Measure.compProd_apply hE]
  calc
    _ ≤ ∫⁻ ω, (C • ν) (Prod.mk ω ⁻¹' E) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hκ] with ω hω
      exact hω _
    _ = C * (P.prod ν) E := by
      rw [Measure.prod_apply hE]
      simp only [Measure.smul_apply, smul_eq_mul]
      rw [lintegral_const_mul _ (measurable_measure_prodMk_left hE)]
    _ = C * ∫⁻ z, P ((fun ω => (ω, z)) ⁻¹' E) ∂ν := by
      rw [Measure.prod_apply_symm hE]
    _ ≤ C * (t * ν univ) := by
      gcongr
      calc
        _ ≤ ∫⁻ _z, t ∂ν := lintegral_mono_ae hsection
        _ = t * ν univ := by simp

/-- A root with a bounded conditional density relative to a deterministic
finite measure retains the polynomial nearby-annulus count tail. The root
specifies a relative displacement at every scale. -/
theorem exists_dominated_root_nearby_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (ν : Measure ℂ) [IsFiniteMeasure ν] (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
      (D : ℝ≥0∞), (∀ᵐ ω ∂P, κ ω ≤ D • ν) →
      (∀ᵐ z ∂ν, z ∈ ball 0 ((1 : ℝ) / 100)) →
    ∀ (x : ℂ) (s ε : ℝ), 0 < s → 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus (μ p.1) (s * r) (x + (s * r) • p.2) a b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      D * (ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) * ν univ) := by
  let := h.isProbabilityMeasure
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_countable_nearby_goodAnnuli_count_tail_all_centres hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro ν _ κ _ D hκ hν x s ε hs hε ht
  obtain ⟨m, hm, hmfin, heq⟩ := exists_measurable_locallyFinite_rep
    (h.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ hω => hω.isLocallyFiniteMeasure)
  let q : ℕ → ℝ := fun n => (7 : ℝ)⁻¹ ^ n
  have hqi : Function.Injective q := by
    intro j k hjk
    exact pow_right_injective₀ (by norm_num : (0 : ℝ) < (7 : ℝ)⁻¹)
      (by norm_num : (7 : ℝ)⁻¹ ≠ 1) hjk
  let S : Set ℕ := {n | q n ∈ Icc ε (ε ^ (3 / 4 : ℝ))}
  let count : (Ω × ℂ) → ℝ := fun p =>
    ({n : ℕ | n ∈ S ∧ IsGoodAnnulus (m p.1) (s * q n)
      (x + (s * q n) • p.2) a b}.ncard : ℝ)
  have hcount : Measurable count := by
    apply measurable_goodAnnulus_count_joint (hm.comp measurable_fst)
      (fun p => hmfin p.1)
      (fun n p => x + (s * q n) • p.2) (fun n _ => s * q n)
      (fun n => by fun_prop) (fun n => measurable_const)
      (fun n _ => mul_pos hs (by dsimp [q]; positivity)) S ha.1 b
  let E : Set (Ω × ℂ) := {p | count p < (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))}
  have hE : MeasurableSet E := measurableSet_lt hcount measurable_const
  have hcounteq (ω : Ω) (z : ℂ) :
      count (ω,z) = ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus (m ω) (s * r) (x + (s * r) • z) a b}.ncard : ℝ) := by
    have he : {r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        IsGoodAnnulus (m ω) (s * r) (x + (s * r) • z) a b} =
        q '' {n : ℕ | n ∈ S ∧ IsGoodAnnulus (m ω) (s * q n)
          (x + (s * q n) • z) a b} := by
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
    filter_upwards [hν] with z hz
    have hbnd := htail x (fun _ => z) (fun _ => hz) s hs ε hε ht
    have hcongr : ((fun ω => (ω,z)) ⁻¹' E) =ᵐ[P]
        {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i : ℕ, IsGoodAnnulus (μ ω) (s * r) (x + (s * r) • z) a b}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      filter_upwards [heq] with ω hω
      simp only [mem_preimage, E, mem_ofPred_eq, hcounteq, ← hω, forall_const]
    rw [measure_congr hcongr]
    exact hbnd
  have hbound := compProd_le_of_dominated_sections P ν κ D _ hκ hE hsection
  have hp := quasiMeasurePreserving_fst_compProd P κ
  have heq' := hp.ae_eq_comp heq
  have hcongr : {p : Ω × ℂ | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) (x + (s * r) • p.2) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} =ᵐ[P ⊗ₘ κ] E := by
    filter_upwards [heq'] with p hp
    simp only [Function.comp_apply] at hp
    simp only [E, mem_ofPred_eq, hcounteq, hp]
  rw [measure_congr hcongr]
  exact hbound

end HarmonicBalls.Section6
