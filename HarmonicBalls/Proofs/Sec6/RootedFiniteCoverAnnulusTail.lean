import HarmonicBalls.Proofs.Sec6.RootedLocalAnnulusCountTail

/-! # Rooted annulus count tails over finite covers

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A finite collection of smallest-scale balls inherits the rooted count
 tail with a factor equal to the number of balls. -/
theorem exists_rooted_finiteCover_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ (T : Finset ℂ) (s ε : ℝ), 0 < s → 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | (∃ x ∈ T, p.2 ∈ ball x (s * ε / 100)) ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      (T.card : ℝ≥0∞) * ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨a, ha, C, hC, hlocal⟩ :=
    exists_rooted_local_goodAnnuli_count_tail hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro κ _ hκ hac T s ε hs hε ht
  let E : ℂ → Set (Ω × ℂ) := fun x => {p | p.2 ∈ ball x (s * ε / 100) ∧
    ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
      (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
      IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
      (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))}
  calc
    _ ≤ (P ⊗ₘ κ) (⋃ x ∈ T, E x) := by
      apply measure_mono
      intro p hp
      obtain ⟨⟨x, hx, hpx⟩, hbad⟩ := hp
      exact mem_iUnion₂.mpr ⟨x, hx, hpx, hbad⟩
    _ ≤ ∑ x ∈ T, (P ⊗ₘ κ) (E x) := measure_biUnion_finset_le T E
    _ ≤ ∑ _x ∈ T, ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hlocal κ hκ hac x s ε hs hε ht
    _ = _ := by simp

end HarmonicBalls.Section6
