import HarmonicBalls.Proofs.Sec6.RootedFiniteCoverAnnulusTail
import HarmonicBalls.Proofs.Sec6.BoundedLatticeCover

/-! # Rooted annulus count tail on the unit disc

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A quantitative unit-disc union bound for roots sampled from a normalized
kernel absolutely continuous with respect to LQG mass. -/
theorem exists_rooted_unitDisc_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ (s ε : ℝ), 0 < s → 0 < ε → ε ≤ 1 →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal ((2800 / (min s 1 * ε)) ^ 2) *
        ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  classical
  obtain ⟨a, ha, C, hC, htail⟩ :=
    exists_rooted_finiteCover_goodAnnuli_count_tail hgrowth hγ hγ2 h hμ hb α β hα hβ
  refine ⟨a, ha, C, hC, ?_⟩
  intro κ _ hκ hac s ε hs hε hε1 ht
  let δ : ℝ := min s 1 * ε / 400
  have hmin : 0 < min s 1 := lt_min hs (by norm_num)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    have hm : min s 1 ≤ 1 := min_le_right _ _
    have hprod : min s 1 * ε ≤ 1 := by nlinarith
    dsimp [δ]; linarith
  obtain ⟨T, hcard, hcover⟩ := exists_unitDisc_lattice_cover hδ hδ1
  have hbound : 2 * δ < s * ε / 100 := by
    have hm : min s 1 ≤ s := min_le_left _ _
    have hmul : min s 1 * ε ≤ s * ε := mul_le_mul_of_nonneg_right hm hε.le
    have hpos : 0 < s * ε := mul_pos hs hε
    dsimp [δ]; linarith
  have hc : (T.card : ℝ≥0∞) ≤ ENNReal.ofReal ((2800 / (min s 1 * ε)) ^ 2) := by
    have heq : 7 / δ = 2800 / (min s 1 * ε) := by dsimp [δ]; ring
    rw [heq] at hcard
    exact_mod_cast (ENNReal.ofReal_le_ofReal hcard)
  calc
    _ ≤ (P ⊗ₘ κ) {p | (∃ x ∈ T, p.2 ∈ ball x (s * ε / 100)) ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} := by
      apply measure_mono
      intro p hp
      obtain ⟨x, hx, hpx⟩ := hcover p.2 hp.1
      exact ⟨⟨x, hx, ball_subset_ball hbound.le hpx⟩, hp.2⟩
    _ ≤ (T.card : ℝ≥0∞) * ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) :=
      htail κ hκ hac T s ε hs hε ht
    _ ≤ _ := by gcongr

end HarmonicBalls.Section6
