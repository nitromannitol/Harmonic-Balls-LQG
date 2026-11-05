import HarmonicBalls.Proofs.Sec6.RootedUnitDiscAnnulusTail

/-! # Polynomial annulus-count tails for roots in the unit disc

The countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- At each fixed positive scale, an arbitrarily high polynomial tail absorbs
 the cost of covering the unit disc. The threshold is independent of the scale. -/
theorem exists_rooted_unitDisc_goodAnnuli_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧
    ∀ (κ : Kernel Ω ℂ) [IsSFiniteKernel κ],
      (∀ᵐ ω ∂P, κ ω univ = 1) → (∀ᵐ ω ∂P, κ ω ≪ μ ω) →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      (P ⊗ₘ κ) {p | p.2 ∈ ball (0 : ℂ) 1 ∧
        ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ p.1) (s * r) p.2 a (b + 1)}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  have hl : 0 < Real.log 7 := Real.log_pos (by norm_num)
  obtain ⟨a, ha, C, hC, ht⟩ := exists_rooted_unitDisc_goodAnnuli_count_tail
    hgrowth hγ hγ2 h hμ hb (16 * Real.log 7 * (q + 2)) β (by positivity) hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  have hm : 0 < min s 1 := lt_min hs (by norm_num)
  refine ⟨(2800 / min s 1) ^ 2 * C, by positivity, ?_⟩
  intro κ _ hk hac ε hε hε1 hlog
  have he : 16 * Real.log 7 * (q + 2) / (16 * Real.log 7) = q + 2 := by
    field_simp
  have hpow : ε ^ (q + 2) = ε ^ q * ε ^ (2 : ℕ) := by
    rw [Real.rpow_add hε, Real.rpow_two]
  have hid : (2800 / (min s 1 * ε)) ^ 2 * (C * ε ^ (q + 2)) =
      ((2800 / min s 1) ^ 2 * C) * ε ^ q := by
    rw [hpow]
    field_simp
  calc
    _ ≤ ENNReal.ofReal ((2800 / (min s 1 * ε)) ^ 2) *
        ENNReal.ofReal (C * ε ^ (q + 2)) := by simpa only [he] using ht κ hk hac s ε hs hε hε1 hlog
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _), hid]

end HarmonicBalls.Section6
