import HarmonicBalls.Proofs.Sec9.AlmostDisjointFrontierUniqueness
import HarmonicBalls.Proofs.Sec9.SharpHausdorffComparison

/-!
# Families with small-dimensional frontier intersections

The I2 volume-growth estimate makes sets below its upper-growth threshold
null. Applied to pairwise frontier intersections, this extends the countable
exception result to families whose boundaries can meet in uncountable sets.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u v

/-- The Hausdorff-dimension lower bound for bounded positive-mass sets
extends to arbitrary positive-mass sets by exhaustion with balls. -/
theorem measure_zero_of_dimH_lt_of_local_lower_bound
    (μ : Measure ℂ) (d : ℝ≥0∞)
    (hlower : ∀ (R : ℝ) (s : Set ℂ), 0 < R → s ⊆ ball 0 R → μ s ≠ 0 → d ≤ dimH s)
    (s : Set ℂ) (hsmall : dimH s < d) : μ s = 0 := by
  have hn : ∀ n : ℕ, μ (s ∩ ball 0 (n + 1 : ℝ)) = 0 := by
    intro n
    by_contra hne
    have hle := hlower (n + 1 : ℝ) _ (by positivity) inter_subset_right hne
    exact (not_lt_of_ge (hle.trans (dimH_mono inter_subset_left))) hsmall
  have hcover : s ⊆ ⋃ n : ℕ, s ∩ ball 0 (n + 1 : ℝ) := by
    intro x hx
    have hx' : x ∈ ⋃ n : ℕ, ball (0 : ℂ) (n + 1 : ℝ) := by
      rw [Metric.iUnion_ball_nat_succ]
      exact mem_univ x
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx'
    exact mem_iUnion.mpr ⟨n, hx, hn⟩
  exact measure_mono_null hcover (measure_iUnion_null hn)

/-- I2 gives weak uniqueness outside countably many indices of any family
whose pairwise frontier intersections have Hausdorff dimension strictly below
the I2 upper-growth threshold. The event works for all such families. -/
theorem ae_subharmonicBall_uniqueness_off_countable_fractal_family
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (ι : Type v) (A : ι → Set ℂ),
      (∀ i j, i ≠ j → dimH (frontier (A i) ∩ frontier (A j)) <
        ENNReal.ofReal (min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)))) →
      ∃ E : Set ι, E.Countable ∧ ∀ i ∉ E, ∀ (z : ℂ) (t R : ℝ),
        0 < t → 0 < R → z ∈ ball (0 : ℂ) R → closure (A i) ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) (A i) z → μ ω (A i) = ENNReal.ofReal t →
        cluster (μ ω) R z t ⊆ A i ∧ A i ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen (A i) → regularizedCluster (μ ω) R z t = A i) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqgMeasure_positive_mass_dimH_lower_bound hI2 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_uniqueness_off_countable_frontier_family hI2 γ α₀ hγ hγ2 hα
      Ω P hC hcirc μ hGFF hμ] with ω hlower hunique
  intro ι A hpair
  apply hunique ι A
  intro i j hij
  exact measure_zero_of_dimH_lt_of_local_lower_bound (μ ω) _ hlower _ (hpair i j hij)

end HarmonicBalls
