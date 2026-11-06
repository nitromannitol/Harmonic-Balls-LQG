import HarmonicBalls.Proofs.Sec6.SingularRootRelativeCollar
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Deterministic collar widths at singular LQG roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- For an arbitrary prescribed sequence of positive radii and relative mass
thresholds, deterministic collar widths can be selected so that the collar
estimate holds eventually at almost every singular-LQG-sampled root. The
relative widths are at most dyadic, but may need to be much smaller. -/
theorem exists_singularRoot_zero_eventually_relative_collar
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (d : ℕ → ℝ≥0∞) (hd : ∀ n, 0 < d n) :
    ∃ m : ℕ → ℕ, (∀ n, 1/((m n : ℝ)+1) < r n * (1/2 : ℝ)^n) ∧
      ∀ᵐ p ∂(P ⊗ₘ κ), ∀ᶠ n in atTop,
      μ₀ p.1 (annulus p.2 (3*r n-1/((m n : ℝ)+1)) (5*r n+1/((m n : ℝ)+1)) \
        annulus p.2 (3*r n+1/((m n : ℝ)+1)) (5*r n-1/((m n : ℝ)+1))) ≤
        d n * μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) := by
  classical
  let E : ℕ → ℕ → Set (Ω × ℂ) := fun n j => {p |
    d n * μ₀ p.1 (annulus p.2 (3*r n) (5*r n)) <
    μ₀ p.1 (annulus p.2 (3*r n-1/((j : ℝ)+1)) (5*r n+1/((j : ℝ)+1)) \
      annulus p.2 (3*r n+1/((j : ℝ)+1)) (5*r n-1/((j : ℝ)+1)))}
  have hex (n : ℕ) : ∃ j, (P ⊗ₘ κ) (E n j) ≤ (2⁻¹ : ℝ≥0∞) ^ n ∧
      1/((j : ℝ)+1) < r n * (1/2 : ℝ)^n := by
    have ht := tendsto_singularRoot_zero_relative_collar_failure hgrowth hγ hγ2 hα h hμ hμ₀ κ hac
      (hr n) (hd n)
    have hp : 0 < (2⁻¹ : ℝ≥0∞) ^ n := pos_iff_ne_zero.mpr (pow_ne_zero _ (by simp))
    have hwidth : 0 < r n * (1/2 : ℝ)^n := mul_pos (hr n) (pow_pos (by norm_num) _)
    have hw := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hwidth)
    obtain ⟨j, hj, hjw⟩ := ((ht.eventually_lt_const hp).and hw).exists
    exact ⟨j, hj.le, hjw⟩
  choose m hm hwidth using hex
  refine ⟨m, hwidth, ?_⟩
  have hs : (∑' n, (P ⊗ₘ κ) (E n (m n))) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hm)
    rw [ENNReal.tsum_geometric_two]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_eventually_notMem hs] with p hp
  filter_upwards [hp] with n hn
  exact le_of_not_gt hn

end HarmonicBalls.Section6
