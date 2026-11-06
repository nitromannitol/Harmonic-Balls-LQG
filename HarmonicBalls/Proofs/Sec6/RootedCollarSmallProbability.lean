import HarmonicBalls.Proofs.Sec6.SingularRootRelativeCollar

/-! # Small relative-collar failure probability at a rooted scale

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped ENNReal Topology
universe u

/-- At any fixed positive radius, the relative-collar failure probability
under a singular-mass dominated root law can be made arbitrarily small. The
selected relative width may depend on the radius and the rooted law. -/
theorem exists_singularRoot_zero_relative_collar_failure_lt
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧
      (P ⊗ₘ κ) {p | d * μ₀ p.1 (annulus p.2 (3*r) (5*r)) <
        μ₀ p.1 (annulus p.2 (3*r-η*r) (5*r+η*r) \
          annulus p.2 (3*r+η*r) (5*r-η*r))} < q := by
  have ht := tendsto_singularRoot_zero_relative_collar_failure
    hgrowth hγ hγ2 hα h hμ hμ₀ κ hac hr hd
  have hw := tendsto_one_div_add_atTop_nhds_zero_nat.eventually
    (Iio_mem_nhds (mul_pos hc hr))
  obtain ⟨n, hn, hwidth⟩ := ((ht.eventually_lt_const hq).and hw).exists
  refine ⟨(1 / ((n : ℝ) + 1)) / r, div_pos (one_div_pos.mpr (by positivity)) hr,
    (div_lt_iff₀ hr).2 hwidth, ?_⟩
  have heq : (1 / ((n : ℝ) + 1)) / r * r = 1 / ((n : ℝ) + 1) :=
    div_mul_cancel₀ _ hr.ne'
  simpa only [heq] using hn

end HarmonicBalls.Section6
