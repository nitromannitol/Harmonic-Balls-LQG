import HarmonicBalls.Proofs.Sec6.RootedCollarSmallProbability

/-! # A common collar width on a finite set of scales

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Narrowing a two-sided annular collar can only decrease its mass. -/
theorem annulus_relative_collar_mono (ν : Measure ℂ) (z : ℂ) {r η η' : ℝ}
    (hr : 0 ≤ r) (hη : η ≤ η') :
    ν (annulus z (3*r-η*r) (5*r+η*r) \ annulus z (3*r+η*r) (5*r-η*r)) ≤
    ν (annulus z (3*r-η'*r) (5*r+η'*r) \ annulus z (3*r+η'*r) (5*r-η'*r)) := by
  apply measure_mono
  have hmul : η*r ≤ η'*r := mul_le_mul_of_nonneg_right hη hr
  intro x hx
  simp only [annulus, Set.mem_sdiff, mem_ball, mem_closedBall, not_le] at hx ⊢
  constructor
  · constructor <;> linarith [hx.1.1, hx.1.2]
  · intro hinner
    apply hx.2
    constructor <;> linarith [hinner.1, hinner.2]

/-- A narrower relative collar has no larger failure probability. -/
theorem measure_relative_collar_failure_mono
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure (Ω × ℂ))
    (μ : Ω → Measure ℂ) {r η η' : ℝ} (hr : 0 ≤ r) (hη : η ≤ η') (d : ℝ≥0∞) :
    Q {p | d * μ p.1 (annulus p.2 (3*r) (5*r)) <
      μ p.1 (annulus p.2 (3*r-η*r) (5*r+η*r) \ annulus p.2 (3*r+η*r) (5*r-η*r))} ≤
    Q {p | d * μ p.1 (annulus p.2 (3*r) (5*r)) <
      μ p.1 (annulus p.2 (3*r-η'*r) (5*r+η'*r) \ annulus p.2 (3*r+η'*r) (5*r-η'*r))} := by
  apply measure_mono
  intro p hp
  exact lt_of_lt_of_le hp (annulus_relative_collar_mono _ _ hr hη)

open Classical in
/-- One positive relative width makes collar failures unlikely at each scale
of a prescribed finite family of positive radii. The width may depend on that
family and on the rooted law. -/
theorem exists_singularRoot_finite_relative_collar_failure_lt
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (κ : Kernel Ω ℂ) [IsFiniteMeasure (P ⊗ₘ κ)] (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (s : Finset ℕ)
    {c : ℝ} (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ ∀ i ∈ s,
      (P ⊗ₘ κ) {p | d * μ₀ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ₀ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} < q := by
  induction s using Finset.induction_on with
  | empty => exact ⟨c / 2, by linarith, by linarith, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨η, hη, hηc, hs⟩ := ih
    obtain ⟨η', hη', hη'η, hi⟩ :=
      exists_singularRoot_zero_relative_collar_failure_lt hgrowth hγ hγ2 hα h hμ hμ₀ κ hac
        (hr i) hη hd hq
    refine ⟨η', hη', hη'η.trans hηc, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hi
    · exact (measure_relative_collar_failure_mono (P ⊗ₘ κ) μ₀ (hr j).le hη'η.le d).trans_lt (hs j hj)

end HarmonicBalls.Section6
