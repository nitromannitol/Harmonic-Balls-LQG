import HarmonicBalls.Proofs.Sec6.CollarFailureFrequency
import HarmonicBalls.Proofs.Sec6.RootedRelativeCollar

/-! # Uniform collar frequencies from a dominating rescaled rooted law

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

open Classical in
/-- A common finite dominating law for rescaled rooted configurations gives a
single relative collar width and a first-moment frequency bound for every
finite family of scales. The domination and event transport hypotheses are
explicit; they do not assert a recentered LQG sampled-root law. -/
theorem exists_uniform_rooted_relativeCollar_failure_count_le
    {Ω : Type*} [MeasurableSpace Ω] (Q Q₀ : Measure (Ω × ℂ)) [IsFiniteMeasure Q₀]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (r : ℕ → ℝ) (T : ℕ → Ω × ℂ → Ω × ℂ)
    (hT : ∀ i, Measurable (T i))
    (hdom : ∀ i, Q.map (T i) ≤ Q₀)
    (htransport : ∀ (i : ℕ) (η : ℝ) (d : ℝ≥0∞),
      {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} =
      (T i) ⁻¹' {p | d * μ p.1 (annulus p.2 3 5) <
        μ p.1 (annulus p.2 (3-η) (5+η) \ annulus p.2 (3+η) (5-η))})
    (hreg : ∀ᵐ p ∂Q₀, μ p.1 (sphere p.2 3) = 0 ∧
      μ p.1 (sphere p.2 5) = 0 ∧ 0 < μ p.1 (annulus p.2 3 5))
    {c : ℝ} (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ ∀ (s : Finset ℕ) (k : ℕ),
      (k : ℝ≥0∞) * Q {p | k ≤ (s.filter fun i =>
        d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card} ≤
      (s.card : ℝ≥0∞) * q := by
  have ht := tendsto_rooted_relative_collar_failure Q₀ μ hμ hloc 3 5 hd hreg
  have hw := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hc)
  obtain ⟨n, hn, hnc⟩ := ((ht.eventually_lt_const hq).and hw).exists
  let η : ℝ := 1 / ((n : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hsingle (i : ℕ) : Q {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} ≤ q := by
    rw [htransport i η d, ← Measure.map_apply (hT i)
      (by simpa only [mul_one] using measurableSet_root_relativeCollarFailure μ hμ hloc 1 η d)]
    exact (hdom i _).trans hn.le
  refine ⟨η, hη, hnc, ?_⟩
  intro s k
  calc
    _ ≤ ∑ i ∈ s, Q {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} :=
      mul_measure_root_relativeCollarFailure_count_le Q μ hμ hloc r η d s k
    _ ≤ ∑ _i ∈ s, q := Finset.sum_le_sum (fun i _ => hsingle i)
    _ = _ := by simp

end HarmonicBalls.Section6
