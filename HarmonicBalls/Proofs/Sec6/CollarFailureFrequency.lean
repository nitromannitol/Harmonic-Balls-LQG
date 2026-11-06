import HarmonicBalls.Proofs.Sec6.CollarGoodAnnulusCounts
import HarmonicBalls.Proofs.Sec6.RootedRelativeCollar
import HarmonicBalls.Proofs.Sec6.RelativeCollarScaling

/-! # Finite frequencies of collar failures

A first-moment estimate for the number of failures. It requires no independence
and applies to any measurable family of events under any measure.
The imported Section 6 iteration uses Leonardo Bonanno’s proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

open Classical in
/-- The measure of outcomes with at least `k` failures is controlled by the
sum of the individual failure measures. -/
theorem mul_measure_failure_count_le_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (s : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) (k : ℕ) :
    (k : ℝ≥0∞) * Q {ω | k ≤ (s.filter fun i => ω ∈ E i).card} ≤
      ∑ i ∈ s, Q (E i) := by
  classical
  let f : Ω → ℝ≥0∞ := fun ω => ∑ i ∈ s, (E i).indicator 1 ω
  have hf : Measurable f := by
    exact Finset.measurable_fun_sum _ fun i hi => measurable_one.indicator (hE i hi)
  have hcard (ω : Ω) : f ω = ((s.filter fun i => ω ∈ E i).card : ℝ≥0∞) := by
    simp only [f, indicator_apply, Pi.one_apply, Finset.sum_boole]
  have hmark := mul_meas_ge_le_lintegral (μ := Q) hf (k : ℝ≥0∞)
  have hevent : {ω | (k : ℝ≥0∞) ≤ f ω} =
      {ω | k ≤ (s.filter fun i => ω ∈ E i).card} := by
    ext ω
    simp only [mem_ofPred_eq, hcard, Nat.cast_le]
  rw [hevent] at hmark
  calc
    _ ≤ ∫⁻ ω, f ω ∂Q := hmark
    _ = ∑ i ∈ s, Q (E i) := by
      dsimp only [f]
      rw [lintegral_finsetSum _ fun i hi => measurable_one.indicator (hE i hi)]
      apply Finset.sum_congr rfl
      intro i hi
      exact lintegral_indicator_one (hE i hi)

/-- Relative-collar failure is jointly measurable in the field and root
when the random measure is measurable and locally finite. -/
theorem measurableSet_root_relativeCollarFailure
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    (hμ : Measurable μ) (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (r η : ℝ) (d : ℝ≥0∞) :
    MeasurableSet {p : Ω × ℂ | d * μ p.1 (annulus p.2 (3*r) (5*r)) <
      μ p.1 (annulus p.2 (3*r-η*r) (5*r+η*r) \
        annulus p.2 (3*r+η*r) (5*r-η*r))} := by
  let ν : Ω × ℂ → Measure ℂ := fun p => (μ p.1).map (fun x => x - p.2)
  have hν : Measurable ν := measurable_map_of_locallyFinite (hμ.comp measurable_fst)
    (fun p => hloc p.1) (f := fun p : (Ω × ℂ) × ℂ => p.2 - p.1.2) (by fun_prop)
  have htransport (p : Ω × ℂ) (s t : ℝ) :
      ν p (annulus 0 s t) = μ p.1 (annulus p.2 s t) := by
    have hm : MeasurableSet (annulus (0 : ℂ) s t) :=
      isOpen_ball.measurableSet.diff measurableSet_closedBall
    rw [show ν p = (μ p.1).map (fun x => x-p.2) from rfl, Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [annulus, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm]
  have htransport' (p : Ω × ℂ) (s t s' t' : ℝ) :
      ν p (annulus 0 s t \ annulus 0 s' t') =
        μ p.1 (annulus p.2 s t \ annulus p.2 s' t') := by
    have hm : MeasurableSet (annulus (0 : ℂ) s t \ annulus 0 s' t') :=
      (isOpen_ball.measurableSet.diff measurableSet_closedBall).diff
        (isOpen_ball.measurableSet.diff measurableSet_closedBall)
    rw [show ν p = (μ p.1).map (fun x => x-p.2) from rfl, Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [annulus, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm]
  have h := (measurableSet_relativeCollarFailure r η d).preimage hν
  simpa only [Set.preimage_ofPred_eq, RelativeCollarFailure, htransport, htransport'] using h

open Classical in
/-- The first-moment frequency estimate for rooted relative-collar failures.
The individual probabilities must still be bounded at the chosen scales. -/
theorem mul_measure_root_relativeCollarFailure_count_le
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure (Ω × ℂ))
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (r : ℕ → ℝ) (η : ℝ) (d : ℝ≥0∞) (s : Finset ℕ) (k : ℕ) :
    (k : ℝ≥0∞) * Q {p | k ≤ (s.filter fun i =>
      d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card} ≤
    ∑ i ∈ s, Q {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} := by
  simpa only [mem_ofPred_eq] using mul_measure_failure_count_le_sum Q s _
    (fun i _ => measurableSet_root_relativeCollarFailure μ hμ hloc (r i) η d) k

end HarmonicBalls.Section6
