import HarmonicBalls.Proofs.Sec6.RootedCollarRescaling
import HarmonicBalls.Proofs.Sec6.RootedRelativeCollar

/-! # Collar frequency from rescaled rooted measure laws

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

open Classical in
/-- If the laws of the normalized, recentered and rescaled measures are all
bounded by one regular rooted reference law, a fixed relative collar width
controls the failure count over every finite set of scales. The measure-law
bound is a hypothesis and is not a sampled-root GFF law identification. -/
theorem exists_rescaled_root_relativeCollar_failure_count_le
    {Ω : Type*} [MeasurableSpace Ω] (Q Q₀ : Measure (Ω × ℂ)) [IsFiniteMeasure Q₀]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (t : ℕ → Ω × ℂ → ℝ≥0∞) (ht : ∀ i, Measurable (t i))
    (ht0 : ∀ i p, t i p ≠ 0) (htop : ∀ i p, t i p ≠ ∞)
    (hdom : ∀ i,
      Q.map (fun p => t i p • ((μ p.1).map (fun x : ℂ => x-p.2)).map
        (fun x : ℂ => (r i)⁻¹ • x)) ≤
      Q₀.map (fun p => (μ p.1).map (fun x : ℂ => x-p.2)))
    (hreg : ∀ᵐ p ∂Q₀, μ p.1 (sphere p.2 3) = 0 ∧
      μ p.1 (sphere p.2 5) = 0 ∧ 0 < μ p.1 (annulus p.2 3 5))
    {c : ℝ} (hc : 0 < c) {d q : ℝ≥0∞} (hd : 0 < d) (hq : 0 < q) :
    ∃ η : ℝ, 0 < η ∧ η < c ∧ ∀ (s : Finset ℕ) (k : ℕ),
      (k : ℝ≥0∞) * Q {p | k ≤ (s.filter fun i =>
        d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))).card} ≤
      (s.card : ℝ≥0∞) * q := by
  have htrans : Measurable (fun p : Ω × ℂ => (μ p.1).map (fun x : ℂ => x-p.2)) :=
    measurable_map_of_locallyFinite (hμ.comp measurable_fst) (fun p => hloc p.1)
      (f := fun p : (Ω × ℂ) × ℂ => p.2-p.1.2) (by fun_prop)
  have htend := tendsto_rooted_relative_collar_failure Q₀ μ hμ hloc 3 5 hd hreg
  have hw := tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hc)
  obtain ⟨n, hn, hnc⟩ := ((htend.eventually_lt_const hq).and hw).exists
  let η : ℝ := 1 / ((n : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  let E : Set (Measure ℂ) := {ν | RelativeCollarFailure ν 1 η d}
  have hE : MeasurableSet E := measurableSet_relativeCollarFailure 1 η d
  have hsingle (i : ℕ) : Q {p | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
      μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
        annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} ≤ q := by
    have heq : {p : Ω × ℂ | d * μ p.1 (annulus p.2 (3*r i) (5*r i)) <
        μ p.1 (annulus p.2 (3*r i-η*r i) (5*r i+η*r i) \
          annulus p.2 (3*r i+η*r i) (5*r i-η*r i))} =
        (fun p : Ω × ℂ => t i p • ((μ p.1).map (fun x : ℂ => x-p.2)).map
          (fun x : ℂ => (r i)⁻¹ • x)) ⁻¹' E := by
      ext p
      exact (relativeCollarFailure_recenter_rescale (μ p.1) p.2 (hr i) η d
        (t i p) (ht0 i p) (htop i p)).symm
    have href : (fun p : Ω × ℂ => (μ p.1).map (fun x : ℂ => x-p.2)) ⁻¹' E =
        {p | d * μ p.1 (annulus p.2 3 5) <
          μ p.1 (annulus p.2 (3-η) (5+η) \ annulus p.2 (3+η) (5-η))} := by
      ext p
      simpa only [E, mem_preimage, mem_ofPred_eq, mul_one] using
        relativeCollarFailure_map_sub (μ p.1) p.2 1 η d
    rw [heq, ← Measure.map_apply (measurable_normalized_recenter_rescale_measure μ hμ hloc
      (r i) (t i) (ht i)) hE]
    calc
      _ ≤ (Q₀.map (fun p => (μ p.1).map (fun x : ℂ => x-p.2))) E := hdom i E
      _ = Q₀ _ := by rw [Measure.map_apply htrans hE, href]
      _ ≤ q := hn.le
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
