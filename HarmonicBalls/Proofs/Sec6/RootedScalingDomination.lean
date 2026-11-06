import HarmonicBalls.Proofs.Sec6.RootedCollarRescaling

/-! # The strength of rooted measure-law domination

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set
open scoped ENNReal

/-- For two measurable images of the same finite measure, domination is
already equality: their total masses coincide. -/
theorem map_le_iff_map_eq_of_finite
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) [IsFiniteMeasure Q] {f g : α → β}
    (hf : Measurable f) (hg : Measurable g) :
    Q.map f ≤ Q.map g ↔ Q.map f = Q.map g := by
  constructor
  · intro h
    apply Measure.eq_of_le_of_measure_univ_eq h
    simp only [Measure.map_apply hf MeasurableSet.univ,
      Measure.map_apply hg MeasurableSet.univ, preimage_univ]
  · intro h
    exact h.le

/-- The domination premise used for rooted collar frequency is equivalent to
exact stationarity of the recentered normalized measure law at each scale.
This is a structural observation and does not assert that LQG has this law. -/
theorem rooted_rescaled_measure_law_le_iff_eq
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure (Ω × ℂ)) [IsFiniteMeasure Q]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (r : ℝ) (t : Ω × ℂ → ℝ≥0∞) (ht : Measurable t) :
    Q.map (fun p => t p • ((μ p.1).map (fun x : ℂ => x-p.2)).map
        (fun x : ℂ => r⁻¹ • x)) ≤
      Q.map (fun p => (μ p.1).map (fun x : ℂ => x-p.2)) ↔
    Q.map (fun p => t p • ((μ p.1).map (fun x : ℂ => x-p.2)).map
        (fun x : ℂ => r⁻¹ • x)) =
      Q.map (fun p => (μ p.1).map (fun x : ℂ => x-p.2)) := by
  apply map_le_iff_map_eq_of_finite Q
  · exact measurable_normalized_recenter_rescale_measure μ hμ hloc r t ht
  · exact measurable_map_of_locallyFinite (hμ.comp measurable_fst) (fun p => hloc p.1)
      (f := fun p : (Ω × ℂ) × ℂ => p.2-p.1.2) (by fun_prop)

end HarmonicBalls.Section6
