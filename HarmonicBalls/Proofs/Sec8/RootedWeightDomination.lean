import HarmonicBalls.Proofs.Sec11.PinchUnnormalizedKernel

/-! # Domination of localized rooted laws

A weighted root restricted to a set is dominated by the unweighted root
restricted to a larger set. This isolates the deterministic weight from a
rooted field comparison.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A weighted rooted law on a measurable set is dominated by the unweighted
rooted law on any measurable superset, provided the two restriction kernels
are represented by their intended finite measures. -/
theorem unnormalizedWeightedRestrictionKernel_compProd_ac_of_subset
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B U : Set ℂ) (hB : MeasurableSet B) (hU : MeasurableSet U) (hBU : B ⊆ U)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hfinB : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞)
    (hfinU : ∀ᵐ ω ∂P, (μ ω) U ≠ ∞) :
    P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ B hB w hw) ≪
      P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ U hU (fun _ => 1) measurable_const) := by
  apply Measure.AbsolutelyContinuous.compProd_right
  have hfinU' : ∀ᵐ ω ∂P, ((μ ω).withDensity (fun _ => 1)) U ≠ ∞ := by
    simpa only [withDensity_const, one_smul] using hfinU
  filter_upwards [ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ B hB w hw hfinB,
    ae_unnormalizedWeightedRestrictionKernel_eq P μ hμ U hU (fun _ => 1)
      measurable_const hfinU'] with ω hBω hUω
  rw [hBω, hUω, withDensity_const, one_smul, restrict_withDensity hB]
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono_set (μ ω) hBU))

/-- For a locally finite random measure, every weighted localization is
dominated by an unweighted rooted law on the containing ball. -/
theorem unnormalizedWeightedLocalization_compProd_ac_ball
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) (n : ℕ) :
    P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ (weightedLocalization w n)
      (measurableSet_weightedLocalization hw n) w hw) ≪
      P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ (ball 0 ((n : ℝ) + 1))
        measurableSet_ball (fun _ => 1) measurable_const) := by
  apply unnormalizedWeightedRestrictionKernel_compProd_ac_of_subset P μ hμ
    (weightedLocalization w n) (ball 0 ((n : ℝ) + 1))
    (measurableSet_weightedLocalization hw n) measurableSet_ball (inter_subset_left) w hw
  · filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    exact weightedLocalization_measure_ne_top (μ ω) hw n
  · filter_upwards [hloc] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω
    exact measure_ball_lt_top.ne

/-- Fixed-root estimates transfer to typical points when the unweighted rooted
law on each localization ball has the required shifted reference-law bound. -/
theorem ae_ae_of_unweighted_ball_shiftedRootReferenceLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ z, w z ≠ 0) (hfin : ∀ z, w z ≠ ∞)
    (ρ : ℕ → Measure ℂ) (shift : ℕ → ℂ × Ω → Ω)
    (hshift : ∀ n, Measurable (shift n)) (Q : ℕ → ℂ → Measure Ω)
    {p : Ω → ℂ → Prop} (hp : MeasurableSet {x : Ω × ℂ | p x.1 x.2})
    (hrooted : ∀ n : ℕ, P ⊗ₘ (unnormalizedWeightedRestrictionKernel P μ hμ
      (ball 0 ((n : ℝ) + 1)) measurableSet_ball (fun _ => 1) measurable_const) ≪
        shiftedRootReferenceLaw (ρ n) P (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, P.map (fun ω => shift n (z, ω)) ≪ Q n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ ω ∂Q n z, p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  apply ae_ae_of_unnormalized_shiftedRootReferenceLaw P μ hμ hloc w hw hpos hfin
    ρ shift hshift Q hp ?_ hac hfixed
  intro n
  exact (unnormalizedWeightedLocalization_compProd_ac_ball P μ hμ hloc w hw n).trans
    (hrooted n)

end HarmonicBalls
