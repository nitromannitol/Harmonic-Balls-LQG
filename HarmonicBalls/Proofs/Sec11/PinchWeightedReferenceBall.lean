import HarmonicBalls.Proofs.Sec11.ShiftedNormalizedMeasureBetween

/-! # Reference-ball masses after a smooth Weyl shift

The underlying field decoder uses Leonardo Bonanno's LatticeProb formalization. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal

/-- A smooth Weyl weighting preserves positive finite mass of every
positive-radius reference ball. -/
theorem IsWholePlaneGFF.ae_weighted_referenceBall_pos_finite
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (g : ℂ → ℝ) (hg : Continuous g) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R) ≠ 0 ∧
      ((μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z)))) (ball 0 R) ≠ ∞ := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ hω => hω.isLocallyFiniteMeasure
  have hc := ae_all_iff.mpr fun n => h.ae_continuous_fieldCircleAverage α (dyadicScale_pos n)
  filter_upwards [ae_referenceBall_pos_finite P μ hfull hloc, hμ, hc] with ω hp hμω hcω R hR
  let w : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (γ * g z))
  let ν := (μ ω).withDensity w
  have hw : Measurable w := ((measurable_const.mul hg.measurable).exp).ennreal_ofReal
  have hw0 : ∀ z, w z ≠ 0 := fun z => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hAC : μ ω ≪ ν := withDensity_absolutelyContinuous' hw.aemeasurable
    (Filter.Eventually.of_forall hw0)
  have hνzero : ν (ball 0 R) ≠ 0 := fun hzero => (hp R hR).1 (hAC hzero)
  have hμshift := Section6.isLQGLimit_addCircleAverage hμω hcω g hg
  let : IsLocallyFiniteMeasure ν := hμshift.isLocallyFiniteMeasure
  exact ⟨hνzero, ne_of_lt (Metric.isBounded_ball.measure_lt_top (μ := ν))⟩

end HarmonicBalls
