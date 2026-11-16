import HarmonicBalls.Proofs.Sec11.CorrectedLocalThirdPositive

/-! # Transfer of local pinch probabilities under potential comparison -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter
open scoped ENNReal

/-- A deterministic comparison of the annulus potentials and almost-everywhere
identification of the other event expressions transfer the local triple probability. -/
theorem pinchLocal_three_positive_of_potential_comparison
    {U V W T Q' Q : Set ℂ} {δ γ α ξ : ℝ}
    (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hDm : IsLQGMetricOfField P γ ξ α hC D)
    (paperPotential paperMass : Ω → ℝ≥0∞) (paperFirst paperSecondMetric paperThird : Ω → Prop)
    (c : ℝ) (hc : 0 < c)
    (hcompare : ∀ᵐ ω ∂P,
      paperPotential ω ≤ ENNReal.ofReal c * annulusGreenPotentialSup (μ ω) 0 3 6 ∧
      (paperFirst ω ↔ pinchFirstEventLocal (D ω) W T Q' Q δ) ∧
      (paperSecondMetric ω ↔
        internalDiam (D ω) δ (closure V) <
          ENNReal.ofReal (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ)))) ∧
      (paperThird ω ↔ pinchThirdEventLocal (D ω) V W δ) ∧
      paperMass ω = μ ω U) :
    ∀ M : ℝ, 0 < M →
      0 < P {ω | paperFirst ω ∧
        (paperSecondMetric ω ∧ ENNReal.ofReal M * paperPotential ω < paperMass ω) ∧
        paperThird ω} := by
  intro M hM
  have hpos := pinchLocal_three_positive hG hγ0 hγ2 (mul_pos hM hc) hα
    P hC hcirc μ D hGFF hμ hDm
  refine hpos.trans_le (measure_mono_ae ?_)
  filter_upwards [hcompare] with ω hω hmem
  rcases hω with ⟨hpot, hfirst, hsecond, hthird, hmass⟩
  rcases hmem with ⟨hfirst', hsecond', hthird'⟩
  refine ⟨hfirst.mpr hfirst', ⟨hsecond.mpr hsecond'.1, ?_⟩, hthird.mpr hthird'⟩
  rw [hmass]
  calc
    ENNReal.ofReal M * paperPotential ω ≤
        ENNReal.ofReal M * (ENNReal.ofReal c * annulusGreenPotentialSup (μ ω) 0 3 6) :=
      by gcongr
    _ = ENNReal.ofReal (M * c) * annulusGreenPotentialSup (μ ω) 0 3 6 := by
      rw [ENNReal.ofReal_mul hM.le, mul_assoc]
    _ < μ ω U := hsecond'.2

end HarmonicBalls
