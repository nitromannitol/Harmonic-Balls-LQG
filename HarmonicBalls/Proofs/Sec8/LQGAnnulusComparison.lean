import HarmonicBalls.Proofs.Sec8.AnnulusComparisonProbability
import HarmonicBalls.Draft.Section2

/-!
# LQG annulus-comparison probability

Locality, full support and local finiteness provide the regularity hypotheses
for the one-scale ratio argument. The scale-invariance of its law remains an
explicit hypothesis.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Every dyadic annulus is a nonempty open subset of the plane. -/
theorem isOpen_nonempty_dyadicAnnulus (z : ℂ) (n : ℕ) :
    IsOpen (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ∧
      (annulus z (dyadicScale (n + 1)) (dyadicScale n)).Nonempty := by
  have hr : 0 < dyadicScale n := dyadicScale_pos n
  have hnext : dyadicScale (n + 1) = dyadicScale n / 2 := by
    simp [dyadicScale, pow_succ, div_eq_mul_inv]
  constructor
  · exact isOpen_ball.sdiff isClosed_closedBall
  · refine ⟨z + (((3 / 4 : ℝ) * dyadicScale n : ℝ) : ℂ), ?_⟩
    have hd : dist (z + (((3 / 4 : ℝ) * dyadicScale n : ℝ) : ℂ)) z =
        (3 / 4 : ℝ) * dyadicScale n := by
      simp [dist_eq_norm, hr.le]
    change dist (z + (((3 / 4 : ℝ) * dyadicScale n : ℝ) : ℂ)) z < dyadicScale n ∧
      ¬ dist (z + (((3 / 4 : ℝ) * dyadicScale n : ℝ) : ℂ)) z ≤ dyadicScale (n + 1)
    rw [hd, hnext]
    constructor <;> linarith

/-- Full support and local finiteness give positive finite dyadic ball and
annulus masses simultaneously at every scale and centre. -/
theorem dyadicAnnulusMasses_pos_finite (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ U) (z : ℂ) (n : ℕ) :
    (μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ 0 ∧
      μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ ∞) ∧
    (μ (ball z (dyadicScale n)) ≠ 0 ∧ μ (ball z (dyadicScale n)) ≠ ∞) := by
  have hgeo := isOpen_nonempty_dyadicAnnulus z n
  have hballpos : 0 < μ (ball z (dyadicScale n)) :=
    hfull _ isOpen_ball ⟨z, mem_ball_self (dyadicScale_pos n)⟩
  have hballtop : μ (ball z (dyadicScale n)) ≠ ∞ := measure_ball_ne_top
  have hatop : μ (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ ∞ :=
    ne_top_of_le_ne_top hballtop (measure_mono Set.sdiff_subset)
  exact ⟨⟨(hfull _ hgeo.1 hgeo.2).ne', hatop⟩, ⟨hballpos.ne', hballtop⟩⟩

/-- Locality and full support reduce the uniform annulus comparison estimate
to equality of the lower-tail laws of the mass ratios. -/
theorem exists_lqg_annulusBallComparison_threshold_of_equal_lower_tails
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (z : ℂ)
    (hlaw : ∀ n a, P {ω | annulusBallMassRatio (μ ω) n z < a} =
      P {ω | annulusBallMassRatio (μ ω) 0 z < a})
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m ∈ Ioo (0 : ℝ) 1, ∀ n,
      P {ω | ¬ AnnulusBallComparison (μ ω) n z m} ≤ δ := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hmeas : AEMeasurable (fun ω => annulusBallMassRatio (μ ω) 0 z) P := by
    apply aemeasurable_annulusBallMassRatio
    · apply Section6.aemeasurable_lqg_measure_borel hγ hγ2 hα hGFF hμ hloc
      exact (isOpen_nonempty_dyadicAnnulus z 0).1.measurableSet
    · exact Section6.aemeasurable_lqg_measure_borel hγ hγ2 hα hGFF hμ hloc _ isOpen_ball.measurableSet
  have hmass : ∀ᵐ ω ∂P, ∀ n, (μ ω (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ 0 ∧
      μ ω (annulus z (dyadicScale (n + 1)) (dyadicScale n)) ≠ ∞) ∧
      (μ ω (ball z (dyadicScale n)) ≠ 0 ∧ μ ω (ball z (dyadicScale n)) ≠ ∞) := by
    filter_upwards [hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hωfull hωloc n
    let : IsLocallyFiniteMeasure (μ ω) := hωloc.isLocallyFiniteMeasure
    exact dyadicAnnulusMasses_pos_finite (μ ω) hωfull z n
  have hpos : ∀ᵐ ω ∂P, 0 < annulusBallMassRatio (μ ω) 0 z := by
    filter_upwards [hmass] with ω hω
    exact annulusBallMassRatio_pos (μ ω) 0 z (hω 0).1.1 (hω 0).1.2 (hω 0).2.1 (hω 0).2.2
  have hball : ∀ n, ∀ᵐ ω ∂P, μ ω (ball z (dyadicScale n)) ≠ 0 ∧
      μ ω (ball z (dyadicScale n)) ≠ ∞ := by
    intro n
    filter_upwards [hmass] with ω hω
    exact (hω n).2
  exact exists_annulusBallComparison_threshold_of_equal_lower_tails P μ z hmeas hpos hball hlaw hδ

end HarmonicBalls
