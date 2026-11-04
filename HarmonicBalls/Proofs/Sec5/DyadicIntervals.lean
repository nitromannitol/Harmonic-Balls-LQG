import HarmonicBalls.Proofs.Sec5.CofinalIntervals
import HarmonicBalls.Proofs.Sec5.LargeCircleAverage

/-! # Cofinal intervals at dyadic radii -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- The scale factor of Lemma 5.7 at radius `2^n`. -/
noncomputable def dyadicClusterScaleFactor (γ α₀ : ℝ) (hcirc : ℝ → ℂ → ℝ) (n : ℕ) : ℝ :=
  Real.exp (γ * (lqgQ γ * Real.log ((2 : ℝ) ^ n) +
    fieldCircleAverage α₀ hcirc ((2 : ℝ) ^ n) 0))

/-- Cofinal intervals follow from the scaled local estimates and identically
distributed positive horizons at dyadic radii. Divergence of the scale
factors is proved from the GFF covariance. -/
theorem cofinalRegularizedClusterIntervals_of_dyadicEstimates
    (hscaled : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∃ T : ℕ → Ω → ℝ, (∀ n, ProbabilityTheory.IdentDistrib (T n) (T 0) P P) ∧
          (∀ᵐ ω ∂P, 0 < T 0 ω) ∧
          ∀ᵐ ω ∂P, ∀ n z, z ∈ ball (0 : ℂ) (((2 : ℝ) ^ n) / 2) →
            0 < dyadicClusterScaleFactor γ α₀ (hcirc ω) n * T n ω →
            SatisfiesHarmonicBallConditionsOn (μ ω)
              (regularizedCluster (μ ω) ((2 : ℝ) ^ n) z) z
              (dyadicClusterScaleFactor γ α₀ (hcirc ω) n * T n ω) ∧
            ∀ t ∈ Ioo 0 (dyadicClusterScaleFactor γ α₀ (hcirc ω) n * T n ω),
              closure (cluster (μ ω) ((2 : ℝ) ^ n) z t) ⊆ ball 0 ((2 : ℝ) ^ n) ∧
              μ ω (frontier (cluster (μ ω) ((2 : ℝ) ^ n) z t)) = 0) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_identDistrib
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨T, hlaw, hpos, hlocal⟩ := hscaled γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  refine ⟨fun n _ => (2 : ℝ) ^ n, fun n ω => dyadicClusterScaleFactor γ α₀ (hcirc ω) n,
    T, hlaw, hpos, ?_⟩
  filter_upwards [hlocal, hGFF.ae_dyadic_scaleFactor_tendsto_atTop hγ hα] with ω hω hA
  exact ⟨tendsto_pow_atTop_atTop_of_one_lt (by norm_num), hA, hω⟩

end HarmonicBalls
