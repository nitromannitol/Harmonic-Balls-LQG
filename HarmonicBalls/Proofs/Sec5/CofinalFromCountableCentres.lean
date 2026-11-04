import HarmonicBalls.Proofs.Sec5.DyadicHorizonProperties

/-! # Cofinal local intervals from countable-centre coverage -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set Filter

/-- Countable-centre coverage, fixed-centre measurability, the earlier cluster
estimates, and the explicit field scaling inputs imply the cofinal regularized
cluster intervals. -/
theorem cofinalRegularizedClusterIntervals_of_countableCentres
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (hfam : ClusterFamilyMeasurabilityStep.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc)
    (e : ℕ → {z // z ∈ ball (0 : ℂ) (1 / 2)})
    (hcover : ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∀ (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) (t : Ioi (0 : ℝ)),
          cluster (μ ω) 1 j t ⊆ closure (⋃ i, cluster (μ ω) 1 (e i) t)) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_normalizedDyadicEstimates
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ
  apply dyadicNormalizedHorizonProperties_of_steps h (hAff P hC hcirc)
    (hCC P γ α₀ hC hcirc) hγ hγ2 hα hμ h32 h33 h53 h54 h71 hfam e
  intro n
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by positivity
  let C := fun (ω : Ω) (φ : ℂ → ℝ) => (k ^ 2)⁻¹ * hC ω (fun y => φ (y / (k : ℂ))) -
    hcirc ω k 0 * ∫ x, φ x
  let circ := fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0
  let ν := fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)
  have hGFFscaled : IsWholePlaneGFF P C circ := by
    have hh := hAff P hC hcirc h (k : ℂ) (by exact_mod_cast hk.ne') 0
    simpa only [C, circ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hk, Complex.real_smul, add_zero, sub_zero] using hh
  have hν : IsLQGMeasureOfField P γ α₀ circ ν :=
    isLQGMeasureOfField_normalizedPullback (hCC P γ α₀ hC hcirc) h hγ hγ2 hα hμ hk
  exact hcover γ α₀ hγ hγ2 hα Ω P C circ ν hGFFscaled hν

end HarmonicBalls
