import HarmonicBalls.Proofs.Sec5.UniformLocalHorizon
import HarmonicBalls.Proofs.Sec5.ScalingMeasure
import HarmonicBalls.Proofs.Sec5.DyadicGeometricScaling

/-! # Uniform local properties at dyadic normalized horizons -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory TopologicalSpace Filter
open scoped Pointwise

/-- The countable-centre horizons with a common law also carry the uniform
local properties of each normalized pullback, assuming countable-centre coverage
at every dyadic scale. -/
theorem dyadicNormalizedHorizonProperties_of_steps
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (hfam : ClusterFamilyMeasurabilityStep.{u})
    {ι : Type*} [Countable ι] (e : ι → {z // z ∈ ball (0 : ℂ) (1 / 2)})
    (hcover : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∀ (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) (t : Ioi (0 : ℝ)),
        cluster (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 j t ⊆
          closure (⋃ i, cluster
            (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 (e i) t)) :
    ∃ T : ℕ → Ω → ℝ, (∀ n, IdentDistrib (T n) (T 0) P P) ∧
      (∀ᵐ ω ∂P, 0 < T 0 ω) ∧
      ∀ᵐ ω ∂P, ∀ n, ∀ z ∈ ball (0 : ℂ) (1 / 2),
        SatisfiesHarmonicBallConditionsOn
          (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω))
          (regularizedCluster
            (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z) z (T n ω) ∧
        ∀ t ∈ Ioo 0 (T n ω),
          closure (cluster (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t) ⊆
            ball 0 1 ∧
          normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)
            (frontier (cluster
              (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t)) = 0 := by
  obtain ⟨T, hlaw, hpos, hT⟩ := dyadicCountableCentresHorizons_of_steps
    h hAff hCC hγ hγ2 hα hμ h71 hfam e
  refine ⟨T, hlaw, hpos, ?_⟩
  apply ae_all_iff.mpr
  intro n
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by positivity
  let C := fun (ω : Ω) (φ : ℂ → ℝ) => (k ^ 2)⁻¹ * hC ω (fun y => φ (y / (k : ℂ))) -
    hcirc ω k 0 * ∫ x, φ x
  let circ := fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0
  let ν := fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)
  have hGFFscaled : IsWholePlaneGFF P C circ := by
    have hh := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
    simpa only [C, circ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hk, Complex.real_smul, add_zero, sub_zero] using hh
  have hν : IsLQGMeasureOfField P γ α₀ circ ν :=
    isLQGMeasureOfField_normalizedPullback hCC h hγ hγ2 hα hμ hk
  have hp := (uniformLocalHorizon_specified_of_countableCentres hGFFscaled hγ hγ2 hα hν
    h32 h33 h53 h54 h71 hfam e (hcover n)).2
  filter_upwards [hp] with ω hω
  have heq : T n ω = realDenseSequenceBallHorizon (3 / 4)
      (fun i t => cluster (ν ω) 1 (e i) t) := by
    rw [hT n ω]
    congr 1
    funext i t
    let a := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0))
    have ha : 0 < a := Real.exp_pos _
    have hs := cluster_scaled_measure (μ := μ ω) (R := 1) (z := (e i : ℂ))
      (k := k) (c := a⁻¹) (t := t) hk (inv_pos.mpr ha) t.property.le
    simpa only [ν, normalizedPullbackMeasure, ← ENNReal.ofReal_inv_of_pos ha,
      inv_inv, mul_one, a, k] using hs.symm
  rw [heq]
  exact hω.2

end HarmonicBalls
