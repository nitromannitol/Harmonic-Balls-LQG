import HarmonicBalls.Proofs.Sec5.UniformFailureEvents
import HarmonicBalls.Proofs.Sec5.UniformContainment
import HarmonicBalls.Proofs.Sec5.ClusterGeometricScaling
import HarmonicBalls.Proofs.Sec5.DyadicIntervals
import HarmonicBalls.Proofs.Sec5.ScalingMeasure

/-! # Cofinal intervals from uniform small-time cluster estimates -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The event that all unit-scale clusters of the dyadically normalized
measure are contained in the unit ball up to a specified small time. -/
def normalizedDyadicContainmentEvent {Ω : Type*} (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (m n : ℕ) : Set Ω :=
  {ω | ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) ((2 : ℝ)⁻¹ ^ m),
    closure (cluster (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t) ⊆
      ball 0 1}

/-- Cofinal intervals follow from uniformly small outer probabilities of
failure of the dyadically normalized containment events. No measurability
of cluster families, coverage by countably many centres, or independence
between scales is assumed. The affine field and coordinate-change inputs
are explicit hypotheses. -/
theorem cofinalRegularizedClusterIntervals_of_uniformFailure
    (h32 : ClusterOpenLaplacianStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc)
    (htail : ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∃ b : ℕ → ℝ≥0∞, (⨅ m, b m) = 0 ∧ ∀ m n,
          P (normalizedDyadicContainmentEvent γ α₀ hcirc μ m n)ᶜ ≤ b m) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ
  obtain ⟨b, hb0, hb⟩ := htail γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ
  have hprops : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ H : ℝ, 0 < H →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) H,
        closure (cluster (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t) ⊆
          ball 0 1) →
      ∀ z ∈ ball (0 : ℂ) (1 / 2),
        SatisfiesHarmonicBallConditionsOn
          (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω))
          (regularizedCluster
            (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z) z H ∧
        ∀ t ∈ Ioo 0 H,
          closure (cluster (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t) ⊆
            ball 0 1 ∧
          normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)
            (frontier (cluster
              (normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)) 1 z t)) = 0 := by
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
    exact ae_uniformLocalClusterProperties_of_containment hGFFscaled hγ hγ2 hα hν h32 h53 h54
  apply ae_cofinal_local_intervals_of_uniform_failure P μ
    (fun n _ => (2 : ℝ) ^ n) (fun n ω => dyadicClusterScaleFactor γ α₀ (hcirc ω) n)
    (fun m => (2 : ℝ)⁻¹ ^ m) (normalizedDyadicContainmentEvent γ α₀ hcirc μ) b
    (fun _ => by positivity) hb hb0
  · filter_upwards [h.ae_dyadic_scaleFactor_tendsto_atTop hγ hα] with ω hω
    exact ⟨tendsto_pow_atTop_atTop_of_one_lt (by norm_num), hω⟩
  · filter_upwards [ae_all_iff.mpr hprops] with ω hω
    intro m n hgood z hz
    have hunit := hω n ((2 : ℝ)⁻¹ ^ m) (by positivity) hgood
    have hscaled := uniformLocalClusterProperties_normalizedPullback_scale
      (γ := γ) (α₀ := α₀) (hcirc := hcirc ω) (μ := μ ω)
      (k := (2 : ℝ) ^ n) (H := (2 : ℝ)⁻¹ ^ m) (by positivity) hunit
    simpa only [dyadicClusterScaleFactor] using hscaled z hz

end HarmonicBalls
