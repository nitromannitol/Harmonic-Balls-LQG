import HarmonicBalls.Proofs.Sec9.HarmonicMeasureUniqueness
import HarmonicBalls.Proofs.Sec9.RegularOpenEqOfAEEq
import HarmonicBalls.Proofs.Sec5.RegularizedGeometry

/-! # Set inclusions from weak uniqueness

Full support turns the null weak-uniqueness defect into a set inclusion.
For regular-open comparison balls this identifies the ball with the
regularized cluster, without requiring its frontier to be null.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- The weak uniqueness conclusion and full support give a sandwich between
the cluster and its regularization; regular-open comparison sets are equal
to the regularized cluster. -/
theorem regularizedCluster_sandwich_of_weak_uniqueness
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {A : Set ℂ} {R t : ℝ} {z : ℂ}
    (hA : IsOpen A) (hsub : cluster μ R z t ⊆ A)
    (hzero : μ (A \ regularizedCluster μ R z t) = 0) :
    cluster μ R z t ⊆ A ∧ A ⊆ regularizedCluster μ R z t ∧
      (IsRegularOpen A → regularizedCluster μ R z t = A) := by
  have hreg : A ⊆ regularizedCluster μ R z t :=
    (isRegularOpen_regularizedCluster μ R z t).subset_of_measure_diff_eq_zero hA hzero
  refine ⟨hsub, hreg, ?_⟩
  intro hregular
  apply Subset.antisymm ?_ hreg
  change interior (closure (cluster μ R z t)) ⊆ A
  rw [← hregular]
  exact interior_mono (closure_mono hsub)

/-- Weak Proposition 9.2 and volume growth yield set inclusions for every
subharmonic ball, and equality for regular-open comparison balls. -/
theorem ae_subharmonicBall_sandwich_of_weak_uniqueness
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hweak : SubharmonicBallUniquenessWeakStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hweak γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hweakω hfull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro A z t R ht hR hz hcl hA hmass
  obtain ⟨hsub, hzero⟩ := hweakω A z t R ht hR hz hcl hA hmass
  exact regularizedCluster_sandwich_of_weak_uniqueness hA.1 hsub hzero

/-- The sandwich for comparison balls contained in the unit disk requires
only I2 and Lemmas 6.9 and 8.2, with arbitrary ambient radius. -/
theorem ae_subharmonicBall_sandwich_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R → closure A ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_weak_uniqueness_inside_unit_disc_of_harmonicMeasure
      hI2 h69 h82 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hweakω hfull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro A z t R ht hR hz hcl hcl1 hA hmass
  obtain ⟨hsub, hzero⟩ := hweakω A z t R ht hR hz hcl hcl1 hA hmass
  exact regularizedCluster_sandwich_of_weak_uniqueness hA.1 hsub hzero

/-- The sandwich and regular-open equality follow from I2, Lemmas 6.9 and
8.2, and the staged affine-invariance and coordinate-change inputs. -/
theorem ae_subharmonicBall_sandwich_of_harmonicMeasure_and_typical_scales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) :=
  ae_subharmonicBall_sandwich_of_weak_uniqueness hI2
    (subharmonicBallUniquenessWeak_of_harmonicMeasure_and_typical_scales hI2 h69 h82 hAff hCC)

end HarmonicBalls
