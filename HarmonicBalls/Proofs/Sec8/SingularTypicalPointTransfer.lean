import HarmonicBalls.Proofs.Sec8.SingularRootedFrequencyExistingMeasure
import HarmonicBalls.Proofs.Sec6.VolumeGrowthNonatomic

/-! # Typical points of singular LQG measures

The local Weyl identity transfers almost-everywhere properties from an
existing regular LQG measure to an existing singular one, away from the
origin. The volume-growth input removes the exceptional origin. The imported
Section 8 development uses Leonardo Bonanno's `LatticeProb.Prob.Birkhoff`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The singular Weyl identity implies absolute continuity with respect to the
regular measure away from the insertion point. -/
theorem restrict_absolutelyContinuous_of_singular_weight
    {μ ν : Measure ℂ} {γ α : ℝ}
    (hweight : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ) :
    μ.restrict {0}ᶜ ≪ ν := by
  rw [hweight]
  exact Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous ν _)

/-- If the singular measure has no atom at the insertion point, it is
absolutely continuous with respect to the regular measure on the whole plane. -/
theorem absolutelyContinuous_of_singular_weight_of_origin_null
    {μ ν : Measure ℂ} {γ α : ℝ}
    (hweight : μ.restrict {0}ᶜ =
      (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ)
    (hzero : μ {0} = 0) : μ ≪ ν := by
  have hae : ∀ᵐ z ∂μ, z ∈ ({0} : Set ℂ)ᶜ := by
    simpa [ae_iff] using hzero
  have h := restrict_absolutelyContinuous_of_singular_weight hweight
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at h

/-- Existing regular and singular measures have absolutely continuous
restrictions away from the origin, without a non-atomicity assumption. -/
theorem IsWholePlaneGFF.ae_singular_restrict_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) :
    ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ ≪ ν ω := by
  filter_upwards [hGFF.ae_singular_weight_of_existing_regular_measure hμ hν] with ω hω
  exact restrict_absolutelyContinuous_of_singular_weight hω

/-- Away from the insertion point, properties at regular-measure-typical
points hold at singular-measure-typical points without a volume-growth input. -/
theorem IsWholePlaneGFF.ae_ae_singular_of_regular_away_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    {p : Ω → ℂ → Prop} (hp : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ≠ 0 → p ω z := by
  filter_upwards [hGFF.ae_singular_restrict_absolutelyContinuous hμ hν, hp]
    with ω hdom hpω
  have h := hdom.ae_le hpω
  exact (ae_restrict_iff' (measurableSet_singleton 0).compl).mp h

universe u

/-- Under the all-scales volume-growth input, an existing singular LQG measure
is absolutely continuous with respect to an existing regular measure of the
same field. -/
theorem IsWholePlaneGFF.ae_singular_absolutelyContinuous_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) :
    ∀ᵐ ω ∂P, μ ω ≪ ν ω := by
  have hnon := Section6.lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ α hC hcirc
    hGFF hγ hγ2 hα μ hμ
  filter_upwards [hGFF.ae_singular_weight_of_existing_regular_measure hμ hν, hnon]
    with ω hweight hnonω
  exact absolutelyContinuous_of_singular_weight_of_origin_null hweight (hnonω 0)

/-- A property holding at regular-measure-typical points also holds at
singular-measure-typical points of the same field. The property may depend on
the realization and need not be measurable. -/
theorem IsWholePlaneGFF.ae_ae_singular_of_regular_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    {p : Ω → ℂ → Prop} (hp : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, p ω z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  filter_upwards [hGFF.ae_singular_absolutelyContinuous_of_volumeGrowth
    hgrowth hγ hγ2 hα hμ hν, hp] with ω hdom hpω
  exact hdom.ae_le hpω

#print axioms restrict_absolutelyContinuous_of_singular_weight
#print axioms absolutelyContinuous_of_singular_weight_of_origin_null
#print axioms IsWholePlaneGFF.ae_singular_restrict_absolutelyContinuous
#print axioms IsWholePlaneGFF.ae_ae_singular_of_regular_away_zero
#print axioms IsWholePlaneGFF.ae_singular_absolutelyContinuous_of_volumeGrowth
#print axioms IsWholePlaneGFF.ae_ae_singular_of_regular_of_volumeGrowth

end HarmonicBalls
