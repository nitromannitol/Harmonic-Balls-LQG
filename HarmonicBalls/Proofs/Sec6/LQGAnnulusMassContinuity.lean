import HarmonicBalls.Proofs.Sec6.AnnulusMassContinuity
import HarmonicBalls.Proofs.Sec9.CircleCoverUniqueness

/-! # Annulus-mass continuity for LQG measures

The volume-growth input gives local finiteness and non-atomicity. Consequently
annulus mass is jointly continuous in the centre and radius outside one
random countable set of centres. This does not establish continuity of the
Brownian avoidance probabilities defining a good annulus.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- An atomless locally finite planar measure has jointly continuous annulus
mass at every radius, except possibly for a countable set of centres. -/
theorem exists_countable_exceptional_centers_annulus_mass_continuous
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∃ E : Set ℂ, E.Countable ∧ ∀ z ∉ E, ∀ r : ℝ,
      ContinuousAt (fun p : ℂ × ℝ => μ (annulus p.1 (3 * p.2) (5 * p.2))) (z, r) := by
  obtain ⟨E, hE, hnull⟩ := exists_countable_centers_spheres_null μ
  refine ⟨E, hE, ?_⟩
  intro z hz r
  exact tendsto_annulus_mass_of_null_boundary μ (continuous_fst.tendsto (z, r))
    (continuous_snd.tendsto (z, r)) (hnull z hz (3 * r)) (hnull z hz (5 * r))

universe u

/-- Under the volume-growth input, the random LQG annulus mass is jointly
continuous in its centre and radius outside one countable set of centres. -/
theorem ae_lqg_annulus_mass_continuous_except_countable_centers
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∃ E : Set ℂ, E.Countable ∧ ∀ z ∉ E, ∀ r : ℝ,
      ContinuousAt (fun p : ℂ × ℝ => μ ω (annulus p.1 (3 * p.2) (5 * p.2))) (z, r) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, ae_lqg_spheres_null_except_countable_centers hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV ⟨E, hE, hnull⟩
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  refine ⟨E, hE, ?_⟩
  intro z hz r
  exact tendsto_annulus_mass_of_null_boundary (μ ω) (continuous_fst.tendsto (z, r))
    (continuous_snd.tendsto (z, r)) (hnull z hz (3 * r)) (hnull z hz (5 * r))

end HarmonicBalls.Section6
