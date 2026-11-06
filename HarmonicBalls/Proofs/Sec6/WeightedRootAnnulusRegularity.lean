import HarmonicBalls.Proofs.Sec6.WeightedRootNearbyDyadicCounts

/-! # Annular regularity at weighted LQG roots

The imported countable-centre iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The volume-growth input gives null boundary circles and positive annular
mass simultaneously at every positive radius for every root law absolutely
continuous with respect to the same LQG measure. The root law may depend on
the field. -/
theorem ae_lqg_ae_root_annulus_regular
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ ν : Measure ℂ, ν ≪ μ ω → ∀ᵐ z ∂ν, ∀ r : ℝ, 0 < r →
      μ ω (sphere z (3 * r)) = 0 ∧ μ ω (sphere z (5 * r)) = 0 ∧
        0 < μ ω (annulus z (3 * r) (5 * r)) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ2 hα
    Ω P hC hcirc μ h hμ
  filter_upwards [hV, hfull] with ω hV hfull
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 _ hR).measure_singleton hx⟩
  intro ν hν
  filter_upwards [hν.ae_le (ae_spheres_null_of_atomless (μ ω))] with z hz r hr
  exact ⟨hz _, hz _, annulus_three_five_pos_of_fullSupport (μ ω) hfull z hr⟩

/-- In particular, arbitrary weighted restrictions of the LQG measure have
regular annuli at their typical roots, without a normalization hypothesis. -/
theorem ae_lqg_ae_weighted_root_annulus_regular
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (w : ℂ → ℝ≥0∞) (B : Set ℂ),
      ∀ᵐ z ∂((μ ω).withDensity w).restrict B, ∀ r : ℝ, 0 < r →
      μ ω (sphere z (3 * r)) = 0 ∧ μ ω (sphere z (5 * r)) = 0 ∧
        0 < μ ω (annulus z (3 * r) (5 * r)) := by
  filter_upwards [ae_lqg_ae_root_annulus_regular hgrowth hγ hγ2 hα h hμ] with ω hω w B
  exact hω _ (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))

end HarmonicBalls.Section6
