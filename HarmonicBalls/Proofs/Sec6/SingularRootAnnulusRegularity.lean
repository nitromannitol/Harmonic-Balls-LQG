import HarmonicBalls.Proofs.Sec6.WeightedRootAnnulusRegularity
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure

/-! # Zero-singularity annuli at singular LQG roots

The imported Section 6 iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Under volume growth, the singular LQG measure is absolutely continuous
with respect to the zero-singularity measure constructed from the same field. -/
theorem ae_singular_lqg_absolutelyContinuous_zero
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀) :
    ∀ᵐ ω ∂P, μ ω ≪ μ₀ ω := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨_, _, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα h hμ
  obtain ⟨_, _, hV₀⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hQ h hμ₀
  have hW := lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  filter_upwards [hV, hV₀, hμ, hW h hγ hγ2 hQ μ₀ hμ₀] with ω hV hV₀ hm hw
  have hz : μ ω {0} = 0 := (hV.2 1 (by norm_num)).measure_singleton (by simp)
  have hz₀ : μ₀ ω {0} = 0 := (hV₀.2 1 (by norm_num)).measure_singleton (by simp)
  rw [eq_singularWeight_of_origin_nonatomic hm hw hz hz₀]
  exact withDensity_absolutelyContinuous _ _

/-- Zero-singularity annuli have null boundary and positive mass at every
positive radius around roots sampled from any measure absolutely continuous
with respect to a singular LQG measure of the same field. -/
theorem ae_zero_annulus_regular_at_singular_roots
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀) :
    ∀ᵐ ω ∂P, ∀ ν : Measure ℂ, ν ≪ μ ω → ∀ᵐ z ∂ν, ∀ r : ℝ, 0 < r →
      μ₀ ω (sphere z (3 * r)) = 0 ∧ μ₀ ω (sphere z (5 * r)) = 0 ∧
        0 < μ₀ ω (annulus z (3 * r) (5 * r)) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  filter_upwards [ae_singular_lqg_absolutelyContinuous_zero hgrowth hγ hγ2 hα h hμ hμ₀,
    ae_lqg_ae_root_annulus_regular hgrowth hγ hγ2 hQ h hμ₀] with ω hac hreg ν hν
  exact hreg ν (hν.trans hac)

/-- The staged zero-strength existence input supplies the reference measure
for the preceding regularity result. -/
theorem exists_zero_lqg_annulus_regular_at_singular_roots
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hE₀ : LQGMeasureExistence P γ 0 hC hcirc) :
    ∃ μ₀ : Ω → Measure ℂ, IsLQGMeasureOfField P γ 0 hcirc μ₀ ∧
      ∀ᵐ ω ∂P, ∀ ν : Measure ℂ, ν ≪ μ ω → ∀ᵐ z ∂ν, ∀ r : ℝ, 0 < r →
        μ₀ ω (sphere z (3 * r)) = 0 ∧ μ₀ ω (sphere z (5 * r)) = 0 ∧
          0 < μ₀ ω (annulus z (3 * r) (5 * r)) := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE₀ h hγ hγ2 hQ
  exact ⟨μ₀, hμ₀, ae_zero_annulus_regular_at_singular_roots hgrowth hγ hγ2 hα h hμ hμ₀⟩

end HarmonicBalls.Section6
