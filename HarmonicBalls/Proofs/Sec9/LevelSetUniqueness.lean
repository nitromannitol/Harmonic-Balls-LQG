import HarmonicBalls.Proofs.Sec9.BoundaryExteriorDefect

/-! # Weak uniqueness for level-set frontiers

For each continuous function, a locally finite Liouville measure charges at
most countably many of its level sets. This gives weak uniqueness for
comparison balls whose common frontier lies in any other level set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- Almost surely, simultaneously for every continuous real-valued function,
all but countably many levels are null. The exceptional set may depend on the
function and the realization. -/
theorem ae_lqg_countable_positive_level_sets
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      {r : ℝ | 0 < μ ω {x | f x = r}}.Countable := by
  filter_upwards [hμ] with ω hlim
  let : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  intro f hf
  exact Measure.countable_meas_level_set_pos hf.measurable

/-- Under I2, for each continuous function, weak uniqueness holds for all
comparison balls whose common frontier lies in a level set outside a countable
exceptional set. All poles, masses and ambient radii are simultaneous. -/
theorem ae_subharmonicBall_sandwich_of_level_set_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      ∃ E : Set ℝ, E.Countable ∧ ∀ r ∉ E,
      ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
        z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
        frontier (cluster (μ ω) R z t) ∩ frontier A ⊆ {x | f x = r} →
        cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqg_countable_positive_level_sets hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount hcompare
  intro f hf
  refine ⟨{r | 0 < μ ω {x | f x = r}}, hcount f hf, ?_⟩
  intro r hr A z t R ht hR hz hcl hA hmass hcover
  apply hcompare A z t R ht hR hz hcl hA hmass
  apply measure_mono_null hcover
  exact le_antisymm (le_of_not_gt hr) zero_le

/-- For each continuous function, all but countably many strict sublevel
sets satisfy the weak-uniqueness inclusions whenever they are subharmonic
balls with the stated mass and compact containment. -/
theorem ae_subharmonicBall_sandwich_for_sublevels
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f →
      ∃ E : Set ℝ, E.Countable ∧ ∀ r ∉ E,
      ∀ (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
        z ∈ ball (0 : ℂ) R → closure {x | f x < r} ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) {x | f x < r} z →
        μ ω {x | f x < r} = ENNReal.ofReal t →
        cluster (μ ω) R z t ⊆ {x | f x < r} ∧
        {x | f x < r} ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen {x | f x < r} →
          regularizedCluster (μ ω) R z t = {x | f x < r}) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_level_set_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcompare
  intro f hf
  obtain ⟨E, hE, hlevel⟩ := hcompare f hf
  refine ⟨E, hE, ?_⟩
  intro r hr z t R ht hR hz hcl hA hmass
  apply hlevel r hr _ z t R ht hR hz hcl hA hmass
  apply inter_subset_right.trans
  intro x hx
  have hx' := hf.frontier_preimage_subset (Iio r) hx
  change f x = r
  simpa only [frontier_Iio, mem_preimage, mem_singleton_iff] using hx'

end HarmonicBalls
