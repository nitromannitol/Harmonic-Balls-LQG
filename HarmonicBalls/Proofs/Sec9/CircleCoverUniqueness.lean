import HarmonicBalls.Proofs.Sec10.CountableMassiveCircles

/-! # Weak uniqueness for frontiers covered by circles

Outside a countable set of centers, every circle is null for an atomless
locally finite planar measure. This gives weak uniqueness when the common
frontier is covered by countably many circles with nonexceptional centers.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- An atomless locally finite planar measure has only countably many centers
of circles of positive mass. -/
theorem exists_countable_centers_spheres_null (μ : Measure ℂ)
    [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∃ E : Set ℂ, E.Countable ∧ ∀ z ∉ E, ∀ r : ℝ, μ (sphere z r) = 0 := by
  let S : Set (ℂ × ℝ) := {a | 0 < μ (sphere a.1 a.2)}
  refine ⟨Prod.fst '' S, (countable_spheres_pos_measure μ).image Prod.fst, ?_⟩
  intro z hz r
  apply le_antisymm _ zero_le
  apply le_of_not_gt
  intro hpos
  apply hz
  exact ⟨(z, r), hpos, rfl⟩

universe u

/-- Under I2, almost surely all circles centered outside a countable set are
null simultaneously in their radii. -/
theorem ae_lqg_spheres_null_except_countable_centers
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∃ E : Set ℂ, E.Countable ∧ ∀ z ∉ E, ∀ r : ℝ, μ ω (sphere z r) = 0 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_countable_lqg_spheres_pos_measure_of_volumeGrowth hI2
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcount
  refine ⟨Prod.fst '' {a : ℂ × ℝ | 0 < μ ω (sphere a.1 a.2)}, hcount.image Prod.fst, ?_⟩
  intro z hz r
  apply le_antisymm _ zero_le
  apply le_of_not_gt
  intro hpos
  exact hz ⟨(z, r), hpos, rfl⟩

/-- Under I2, outside one countable exceptional set of circle centers, the
weak-uniqueness inclusions hold whenever the common frontier is covered by
countably many circles centered outside that set. The cover may depend on the
realization, comparison ball, pole, mass, and ambient radius. -/
theorem ae_subharmonicBall_sandwich_of_circle_cover
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∃ E : Set ℂ, E.Countable ∧
      ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
        z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
        ∀ (c : ℕ → ℂ) (r : ℕ → ℝ), (∀ n, c n ∉ E) →
        frontier (cluster (μ ω) R z t) ∩ frontier A ⊆ ⋃ n, sphere (c n) (r n) →
        cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqg_spheres_null_except_countable_centers hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω ⟨E, hE, hnull⟩ hcompare
  refine ⟨E, hE, ?_⟩
  intro A z t R ht hR hz hcl hA hmass c r hc hcover
  apply hcompare A z t R ht hR hz hcl hA hmass
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro n
  exact hnull (c n) (hc n) (r n)

end HarmonicBalls
