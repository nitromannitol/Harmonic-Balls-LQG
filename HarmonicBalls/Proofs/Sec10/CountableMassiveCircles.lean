import HarmonicBalls.Proofs.Sec9.CountableFrontierComparison
import Mathlib.Geometry.Euclidean.Basic

/-! # Circles of positive mass

Distinct circles in the plane meet in at most two points. Consequently an
atomless locally finite measure assigns positive mass to at most countably
many circles, simultaneously over their centers and radii.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- The intersection of two distinct planar circles is finite. -/
theorem finite_inter_spheres_of_ne (a b : ℂ × ℝ) (hab : a ≠ b) :
    (sphere a.1 a.2 ∩ sphere b.1 b.2).Finite := by
  classical
  by_cases hn : (sphere a.1 a.2 ∩ sphere b.1 b.2).Nonempty
  · obtain ⟨x, hx⟩ := hn
    have hcent : a.1 ≠ b.1 := by
      intro heq
      apply hab
      apply Prod.ext heq
      have hxa := mem_sphere.mp hx.1
      have hxb := mem_sphere.mp hx.2
      rw [heq] at hxa
      exact hxa.symm.trans hxb
    by_cases hy : ∃ y ∈ sphere a.1 a.2 ∩ sphere b.1 b.2, y ≠ x
    · obtain ⟨y, hy, hyx⟩ := hy
      apply ((finite_singleton y).insert x).subset
      intro p hp
      simp only [mem_insert_iff, mem_singleton_iff]
      exact EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
        Complex.finrank_real_complex hcent hyx.symm (mem_sphere.mp hx.1)
        (mem_sphere.mp hy.1) (mem_sphere.mp hp.1) (mem_sphere.mp hx.2)
        (mem_sphere.mp hy.2) (mem_sphere.mp hp.2)
    · apply (finite_singleton x).subset
      intro p hp
      simp only [mem_singleton_iff]
      by_contra hpx
      exact hy ⟨p, hp, hpx⟩
  · rw [not_nonempty_iff_eq_empty.mp hn]
    exact finite_empty

/-- An atomless locally finite planar measure has only countably many circles
of positive mass. -/
theorem countable_spheres_pos_measure (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    [NullSingletonClass μ] :
    {a : ℂ × ℝ | 0 < μ (sphere a.1 a.2)}.Countable := by
  apply Measure.countable_meas_pos_of_disjoint_iUnion₀
  · intro a
    exact isClosed_sphere.measurableSet.nullMeasurableSet
  · intro a b hab
    exact (finite_inter_spheres_of_ne a b hab).countable.measure_zero μ

universe u

/-- I2 gives, almost surely, a countable exceptional family of circles for
the LQG measure, simultaneously over all centers and radii. -/
theorem ae_countable_lqg_spheres_pos_measure_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, {a : ℂ × ℝ | 0 < μ ω (sphere a.1 a.2)}.Countable := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 (‖x‖ + 1) hR).measure_singleton hx⟩
  exact countable_spheres_pos_measure (μ ω)

end HarmonicBalls
