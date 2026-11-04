import HarmonicBalls.Proofs.Sec9.CircleCoverUniqueness

/-! # Weak uniqueness for frontiers covered by lines

Distinct nonhorizontal affine lines meet in at most one point. Thus an
atomless locally finite planar measure has only countably many directions
in this family for which any line has positive mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- The affine line `re = m * im + b`. -/
def affineRealLine (m b : ℝ) : Set ℂ := {z | z.re = m * z.im + b}

/-- Two distinct lines in this parametrization intersect in at most one point. -/
theorem finite_inter_affineRealLine_of_ne (a b : ℝ × ℝ) (hab : a ≠ b) :
    (affineRealLine a.1 a.2 ∩ affineRealLine b.1 b.2).Finite := by
  classical
  by_cases hne : (affineRealLine a.1 a.2 ∩ affineRealLine b.1 b.2).Nonempty
  · obtain ⟨x, hx⟩ := hne
    apply (finite_singleton x).subset
    intro y hy
    have hx1 : x.re = a.1 * x.im + a.2 := hx.1
    have hx2 : x.re = b.1 * x.im + b.2 := hx.2
    have hy1 : y.re = a.1 * y.im + a.2 := hy.1
    have hy2 : y.re = b.1 * y.im + b.2 := hy.2
    have hm : a.1 ≠ b.1 := by
      intro hm
      have hb : a.2 = b.2 := by rw [hm] at hx1; linarith
      exact hab (Prod.ext hm hb)
    have hzero : (a.1 - b.1) * (y.im - x.im) = 0 := by nlinarith
    have him : y.im = x.im := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
      (sub_ne_zero.mpr hm))
    simp only [mem_singleton_iff]
    apply Complex.ext
    · rw [him] at hy1
      linarith
    · exact him
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact finite_empty

/-- Only countably many lines in this family have positive mass. -/
theorem countable_affineRealLine_pos_measure (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    [NullSingletonClass μ] :
    {a : ℝ × ℝ | 0 < μ (affineRealLine a.1 a.2)}.Countable := by
  apply Measure.countable_meas_pos_of_disjoint_iUnion₀
  · intro a
    apply IsClosed.nullMeasurableSet
    exact isClosed_eq Complex.continuous_re
      ((continuous_const.mul Complex.continuous_im).add continuous_const)
  · intro a b hab
    exact (finite_inter_affineRealLine_of_ne a b hab).countable.measure_zero μ

/-- Outside a countable set of slopes, every line with that slope is null. -/
theorem exists_countable_slopes_affineRealLine_null (μ : Measure ℂ)
    [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∃ E : Set ℝ, E.Countable ∧ ∀ m ∉ E, ∀ b : ℝ, μ (affineRealLine m b) = 0 := by
  let S : Set (ℝ × ℝ) := {a | 0 < μ (affineRealLine a.1 a.2)}
  refine ⟨Prod.fst '' S, (countable_affineRealLine_pos_measure μ).image Prod.fst, ?_⟩
  intro m hm b
  apply le_antisymm _ zero_le
  apply le_of_not_gt
  intro hpos
  exact hm ⟨(m, b), hpos, rfl⟩

universe u

/-- I2 gives one countable exceptional set of slopes such that every line
with a nonexceptional slope is LQG-null, simultaneously in its intercept. -/
theorem ae_lqg_affineRealLine_null_except_countable_slopes
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∃ E : Set ℝ, E.Countable ∧
      ∀ m ∉ E, ∀ b : ℝ, μ ω (affineRealLine m b) = 0 := by
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
  exact exists_countable_slopes_affineRealLine_null (μ ω)

/-- Weak-uniqueness inclusions hold when the common frontier has a countable
cover by lines with slopes outside one countable exceptional set. -/
theorem ae_subharmonicBall_sandwich_of_affineRealLine_cover
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∃ E : Set ℝ, E.Countable ∧
      ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
        z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
        ∀ (m b : ℕ → ℝ), (∀ n, m n ∉ E) →
        frontier (cluster (μ ω) R z t) ∩ frontier A ⊆
          ⋃ n, affineRealLine (m n) (b n) →
        cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqg_affineRealLine_null_except_countable_slopes hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω ⟨E, hE, hnull⟩ hcompare
  refine ⟨E, hE, ?_⟩
  intro A z t R ht hR hz hcl hA hmass m b hm hcover
  apply hcompare A z t R ht hR hz hcl hA hmass
  apply measure_mono_null hcover
  apply measure_iUnion_null
  intro n
  exact hnull (m n) (hm n) (b n)

end HarmonicBalls
