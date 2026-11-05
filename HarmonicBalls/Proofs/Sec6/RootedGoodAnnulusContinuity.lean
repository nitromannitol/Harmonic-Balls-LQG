import HarmonicBalls.Proofs.Sec6.NearbyGoodAnnulusContinuity
import HarmonicBalls.Proofs.Sec9.CircleCoverUniqueness

/-! # Stability of good-annulus counts at mass-typical centres -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- For an atomless locally finite planar measure, every circle centred at a
mass-typical point is null, simultaneously over all radii. -/
theorem ae_spheres_null_of_atomless (μ : Measure ℂ)
    [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ z ∂μ, ∀ r : ℝ, μ (sphere z r) = 0 := by
  obtain ⟨E, hE, hnull⟩ := exists_countable_centers_spheres_null μ
  have hEμ : μ E = 0 := hE.measure_zero μ
  have hae : ∀ᵐ z ∂μ, z ∉ E := by
    rw [ae_iff]
    simpa only [not_not, ofPred_mem_eq] using hEμ
  filter_upwards [hae] with z hz
  exact hnull z hz

/-- At mass-typical centres, good-annulus counts in all finite radius windows
are locally preserved after strict threshold relaxation. Annular positivity is
assumed only at radii that are counted at the reference centre. -/
theorem ae_exists_nearby_goodAnnuli_count_lower_bound
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ z ∂μ, ∀ (S : Set ℝ), S.Finite →
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, IsGoodAnnulus μ r z a b →
        0 < r ∧ 0 < μ (annulus z (3*r) (5*r))) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
        {r ∈ S | IsGoodAnnulus μ r z a b}.ncard ≤
          {r ∈ S | IsGoodAnnulus μ r w a' b'}.ncard := by
  filter_upwards [ae_spheres_null_of_atomless μ] with z hz
  intro S hS a a' b b' ha' ha hb hbb hreg
  apply exists_nearby_goodAnnuli_count_lower_bound μ z hS ha' ha hb hbb
  intro r hr hg
  obtain ⟨hrpos, hpos⟩ := hreg r hr hg
  have hfin : μ (annulus z (3*r) (5*r)) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  exact ⟨hrpos, hz _, hz _, hpos, hfin⟩

universe u

/-- The all-scales volume-growth input gives the count-stability property at
LQG-mass-typical centres, simultaneously for finite windows and thresholds. -/
theorem ae_lqg_ae_nearby_goodAnnuli_count_lower_bound
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ (S : Set ℝ), S.Finite →
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, IsGoodAnnulus (μ ω) r z a b →
        0 < r ∧ 0 < μ ω (annulus z (3*r) (5*r))) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, dist w z < δ →
        {r ∈ S | IsGoodAnnulus (μ ω) r z a b}.ncard ≤
          {r ∈ S | IsGoodAnnulus (μ ω) r w a' b'}.ncard := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hV
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  let : NullSingletonClass (μ ω) := ⟨fun x => by
    have hR : 0 < ‖x‖ + 1 := by positivity
    have hx : x ∈ ball (0 : ℂ) (‖x‖ + 1) := by
      simp only [mem_ball, dist_zero_right]
      linarith
    exact (hV.2 _ hR).measure_singleton hx⟩
  exact ae_exists_nearby_goodAnnuli_count_lower_bound (μ ω)

end HarmonicBalls.Section6
