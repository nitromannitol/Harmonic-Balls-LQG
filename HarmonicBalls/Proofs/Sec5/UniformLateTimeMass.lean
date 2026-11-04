import HarmonicBalls.Proofs.Sec5.UniformCompactExhaustion
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-! # Uniform late-time control of cluster mass

Compact exhaustion and inner regularity bound the mass outside all sufficiently
late clusters, uniformly for centres in a compact subset of the disc.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The mass outside a cluster becomes uniformly small for centres in a
compact subset of the disc. This also bounds every later cluster increment. -/
theorem uniform_centre_late_time_cluster_mass_of_volumeGrowth
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {K : Set ℂ} (hK : IsCompact K) (hKsub : K ⊆ ball 0 R)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
      μ (ball 0 R \ cluster μ R z t) < ε ∧
      ∀ s : ℝ, μ (cluster μ R z s \ cluster μ R z t) < ε := by
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨L, hLsub, hL, hsmall⟩ := measurableSet_ball.exists_isCompact_sdiff_lt
    (μ := μ) (measure_ball_lt_top.ne) hε.ne'
  obtain ⟨T, hT, hentry⟩ := exists_uniform_compact_entry_time_of_volumeGrowth
    hμ hR hV hK hL hKsub hLsub
  refine ⟨T, hT, ?_⟩
  intro z hz t ht
  have hcontain := hentry z hz t ht
  have hsub : ball (0 : ℂ) R \ cluster μ R z t ⊆ ball 0 R \ L := by
    intro x hx
    exact ⟨hx.1, fun hLx => hx.2 (hcontain hLx)⟩
  have hrest : μ (ball 0 R \ cluster μ R z t) < ε :=
    (measure_mono hsub).trans_lt hsmall
  refine ⟨hrest, ?_⟩
  intro s
  apply (measure_mono ?_).trans_lt hrest
  intro x hx
  exact ⟨cluster_subset_ball hx.1, hx.2⟩

universe u

/-- Almost surely, the late-time mass bound holds simultaneously for all
radii, compact sets of centres, and positive tolerances. -/
theorem ae_uniform_centre_late_time_cluster_mass
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 R →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ z ∈ K, ∀ t : ℝ, T ≤ t →
        μ ω (ball 0 R \ cluster (μ ω) R z t) < ε ∧
        ∀ s : ℝ, μ ω (cluster (μ ω) R z s \ cluster (μ ω) R z t) < ε := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV] with ω hω
  intro R hR K hK hKsub ε hε
  exact uniform_centre_late_time_cluster_mass_of_volumeGrowth hω.1 hR (hω.2 R hR)
    hK hKsub hε

end HarmonicBalls
