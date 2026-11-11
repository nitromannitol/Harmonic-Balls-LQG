import HarmonicBalls.Proofs.Sec5.RightDiscontinuityMeasurability

/-! # Almost-everywhere time continuity -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- For almost every deterministic time, a random volume-growth measure has
an almost surely right-continuous cluster at a fixed centre. -/
theorem ae_time_ae_cluster_right_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) 1 βminus βplus) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, 0 < t →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  classical
  let ν := hμ.mk μ
  obtain ⟨A, hA, hAeq⟩ := exists_measurableSet_right_discontinuity_joint_time_of_volumeGrowth hz
  let E : Set (Ω × ℝ) := {p | 0 < p.2 ∧ (ν p.1, p.2) ∈ A}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const measurable_snd).inter
    (hA.preimage ((hμ.measurable_mk.comp measurable_fst).prodMk measurable_snd))
  have hνgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βminus βplus, VolumeGrowth (ν ω) 1 βminus βplus := by
    filter_upwards [hgood, hμ.ae_eq_mk] with ω hg he
    simpa only [ν, ← he] using hg
  have hcount : ∀ᵐ ω ∂P, {t : ℝ | (ω, t) ∈ E}.Countable := by
    filter_upwards [hνgood] with ω hω
    obtain ⟨hloc, βminus, βplus, hv⟩ := hω
    have hm : ∀ s s', 0 < s → s ≤ s' → cluster (ν ω) 1 z s ⊆ cluster (ν ω) 1 z s' := by
      intro s s' hs hss'
      exact cluster_subset_of_general obstacleMonotoneGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc zero_lt_one hv hz hs hss'
    apply (countable_not_rightContinuous_of_monotone hm (fun _ _ => cluster_subset_ball)).mono
    intro t ht
    exact ⟨ht.1, (hAeq (ν ω) hloc ⟨βminus, βplus, hv⟩ t ht.1).mp ht.2⟩
  have hae : ∀ᵐ ω ∂P, ∀ᵐ t : ℝ ∂volume, (ω, t) ∉ E := by
    filter_upwards [hcount] with ω hc
    exact hc.ae_notMem volume
  have hswap : ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, (ω, t) ∉ E :=
    (Measure.ae_ae_comm hE.compl).mp hae
  filter_upwards [hswap] with t ht
  filter_upwards [ht, hνgood, hμ.ae_eq_mk] with ω hn hg he htpos
  by_contra hf
  have hνfail : ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (cluster (ν ω) 1 z s) ⊆
        cluster (ν ω) 1 z t + ball (0 : ℂ) ε := by
    simpa only [ν, ← he] using hf
  exact hn ⟨htpos, (hAeq (ν ω) hg.1 hg.2 t htpos).mpr hνfail⟩

universe u

/-- The LQG cluster is almost surely right-continuous at almost every
deterministic time; I2 provides the required volume growth. -/
theorem ae_time_ae_lqg_cluster_right_continuous
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, 0 < t →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨βm, βp, hvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) 1 βminus βplus := by
    filter_upwards [hvol] with ω hω
    exact ⟨hω.1, βm, βp, hω.2 1 zero_lt_one⟩
  exact ae_time_ae_cluster_right_continuous P μ (hGFF.aemeasurable_lqgMeasure hμ) hz hgood

/-- One full-measure set of deterministic times works simultaneously for
any prescribed countable family of centres. -/
theorem ae_time_ae_lqg_cluster_right_continuous_for_countable_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {C : Set ℂ} (hcount : C.Countable) (hCsub : C ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ t : ℝ ∂volume, ∀ᵐ ω ∂P, ∀ z ∈ C, 0 < t →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  have : Countable C := hcount.to_subtype
  have ht : ∀ᵐ t : ℝ ∂volume, ∀ z : C, ∀ᵐ ω ∂P, 0 < t →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
    apply ae_all_iff.mpr
    intro z
    exact ae_time_ae_lqg_cluster_right_continuous hI2 hγ hγ2 hα hGFF hμ (hCsub z.property)
  filter_upwards [ht] with t ht'
  have hw := ae_all_iff.mpr ht'
  filter_upwards [hw] with ω hω z hz
  exact hω ⟨z, hz⟩


end HarmonicBalls
