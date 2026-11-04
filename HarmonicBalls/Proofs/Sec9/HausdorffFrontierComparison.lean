import HarmonicBalls.Proofs.Sec9.CountableFrontierComparison
import Mathlib.MeasureTheory.Measure.Hausdorff
import HarmonicBalls.Steps.Sec4.Basic

/-! # Hausdorff measure and volume growth -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- The upper volume-growth bound controls the restriction of the measure to
its domain by Hausdorff measure of the same exponent. -/
theorem VolumeGrowth.restrict_le_smul_hausdorffMeasure
    {μ : Measure ℂ} {R βm βp : ℝ} (hV : VolumeGrowth μ R βm βp) :
    μ.restrict (ball (0 : ℂ) R) ≤
      ENNReal.ofReal (2 ^ βp) • Measure.hausdorffMeasure βp := by
  obtain ⟨hβm, hβ, r₀, hr₀, hbound⟩ := hV
  let c : ℝ≥0∞ := ENNReal.ofReal (2 ^ βp)
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hle : c⁻¹ • μ.restrict (ball (0 : ℂ) R) ≤ Measure.hausdorffMeasure βp := by
    apply Measure.le_hausdorffMeasure βp _ (ENNReal.ofReal (r₀ / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_ball]
    have hfin : ediam s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hs
    have hdiam : diam s ≤ r₀ / 4 := by
      rw [Metric.diam, ← ENNReal.toReal_ofReal (show 0 ≤ r₀ / 4 by positivity)]
      exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hs
    by_cases hne : (s ∩ ball (0 : ℂ) R).Nonempty
    · obtain ⟨x, hx, hxR⟩ := hne
      by_cases hz : ediam s = 0
      · have hsub : s ∩ ball (0 : ℂ) R ⊆ {x} := by
          intro y hy
          simp only [mem_singleton_iff]
          exact (Metric.ediam_eq_zero_iff.mp hz) hy.1 hx
        have hμ : μ (s ∩ ball (0 : ℂ) R) = 0 :=
          measure_mono_null hsub (VolumeGrowth.measure_singleton ⟨hβm, hβ, r₀, hr₀, hbound⟩ hxR)
        simp [hμ]
      · have hdpos : 0 < diam s := by
          rw [Metric.diam]
          exact ENNReal.toReal_pos hz hfin
        have hsmall : 2 * diam s < r₀ := by linarith
        have hsubset : s ∩ ball (0 : ℂ) R ⊆ ball x (2 * diam s) := by
          intro y hy
          rw [mem_ball]
          have := Metric.dist_le_diam_of_mem' hfin hy.1 hx
          linarith
        have hball := (hbound (2 * diam s) (by positivity) hsmall x hxR).2
        calc
          c⁻¹ * μ (s ∩ ball (0 : ℂ) R) ≤ c⁻¹ * ENNReal.ofReal ((2 * diam s) ^ βp) :=
            by gcongr; exact (measure_mono hsubset).trans hball
          _ = ediam s ^ βp := by
            rw [Real.mul_rpow (by norm_num) (diam_nonneg), ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
            change c⁻¹ * (c * ENNReal.ofReal (diam s ^ βp)) = _
            rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
            rw [← ENNReal.ofReal_rpow_of_nonneg diam_nonneg hβ.le, Metric.diam, ENNReal.ofReal_toReal hfin]
    · have : s ∩ ball (0 : ℂ) R = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [this]
  have := smul_le_smul_left c hle
  simpa [smul_smul, ENNReal.mul_inv_cancel hc0 hct, c] using this

/-- A Hausdorff-null subset of the volume-growth domain is null for the
volume-growth measure. -/
theorem VolumeGrowth.measure_zero_of_hausdorffMeasure_eq_zero
    {μ : Measure ℂ} {R βm βp : ℝ} (hV : VolumeGrowth μ R βm βp)
    {s : Set ℂ} (hs : s ⊆ ball 0 R)
    (hz : Measure.hausdorffMeasure βp s = 0) : μ s = 0 := by
  have hle := (Measure.le_iff'.mp hV.restrict_le_smul_hausdorffMeasure) s
  rw [Measure.restrict_apply' measurableSet_ball, inter_eq_self_of_subset_left hs,
    Measure.smul_apply, hz, smul_zero] at hle
  exact le_antisymm hle zero_le

/-- Countable covers by sets of finite lower-dimensional Hausdorff measure
are null for a volume-growth measure. -/
theorem VolumeGrowth.measure_zero_of_countable_hausdorff_cover
    {μ : Measure ℂ} {R βm βp d : ℝ} (hV : VolumeGrowth μ R βm βp)
    {s : Set ℂ} (hs : s ⊆ ball 0 R) (hd : d < βp)
    (t : ℕ → Set ℂ) (hst : s ⊆ ⋃ n, t n)
    (hfinite : ∀ n, Measure.hausdorffMeasure d (t n) ≠ ∞) : μ s = 0 := by
  apply hV.measure_zero_of_hausdorffMeasure_eq_zero hs
  apply measure_mono_null hst
  apply measure_iUnion_null
  intro n
  exact (Measure.hausdorffMeasure_zero_or_top hd (t n)).resolve_right (hfinite n)

/-- A set in the volume-growth domain with finite lower-dimensional
Hausdorff measure is null for the volume-growth measure. -/
theorem VolumeGrowth.measure_zero_of_hausdorffMeasure_lt_top
    {μ : Measure ℂ} {R βm βp d : ℝ} (hV : VolumeGrowth μ R βm βp)
    {s : Set ℂ} (hs : s ⊆ ball 0 R) (hd : d < βp)
    (hfinite : Measure.hausdorffMeasure d s ≠ ∞) : μ s = 0 := by
  have hz : Measure.hausdorffMeasure βp s = 0 :=
    (Measure.hausdorffMeasure_zero_or_top hd s).resolve_right hfinite
  have hle := (Measure.le_iff'.mp hV.restrict_le_smul_hausdorffMeasure) s
  rw [Measure.restrict_apply' measurableSet_ball, inter_eq_self_of_subset_left hs,
    Measure.smul_apply, hz, smul_zero] at hle
  exact le_antisymm hle zero_le

universe u

/-- On the volume-growth event, weak uniqueness holds whenever the common
frontier has finite Hausdorff measure in a dimension below the volume-growth
exponent. The exponent is deterministic and the condition is simultaneous
for all comparison balls. -/
theorem ae_subharmonicBall_sandwich_of_finite_hausdorff_common_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ β > 0, ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R d : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      d < β → Measure.hausdorffMeasure d
        (frontier (cluster (μ ω) R z t) ∩ frontier A) ≠ ∞ →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βp, βm, hβp, hβp', hβm, _⟩ := exists_volumeGrowth_exponents hγ hγ2 hα
  refine ⟨βp, hβp, ?_⟩
  filter_upwards [ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hI2 hγ hγ2 hα
      hβp hβp' hβm hGFF hμ, ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV hcompare
  intro A z t R d ht hR hz hcl hA hmass hd hfinite
  apply hcompare A z t R ht hR hz hcl hA hmass
  apply (hV.2 R hR).measure_zero_of_hausdorffMeasure_lt_top _ hd hfinite
  exact (inter_subset_right.trans frontier_subset_closure).trans hcl

/-- Weak uniqueness also holds when the common frontier is covered by
countably many sets of finite lower-dimensional Hausdorff measure. -/
theorem ae_subharmonicBall_sandwich_of_countable_hausdorff_cover
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ β > 0, ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R d : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      d < β → ∀ T : ℕ → Set ℂ,
      (frontier (cluster (μ ω) R z t) ∩ frontier A) ⊆ ⋃ n, T n →
      (∀ n, Measure.hausdorffMeasure d (T n) ≠ ∞) →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βp, βm, hβp, hβp', hβm, _⟩ := exists_volumeGrowth_exponents hγ hγ2 hα
  refine ⟨βp, hβp, ?_⟩
  filter_upwards [ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hI2 hγ hγ2 hα
      hβp hβp' hβm hGFF hμ, ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV hcompare
  intro A z t R d ht hR hz hcl hA hmass hd T hcover hfinite
  apply hcompare A z t R ht hR hz hcl hA hmass
  exact (hV.2 R hR).measure_zero_of_countable_hausdorff_cover
    ((inter_subset_right.trans frontier_subset_closure).trans hcl) hd T hcover hfinite

end HarmonicBalls
