import HarmonicBalls.Proofs.Sec9.HausdorffFrontierComparison
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-! # Hausdorff-size criteria in the full volume-growth exponent range -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

universe u

/-- I2 implies that sets with a countable cover by finite Hausdorff-measure
sets are null whenever the dimension is below the admissible upper-growth
threshold. The event is simultaneous in the domain, set and dimension. -/
theorem ae_lqgMeasure_zero_of_countable_hausdorff_cover
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (R : ℝ) (s : Set ℂ) (d : ℝ), 0 < R → s ⊆ ball 0 R →
      d < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) → ∀ T : ℕ → Set ℂ,
      s ⊆ ⋃ n, T n → (∀ n, Measure.hausdorffMeasure d (T n) ≠ ∞) → μ ω s = 0 := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hthreshold : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    apply lt_min
    · have : 0 < 2 - γ := by linarith
      positivity
    · exact mul_pos hγ (sub_pos.mpr hα)
  filter_upwards [hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hV
  intro R s d hR hs hd T hcover hfinite
  have hmax : max d 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) :=
    max_lt hd hthreshold
  obtain ⟨βp, hβp0, hβp'⟩ := exists_between hmax
  let βm := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hβm : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < βm := lt_add_one _
  have hβm0 : 0 < βm := ((mul_pos hγ (sub_pos.mpr hα)).trans_le (le_max_right _ _)).trans hβm
  have hβp : 0 < βp := (le_max_right d 0).trans_lt hβp0
  obtain ⟨r₀, hr₀, hbound⟩ := hV R hR βp βm hβp hβp' hβm
  have hv : VolumeGrowth (μ ω) R βm βp := ⟨hβm0, hβp, r₀, hr₀, hbound⟩
  exact hv.measure_zero_of_countable_hausdorff_cover hs ((le_max_left d 0).trans_lt hβp0)
    T hcover hfinite

/-- Under I2, the weak-uniqueness inclusions hold when the common frontier is
covered by countably many finite Hausdorff-measure sets in any dimension below
the volume-growth threshold; this holds simultaneously in all parameters. -/
theorem ae_subharmonicBall_sandwich_of_hausdorff_cover_below_growth_threshold
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R d : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      d < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) → ∀ T : ℕ → Set ℂ,
      (frontier (cluster (μ ω) R z t) ∩ frontier A) ⊆ ⋃ n, T n →
      (∀ n, Measure.hausdorffMeasure d (T n) ≠ ∞) →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqgMeasure_zero_of_countable_hausdorff_cover hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hzero hcompare
  intro A z t R d ht hR hz hcl hA hmass hd T hcover hfinite
  apply hcompare A z t R ht hR hz hcl hA hmass
  exact hzero R _ d hR ((inter_subset_right.trans frontier_subset_closure).trans hcl)
    hd T hcover hfinite

/-- Any bounded set of positive Liouville mass has Hausdorff dimension at
least the upper volume-growth threshold. -/
theorem ae_lqgMeasure_positive_mass_dimH_lower_bound
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (R : ℝ) (s : Set ℂ), 0 < R → s ⊆ ball 0 R → μ ω s ≠ 0 →
      ENNReal.ofReal (min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))) ≤ dimH s := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hthreshold : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    apply lt_min
    · have : 0 < 2 - γ := by linarith
      positivity
    · exact mul_pos hγ (sub_pos.mpr hα)
  filter_upwards [ae_lqgMeasure_zero_of_countable_hausdorff_cover hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hzero
  intro R s hR hs hnon
  apply le_of_not_gt
  intro hlt
  obtain ⟨d, hsd, hdlim⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
  have hd : (d : ℝ) < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    apply (ENNReal.ofReal_lt_ofReal_iff hthreshold).mp
    simpa using hdlim
  have hnull : Measure.hausdorffMeasure (d : ℝ) s = 0 := hausdorffMeasure_of_dimH_lt hsd
  apply hnon
  exact hzero R s d hR hs hd (fun _ => s)
    (fun x hx => mem_iUnion.mpr ⟨0, hx⟩) (fun _ => by simp [hnull])

/-- A failure of the regularized-cluster inclusion forces the common
frontier to have at least the upper volume-growth threshold as Hausdorff
dimension. -/
theorem ae_subharmonicBall_comparison_failure_dimH_lower_bound
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      ¬ A ⊆ regularizedCluster (μ ω) R z t →
      ENNReal.ofReal (min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))) ≤
        dimH (frontier (cluster (μ ω) R z t) ∩ frontier A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqgMeasure_positive_mass_dimH_lower_bound hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hdim hcompare
  intro A z t R ht hR hz hcl hA hmass hfail
  apply hdim R _ hR ((inter_subset_right.trans frontier_subset_closure).trans hcl)
  intro hnull
  exact hfail (hcompare A z t R ht hR hz hcl hA hmass hnull).2.1

/-- A Lipschitz image of a compact real interval has finite one-dimensional
Hausdorff measure. -/
theorem hausdorffMeasure_one_image_unit_interval_lt_top
    {K : ℝ≥0} {f : ℝ → ℂ} (hf : LipschitzWith K f) :
    Measure.hausdorffMeasure 1 (f '' Icc (0 : ℝ) 1) ≠ ∞ := by
  have h := hf.hausdorffMeasure_image_le (d := 1) (by norm_num) (Icc (0 : ℝ) 1)
  apply ne_of_lt
  calc
    Measure.hausdorffMeasure 1 (f '' Icc (0 : ℝ) 1) ≤
        (K : ℝ≥0∞) ^ (1 : ℝ) * Measure.hausdorffMeasure 1 (Icc (0 : ℝ) 1) := h
    _ < ∞ := by simp [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]

/-- If the volume-growth threshold exceeds one, weak uniqueness holds when
the common frontier is covered by countably many Lipschitz curves. -/
theorem ae_subharmonicBall_sandwich_of_lipschitz_curve_cover
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    1 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
      z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
      IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
      ∀ (f : ℕ → ℝ → ℂ) (K : ℕ → ℝ≥0), (∀ n, LipschitzWith (K n) (f n)) →
      (frontier (cluster (μ ω) R z t) ∩ frontier A) ⊆
        ⋃ n, f n '' Icc (0 : ℝ) 1 →
      cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
      (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα hthreshold Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_hausdorff_cover_below_growth_threshold hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcompare
  intro A z t R ht hR hz hcl hA hmass f K hlip hcover
  exact hcompare A z t R 1 ht hR hz hcl hA hmass hthreshold
    (fun n => f n '' Icc (0 : ℝ) 1) hcover
    (fun n => hausdorffMeasure_one_image_unit_interval_lt_top (hlip n))

end HarmonicBalls
