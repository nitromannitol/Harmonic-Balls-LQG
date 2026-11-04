import HarmonicBalls.Proofs.Sec5.ContactLocalExclusion
import HarmonicBalls.Proofs.Sec5.ClusterLeftContinuity

/-! # Boundary-contact continuity and vanishing increments

Harnack barriers exclude new interior limit points at every time when the
masses of some dyadic increments tend to zero. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal

universe u

/-- Vanishing increment mass and good annuli exclude new interior limit points
except possibly the origin, simultaneously for all centres and positive times. -/
theorem ae_future_closure_inter_ball_subset_closure_union_origin_of_vanishing_increment
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) →
      (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
        closure (cluster (μ ω) 1 z t) ∪ {0} := by
  obtain ⟨c, hc, h61⟩ := h61
  obtain ⟨α, hα, h61⟩ := h61 γ hγ hγ2
  obtain ⟨E, hE, hcount⟩ := h61 α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  let v : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
  have hv : 0 < v := by
    dsimp [v]
    exact lt_min (by positivity) (mul_pos hγ (sub_pos.mpr hα₀))
  let βplus : ℝ := v / 2
  have hβplus : 0 < βplus := by dsimp [βplus]; positivity
  have hβplus' : βplus < v := by dsimp [βplus]; linarith
  let β : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hβ : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β := by dsimp [β]; linarith
  have hvol0 := (hvolume γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ βplus β
    hβplus hβplus' hβ).1
  have hvol : PolyHighProb P (fun s => {ω | ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal (s ^ β) ≤ μ ω (ball x s)}) := by
    apply hvol0.mono
    intro s ω hω x hx
    exact (hω x hx).1
  have hdyadic := ((hvol.comp_mul (c := (1 : ℝ) / 8) (by norm_num)).inter hcount).ae_eventually_dyadic
  filter_upwards [hdyadic] with ω hgood
  have hgood' : ∀ᶠ n : ℕ in atTop,
      (∀ x ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal ((dyadicScale n / 8) ^ β) ≤ μ ω (ball x (dyadicScale n / 8))) ∧
      (∀ w ∈ prevalenceGrid (dyadicScale n),
        ∃ ρ ∈ Icc (dyadicScale n) (Real.sqrt (dyadicScale n)), ω ∈ E ρ w) := by
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1
    have hs : 0 < ((2 : ℝ)⁻¹) ^ n := by positivity
    have hs1 : ((2 : ℝ)⁻¹) ^ n < 1 := by
      have hp := pow_le_pow_of_le_one (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
        (show (2 : ℝ)⁻¹ ≤ 1 by norm_num) hn1
      norm_num at hp ⊢
      linarith
    refine ⟨?_, ?_⟩
    · simpa only [dyadicScale, mem_ofPred_eq, one_div, div_eq_mul_inv, one_mul, mul_comm] using hn.1
    · simpa only [dyadicScale] using exists_good_scale_of_prevalence_count hc hs hs1 hn.2
  intro t ht z hz hmass
  classical
  let m : ℕ → ℕ := fun n => Classical.choose (hmass (dyadicScale n) (dyadicScale_pos n))
  have hm : ∀ n, μ ω (cluster (μ ω) 1 z (t + dyadicScale (m n)) \ cluster (μ ω) 1 z t) ≤
      ENNReal.ofReal (dyadicScale n) := fun n => Classical.choose_spec (hmass _ (dyadicScale_pos n))
  have hsub := iInter_future_closure_inter_ball_subset_closure_union_origin
    (μ ω) (cluster (μ ω) 1 z t) (fun n => cluster (μ ω) 1 z (t + dyadicScale (m n)))
    α β hα (fun ρ w => ω ∈ E ρ w) hgood' hm (by
    intro n w ρ hρ hEρ hdomain hsmall
    apply hE ω ρ hρ w hEρ z hz (t + dyadicScale (m n))
      (add_pos ht (dyadicScale_pos (m n))) _ hsmall
    intro y hy
    refine ⟨(hdomain hy).1, ?_⟩
    intro hyz
    have hyz' : y = z := by simpa using hyz
    exact (hdomain hy).2 (hyz'.symm ▸ self_mem_cluster (μ := μ ω) (t := t) hz))
  intro x hx
  apply hsub
  exact ⟨Set.mem_iInter.mpr (fun n => Set.mem_iInter.mp hx.1 (m n)), hx.2⟩

/-- Connectedness removes the origin exception from the interior exclusion. -/
theorem ae_future_closure_inter_ball_subset_closure_of_vanishing_increment
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) →
      (⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ ball 0 1 ⊆
        closure (cluster (μ ω) 1 z t) := by
  filter_upwards [h32 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_union_origin_of_vanishing_increment
      hvolume h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hconnected hmono hsub
  intro t ht z hz hsmall
  apply iInter_inter_ball_subset_closure_of_subset_union_origin (cluster (μ ω) 1 z t)
    (fun n => closure (cluster (μ ω) 1 z (t + dyadicScale n))) z (self_mem_cluster hz)
  · exact fun _ => isClosed_closure
  · intro i j hij
    apply closure_mono
    have hscale : dyadicScale j ≤ dyadicScale i := by
      dsimp [dyadicScale]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
    exact hmono _ _ 1 (add_pos ht (dyadicScale_pos j)) (by linarith)
      zero_lt_one z hz
  · intro n
    exact (hconnected (t + dyadicScale n) 1 (add_pos ht (dyadicScale_pos n))
      zero_lt_one z hz).2.1.isPreconnected.closure
  · intro n x hx
    exact subset_closure (hmono t (t + dyadicScale n) 1 ht
      (le_add_of_nonneg_right (dyadicScale_pos n).le) zero_lt_one z hz hx)
  · exact hsub t ht z hz hsmall

/-- If increments have vanishing mass, right continuity follows once the future
closures acquire no new points on the unit circle. -/
theorem ae_cluster_right_continuity_of_vanishing_increment_and_sphere_inclusion
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) →
      ((⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n))) ∩ sphere 0 1 ⊆
        closure (cluster (μ ω) 1 z t)) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_future_closure_inter_ball_subset_closure_of_vanishing_increment
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ]
    with ω hmono hinterior
  intro t ht z hz hsmall hsphere
  apply (cluster_closure_dyadic_iInter_subset_iff_right_continuous ht
    (fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz)).1
  intro x hx
  have hx' : x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)) := by
    simpa only [dyadicScale] using hx
  by_cases hxball : x ∈ ball (0 : ℂ) 1
  · exact hinterior t ht z hz hsmall ⟨hx', hxball⟩
  · have hxclosed : x ∈ closedBall (0 : ℂ) 1 :=
      closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
        (Set.mem_iInter.mp hx' 0)
    have hxdist : dist x 0 = 1 := by
      have hle := mem_closedBall.mp hxclosed
      have hge : 1 ≤ dist x 0 := le_of_not_gt (by simpa only [mem_ball] using hxball)
      exact le_antisymm hle hge
    exact hsphere ⟨hx', mem_sphere.mpr hxdist⟩


/-- Vanishing changes in total mass imply vanishing mass of increments for
an increasing family of open sets with finite initial mass. -/
theorem vanishing_increment_of_vanishing_mass_change
    (μ : Measure ℂ) (A : Set ℂ) (B : ℕ → Set ℂ)
    (hA : IsOpen A) (hfin : μ A ≠ ⊤) (hsub : ∀ n, A ⊆ B n)
    (hmass : ∀ ε : ℝ, 0 < ε → ∃ n, μ (B n) ≤ μ A + ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ n, μ (B n \ A) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := hmass ε hε
  exact ⟨n, measure_sdiff_le_of_measure_le_add (hsub n) hA.measurableSet.nullMeasurableSet hfin hn⟩

/-- Once the closure contains the whole unit circle, vanishing increment
mass gives Hausdorff continuity even if the cluster has lost mass. -/
theorem ae_cluster_hausdorff_continuity_of_vanishing_increment_and_sphere_subset
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) →
      sphere (0 : ℂ) 1 ⊆ closure (cluster (μ ω) 1 z t) →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
        hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_cluster_right_continuity_of_vanishing_increment_and_sphere_inclusion
      hvolume h32 h33 h61 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hmono hright
  intro t ht z hz hsmall hsphere
  apply cluster_hausdorffContinuousWithinAt_of_right_continuity ht
    (fun s s' hs hss => hmono s s' 1 hs hss zero_lt_one z hz)
  apply hright t ht z hz hsmall
  exact fun _ hx => hsphere hx.2

end HarmonicBalls
